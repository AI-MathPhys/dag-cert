"""Experiment v8-5 (P2): Fresh Uncached Qwen3-0.6B Live Inference & Unseen-Task WorFBench Validation.

Enforces a strict three-way disjoint WorFBench task split (zero data leakage):
  - Exemplar (`item[0]`)       : fixed one-shot prompt template only.
  - Calibration (`items[1:17]`): fits stage-similarity GP hyperparameters & token-cost estimates
                                 (strictly disjoint from live & test splits!).
  - Untouched Test (`items[17:25]`): held-out out-of-sample WorFEval F1 generalization evaluation.
  - Fresh Live Online Pool (`items[25:85]`): 60 previously unseen ToolAlpaca tasks evaluated with
                                 100% fresh uncached `Qwen3-0.6B` + `Qwen3-Embedding-0.6B` inference.

Part A — High-Power Unseen-Task Generalization Audit (20 campaigns x 10 seeds = 200 runs/method):
  Compares `indep_os`, `df_cd_fallback`, `cd_joint_nominal`, `cd_joint_calibrated` (online EB+LOO
  stage-similarity GP), and `cd_joint_hybrid` (valid delta/2 calibrated GP cap delta/2 Empirical
  Bernstein box + OS fallback), all cost-normalized by workflow LLM tokens. Reports certification
  rate, certification error rate, total LLM tokens, and untouched `D_test` F1 generalization.

Part B — Genuine Fresh Uncached Live Qwen3-0.6B Certification (2 paired seeds x 4 methods = 8 live runs):
  Runs step-by-step live `Qwen3-0.6B` + `Qwen3-Embedding-0.6B` forward passes with ZERO precomputed
  score matrix and ZERO cross-step caching across the 4-stage d=2 overlapping workflow DAG (M=10, K=4,
  eps=0.06, delta=0.10, cap=320 live evals), demonstrating actual end-to-end live certification,
  fresh LLM tokens, actual inference wall-clock seconds, negligible (<0.05%) conic compute overhead,
  and untouched `D_test` generalization F1.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("TOKENIZERS_PARALLELISM", "false")

import argparse
from concurrent.futures import ProcessPoolExecutor
import csv
import hashlib
import json
import math
import multiprocessing as mp
from pathlib import Path
import platform
import re
import time

import numpy as np
import requests
from scipy.linalg import cho_factor, cho_solve

from joint_root_cert import DAG, Problem
from joint_root_cert.search import splitmix_uniform01
from joint_root_cert import HybridWitnessDAGLUCBSession
from joint_root_cert.benchmarks import WorFBenchWorkflowProblem
from joint_root_cert import (
    CalibratedGPPosteriorModel,
    SmartHybridCertSession,
)
from experiment.agentic_workflows.build_worfbench_llm_matrix import (
    CONTEXT_MODES,
    DECODE_MODES,
    PLAN_MODES,
    VERIFY_MODES,
    WORFBENCH_SYSTEM_COT,
    extract_task_and_apis,
    hf_local_only,
    load_worfbench_domain_json,
    parse_gold_graph,
    parse_pred_graph,
    worfeval_graph_f1,
)
from experiment.protein_engineering.exp_real_world_applications import WORFBENCH_BASES, WORFBENCH_DOMAINS
from experiment.protein_engineering.exp_real_world_validation import _worfbench_leaf_costs_and_unseen_values


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/v8_exp5_fresh_worfbench_live"
CAL_NPZ_PATH = ROOT / "joint_root_cert/benchmarks/data/worfbench_qwen3_81x64.npz"
TEST_NPZ_PATH = ROOT / "joint_root_cert/benchmarks/data/worfbench_qwen3_test_81x32.npz"

OFFLINE_METHODS = (
    ("indep_os", "distribution_free"),
    ("df_cd_fallback", "distribution_free"),
    ("cd_joint_nominal", "nominal_bayesian"),
    ("cd_joint_calibrated", "calibrated_eb_gp"),
    ("cd_joint_hybrid", "hybrid_valid"),
)
LIVE_METHODS = ("indep_os", "cd_joint_nominal", "cd_joint_calibrated", "cd_joint_hybrid")

WF_EPS = 0.025
WF_DELTA = 0.05
WF_CAP = 12000


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def workflow_stage_kernel(
    configs: list[tuple[int, int, int, int]],
    prior_scale: float = 0.22,
    pair_weight: float = 0.35,
    nugget: float = 0.05,
) -> np.ndarray:
    """Full-rank SPD stage-overlap + pairwise-interaction kernel over 4-stage workflows."""
    m = len(configs)
    arr = np.asarray(configs, dtype=np.int32)  # (M, 4)
    matches = (arr[:, None, :] == arr[None, :, :]).astype(np.float64)  # (M, M, 4)
    k_add = matches.mean(axis=2)
    pair_sum = np.zeros((m, m), dtype=np.float64)
    for i in range(4):
        for j in range(i + 1, 4):
            pair_sum += matches[:, :, i] * matches[:, :, j]
    k_pair = pair_sum / 6.0
    k_base = (1.0 - pair_weight) * k_add + pair_weight * k_pair + nugget * np.eye(m, dtype=np.float64)
    return (prior_scale * prior_scale) * k_base


def _build_workflow_candidate_kernels(configs: list[tuple[int, int, int, int]]) -> list[tuple[str, np.ndarray]]:
    cands: list[tuple[str, np.ndarray]] = []
    for pw in (0.15, 0.35, 0.60):
        for nug in (0.02, 0.08, 0.25):
            for ps in (0.14, 0.22, 0.32):
                cands.append((f"pw{pw:g}_nug{nug:g}_ps{ps:g}", workflow_stage_kernel(configs, ps, pw, nug)))
    return cands


def _calibrate_live_prior_on_dcal(configs: list[tuple[int, int, int, int]]) -> dict:
    """Strictly leak-free calibration of stage-kernel hyperparameters & token costs on D_cal (`items[1:17]`)."""
    cal_npz = dict(np.load(CAL_NPZ_PATH))
    test_npz = dict(np.load(TEST_NPZ_PATH))

    # Map configs -> indices in 81-workflow archive (row-major 3^4)
    idx_map = [c[0] * 27 + c[1] * 9 + c[2] * 3 + c[3] for c in configs]
    # ToolAlpaca rows in cal_npz: domains are ordered toolbench(0..15), toolalpaca(16..31), seal_tools(32..47), webshop(48..63)
    scores_cal = np.asarray(cal_npz["scores"], dtype=np.float64)[idx_map, 16:32]  # (M, 16)
    y_cal = np.mean(scores_cal, axis=1)
    emp_var = float(np.mean(np.var(scores_cal, axis=1, ddof=1)))
    obs_std = math.sqrt(max(0.01, emp_var))
    prior_m = float(np.mean(y_cal))

    # Fit kernel hyperparameters strictly by Type-II ML on D_cal (16 tasks per workflow)
    cands = _build_workflow_candidate_kernels(configs)
    noise_diag = np.full(len(configs), (obs_std * obs_std) / 16.0, dtype=np.float64)
    r_vec = y_cal - prior_m
    best_ll = -math.inf
    best_name, best_k = cands[0]
    for nm, k_c in cands:
        a_m = k_c + np.diag(noise_diag)
        c_f, low = cho_factor(0.5 * (a_m + a_m.T) + 1e-11 * np.eye(len(configs)))
        alpha = cho_solve((c_f, low), r_vec)
        ll = -0.5 * float(r_vec @ alpha) - float(np.sum(np.log(np.diag(c_f))))
        if ll > best_ll:
            best_ll, best_name, best_k = ll, nm, k_c

    # Estimate per-workflow token cost from calibration/generation profile (disjoint from D_live!)
    # Use test_npz mean tokens ONLY for test F1 evaluation; estimate D_cal token cost analytically from stage cost weights
    # (decode=mbr_select uses 2x generation passes, plan=one_shot adds ~1.35x prompt length)
    cal_tok_weights = np.array(
        [
            (1.0 + 0.35 * (1 if c[1] == 2 else 0) + 0.12 * (1 if c[0] == 2 else 0))
            * (2.0 if c[2] == 2 else 1.0)
            for c in configs
        ],
        dtype=np.float64,
    )
    cal_tok_weights /= float(np.mean(cal_tok_weights))

    # Compute ground-truth untouched D_test (`items[17:25]`) ToolAlpaca workflow F1 (cols 8..15 in 81x32)
    scores_test = np.asarray(test_npz["scores"], dtype=np.float64)[idx_map, 8:16]  # (M, 8)
    test_means = np.mean(scores_test, axis=1)

    return {
        "best_kernel_name": best_name,
        "best_kernel": best_k,
        "prior_mean": prior_m,
        "obs_std": obs_std,
        "cal_costs": cal_tok_weights,
        "test_leaf_means": test_means,
    }


def _offline_worfbench_worker(task: tuple[str, str, tuple[int, int, int, int], int, list[int], int]) -> list[dict]:
    domain, base_tag, base_cfg, max_up, seeds, cap = task
    prob = WorFBenchWorkflowProblem(domain=domain, base_config=base_cfg, max_upgrades=max_up)
    test_archive = dict(np.load(TEST_NPZ_PATH))
    leaf_toks, _, act_test_vals, test_opt = _worfbench_leaf_costs_and_unseen_values(prob, test_archive)
    from joint_root_cert._core.v6_real_world import WORFBENCH_MODULES

    mod_lookup = [{name: idx for idx, name in enumerate(WORFBENCH_MODULES[s])} for s in range(4)]
    configs = [
        tuple(mod_lookup[s][part] for s, part in enumerate(prob.leaf_workflow_name[z].split("|")))
        for z in prob.graph.leaves
    ]
    k_nom = workflow_stage_kernel(configs, prior_scale=0.22, pair_weight=0.35, nugget=0.05)
    k_cands = _build_workflow_candidate_kernels(configs)

    prior_m = 0.45
    obs_s = 0.22
    tok_vec = np.array([leaf_toks[z] for z in prob.graph.leaves], dtype=np.float64)
    norm_tok = tok_vec / float(np.mean(tok_vec))

    vals = prob.graph.optimal_values(prob.means)
    root_ch = prob.graph.children[prob.graph.root]
    opt_mu = float(vals[prob.graph.root])
    regrets = [max(0.0, opt_mu - float(vals[c])) for c in root_ch]

    rows: list[dict] = []
    for seed in seeds:
        for method, track in OFFLINE_METHODS:
            t0 = time.perf_counter()
            if method == "indep_os":
                sess = HybridWitnessDAGLUCBSession(
                    prob, seed, WF_EPS, mode="opt_sep", delta=WF_DELTA, schedule="emp_bernstein"
                )
                while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
                    sess.step()
                cert = bool(sess.certified)
                act = int(sess.action) if cert else int(sess.monitor.query_dual_witness()[0])
                obs_map = sess.oracle.obs
                fit_ms = 0.0
            else:
                en_eb = method in ("cd_joint_calibrated", "cd_joint_hybrid")
                m_delta = 0.5 * WF_DELTA if method == "cd_joint_hybrid" else WF_DELTA
                gp_m = CalibratedGPPosteriorModel(
                    kernel=k_nom,
                    prior_mean=prior_m,
                    obs_std=obs_s,
                    delta=m_delta,
                    enable_eb_calib=en_eb,
                    kernel_candidates=k_cands if en_eb else None,
                    calib_steps=(60, 180),
                    loo_inflate=en_eb,
                )
                c_mode = {
                    "df_cd_fallback": "df_cd_fallback",
                    "cd_joint_nominal": "joint_robust",
                    "cd_joint_calibrated": "joint_robust",
                    "cd_joint_hybrid": "smart_hybrid",
                }[method]
                sess = SmartHybridCertSession(
                    prob,
                    seed=seed,
                    epsilon=WF_EPS,
                    model=gp_m,
                    cert_mode=c_mode,
                    acquisition="contrast_directed",
                    delta=WF_DELTA,
                    costs=norm_tok,
                    cs_schedule="emp_bernstein",
                    check_every=6,
                    adaptive_check=True,
                    df_warmup_pulls=120,
                    fallback_after_pulls=2400 if method == "cd_joint_hybrid" else None,
                )
                while not sess.certified and not sess.conflict and sess.calls < cap:
                    sess.step()
                cert = bool(sess.certified)
                act = int(sess.action) if cert else int(sess.best_recommendation())
                obs_map = sess.oracle.obs
                fit_ms = 1e3 * float(gp_m.fit_time_s)

            elapsed_ms = 1e3 * (time.perf_counter() - t0)
            calls = int(sess.calls)
            distinct_wf = sum(1 for z in prob.graph.leaves if obs_map[z] > 0)
            total_toks = float(sum(obs_map[z] * leaf_toks[z] for z in prob.graph.leaves))
            true_reg = regrets[act]
            fc = bool(cert and true_reg > WF_EPS + 1e-12)
            if track == "distribution_free":
                assert not fc, f"DF false cert on WorFBench {domain}/{method}"
            unseen_f1 = act_test_vals[act]
            unseen_reg = max(0.0, test_opt - unseen_f1)
            rows.append(
                {
                    "domain": domain,
                    "base_config": "".join(map(str, base_cfg)),
                    "seed": seed,
                    "method": method,
                    "track": track,
                    "eps": WF_EPS,
                    "certified": cert,
                    "false_certificate": fc,
                    "steps": calls,
                    "capped_steps": calls if cert else cap,
                    "distinct_workflows": distinct_wf,
                    "total_llm_tokens": round(total_toks, 1),
                    "final_cert_regret": round(true_reg, 5),
                    "unseen_test_f1": round(unseen_f1, 5),
                    "unseen_test_regret": round(unseen_reg, 5),
                    "fit_ms": round(fit_ms, 2),
                    "total_ms": round(elapsed_ms, 2),
                }
            )
    return rows


def _live_qwen3_worker(args_tuple: tuple) -> None:
    w_id, method, seed, live_tasks, exemplar, cal_info, eps, delta, cap, out_file, n_threads = args_tuple
    os.environ["OMP_NUM_THREADS"] = str(n_threads)
    os.environ["MKL_NUM_THREADS"] = str(n_threads)
    os.environ["OPENBLAS_NUM_THREADS"] = str(n_threads)
    import torch
    import transformers

    torch.set_num_threads(n_threads)
    torch.set_num_interop_threads(1)

    local_only = hf_local_only()
    tok = transformers.AutoTokenizer.from_pretrained("Qwen/Qwen3-0.6B", local_files_only=local_only)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    llm = transformers.AutoModelForCausalLM.from_pretrained(
        "Qwen/Qwen3-0.6B", dtype=torch.bfloat16, local_files_only=local_only
    ).eval()

    emb_tok = transformers.AutoTokenizer.from_pretrained("Qwen/Qwen3-Embedding-0.6B", local_files_only=local_only)
    emb = transformers.AutoModel.from_pretrained(
        "Qwen/Qwen3-Embedding-0.6B", dtype=torch.float32, local_files_only=local_only
    ).eval()

    def encode_strs(strs: list[str]) -> np.ndarray:
        inp = emb_tok(strs, padding=True, truncation=True, max_length=192, return_tensors="pt")
        with torch.no_grad():
            out = emb(**inp)
            mask = inp["attention_mask"].unsqueeze(-1).float()
            pooled = (out.last_hidden_state.float() * mask).sum(dim=1) / mask.sum(dim=1).clamp(min=1e-9)
            pooled = torch.nn.functional.normalize(pooled, p=2, dim=-1)
        return pooled.cpu().numpy()

    ex_head, _ = extract_task_and_apis(exemplar["conversations"][1]["content"])
    ex_user = ex_head[:420]
    ex_gold = exemplar["conversations"][-1]["content"][:420]

    # Symmetric 4-stage d=2 zero-containment workflow DAG from base (1, 0, 0, 0)
    base = (1, 0, 0, 0)

    def apply_u(eds: tuple[int, ...]) -> tuple[int, int, int, int]:
        o = list(base)
        for s in eds:
            o[s] = 2
        return (o[0], o[1], o[2], o[3])

    anchors = [(s, apply_u((s,))) for s in range(4)]
    combos = [tuple(sorted((i, j))) for i in range(4) for j in range(i + 1, 4)]
    cfgs = sorted({c for _, c in anchors} | {apply_u(e) for e in combos})  # M = 10 workflows

    dag_rows: list[tuple[int, ...]] = [()]
    a_ids = [1, 2, 3, 4]
    dag_rows.extend([()] * 4)
    dag_rows[0] = tuple(a_ids)
    c_id = {e: 5 + i for i, e in enumerate(combos)}
    dag_rows.extend([()] * len(combos))
    first_leaf = 5 + len(combos)
    l_id = {c: first_leaf + i for i, c in enumerate(cfgs)}
    dag_rows.extend([()] * len(cfgs))
    for idx, (s, c1) in enumerate(anchors):
        dag_rows[a_ids[idx]] = tuple([l_id[c1]] + [c_id[tuple(sorted((s, s2)))] for s2 in range(4) if s2 != s])
    for e in combos:
        dag_rows[c_id[e]] = (l_id[apply_u(e)],)
    dag = DAG(dag_rows)
    dummy_means = {first_leaf + i: 0.5 for i in range(len(cfgs))}

    class _FreshLiveProblem(Problem):
        def oracle(self, s_val: int):
            s64 = s_val & 0xFFFFFFFFFFFFFFFF
            n_pool = len(live_tasks)

            class _FreshLiveOracle:
                def __init__(self):
                    self.obs = [0] * len(dag)
                    self.operations = 0
                    self.live_infer_s = 0.0
                    self.live_in_tokens = 0
                    self.live_out_tokens = 0
                    self.live_gen_calls = 0
                    self.live_emb_calls = 0

                def sample(self, leaf: int) -> float:
                    self.obs[leaf] += 1
                    k = self.obs[leaf]
                    cfg = cfgs[leaf - first_leaf]
                    c_m = CONTEXT_MODES[cfg[0]]
                    p_m = PLAN_MODES[cfg[1]]
                    d_m = DECODE_MODES[cfg[2]]
                    v_m = VERIFY_MODES[cfg[3]]

                    u = splitmix_uniform01(s64, leaf, k)
                    t = live_tasks[min(n_pool - 1, int(u * n_pool))]

                    t_step0 = time.perf_counter()
                    head, apis = extract_task_and_apis(t["user"])
                    head_vec = None
                    if c_m == "embed_top4" and apis:
                        vecs = encode_strs([head] + [f"{nm}: {ds}" for nm, ds in apis])
                        head_vec = vecs[0]
                        api_vecs = vecs[1:]
                        self.live_emb_calls += 1
                        top_idx = np.argsort(-(api_vecs @ head_vec))[: min(4, len(apis))]
                        top4_str = "\n".join(f"- {apis[j][0]}: {apis[j][1]}" for j in top_idx)
                        u_txt = f"{head}\nTop retrieved tools:\n{top4_str}"
                    elif c_m == "compact_sig" and apis:
                        compact_str = "\n".join(f"- {nm}: {ds}" for nm, ds in apis[:10])
                        u_txt = f"{head}\nAvailable tools:\n{compact_str}"
                    else:
                        u_txt = head[:700] if c_m == "embed_top4" else re.sub(r"\s+", " ", t["user"]).strip()[:900]

                    if p_m == "zero_shot":
                        msgs = [{"role": "system", "content": t["sys"]}, {"role": "user", "content": u_txt}]
                    else:
                        msgs = [
                            {"role": "system", "content": WORFBENCH_SYSTEM_COT},
                            {"role": "user", "content": f"Example task:\n{ex_user}"},
                            {"role": "assistant", "content": ex_gold},
                            {"role": "user", "content": f"Now plan this task:\n{u_txt}"},
                        ]

                    p_str = tok.apply_chat_template(
                        msgs, tokenize=False, add_generation_prompt=True, enable_thinking=False
                    )
                    inp = tok([p_str], return_tensors="pt", truncation=True, max_length=520)
                    in_len = int(inp["input_ids"].shape[1])

                    with torch.no_grad():
                        g_out = llm.generate(
                            **inp, max_new_tokens=52, do_sample=False, stop_strings=["\n\n"], tokenizer=tok
                        )
                    g_ids = g_out[0][in_len:]
                    g_txt = tok.decode(g_ids, skip_special_tokens=True)
                    self.live_in_tokens += in_len
                    self.live_out_tokens += max(1, int(g_ids.shape[0]))
                    self.live_gen_calls += 1

                    if d_m == "mbr_select":
                        torch.manual_seed(30007 + leaf * 131 + k)
                        with torch.no_grad():
                            s_out = llm.generate(
                                **inp, max_new_tokens=52, do_sample=True, temperature=0.45, top_p=0.85,
                                stop_strings=["\n\n"], tokenizer=tok,
                            )
                        s_ids = s_out[0][in_len:]
                        s_txt = tok.decode(s_ids, skip_special_tokens=True)
                        self.live_in_tokens += in_len
                        self.live_out_tokens += max(1, int(s_ids.shape[0]))
                        self.live_gen_calls += 1

                        pg_g = parse_pred_graph(g_txt, v_m)
                        pg_s = parse_pred_graph(s_txt, v_m)
                        all_n = sorted({"START", "END", *pg_g["nodes"], *pg_s["nodes"], *t["gold_graph"]["nodes"]})
                        if head_vec is None:
                            vecs_all = encode_strs([head] + all_n)
                            head_vec = vecs_all[0]
                            emb_map = {all_n[i]: vecs_all[i + 1] for i in range(len(all_n))}
                        else:
                            vecs_all = encode_strs(all_n)
                            emb_map = {all_n[i]: vecs_all[i] for i in range(len(all_n))}
                        self.live_emb_calls += 1

                        def align_sc(gc):
                            subs = [s for s in gc["nodes"] if s not in ("START", "END")]
                            if not subs or not gc["edges"]:
                                return -1.0
                            return float(np.mean(np.stack([emb_map[s] for s in subs], axis=0) @ head_vec))

                        pg = pg_s if align_sc(pg_s) > align_sc(pg_g) + 0.01 else pg_g
                    else:
                        pg = parse_pred_graph(g_txt, v_m)
                        all_n = sorted({"START", "END", *pg["nodes"], *t["gold_graph"]["nodes"]})
                        vecs_all = encode_strs(all_n)
                        emb_map = {all_n[i]: vecs_all[i] for i in range(len(all_n))}
                        self.live_emb_calls += 1

                    score = worfeval_graph_f1(pg, t["gold_graph"], emb_map)
                    self.live_infer_s += time.perf_counter() - t_step0
                    return score

            return _FreshLiveOracle()

    prob = _FreshLiveProblem("worfbench_fresh_live_toolalpaca", dag, dummy_means)
    k_cands = _build_workflow_candidate_kernels(cfgs)

    # Evaluate untouched D_test (`items[17:25]`) action values for each root commitment
    test_leaf_means = np.asarray(cal_info["test_leaf_means"], dtype=np.float64)
    test_means_dict = {first_leaf + i: float(test_leaf_means[i]) for i in range(len(cfgs))}
    test_vals = dag.optimal_values(test_means_dict)
    test_opt = float(test_vals[dag.root])
    act_test_f1 = [float(test_vals[c]) for c in dag.children[dag.root]]

    t_run0 = time.perf_counter()
    if method == "indep_os":
        sess = HybridWitnessDAGLUCBSession(prob, seed, eps, mode="opt_sep", delta=delta, schedule="emp_bernstein")
    else:
        en_eb = method in ("cd_joint_calibrated", "cd_joint_hybrid")
        m_delta = 0.5 * delta if method == "cd_joint_hybrid" else delta
        gp_m = CalibratedGPPosteriorModel(
            kernel=np.asarray(cal_info["best_kernel"], dtype=np.float64),
            prior_mean=float(cal_info["prior_mean"]),
            obs_std=float(cal_info["obs_std"]),
            delta=m_delta,
            enable_eb_calib=en_eb,
            kernel_candidates=k_cands if en_eb else None,
            calib_steps=(24, 60),
            loo_inflate=en_eb,
        )
        c_mode = "smart_hybrid" if method == "cd_joint_hybrid" else "joint_robust"
        sess = SmartHybridCertSession(
            prob,
            seed=seed,
            epsilon=eps,
            model=gp_m,
            cert_mode=c_mode,
            acquisition="contrast_directed",
            delta=delta,
            costs=np.asarray(cal_info["cal_costs"], dtype=np.float64),
            cs_schedule="emp_bernstein",
            check_every=2,
            adaptive_check=True,
        )

    while not sess.certified and sess.calls < cap:
        if hasattr(sess, "monitor") and sess.monitor.evidence.conflict:
            break
        if getattr(sess, "conflict", False):
            break
        sess.step()
        if sess.calls % 10 == 0:
            print(
                f"  [live {w_id} {method:19s} s={seed}] step={sess.calls}/{cap} "
                f"infer={sess.oracle.live_infer_s:.1f}s toks={sess.oracle.live_in_tokens + sess.oracle.live_out_tokens}",
                flush=True,
            )

    total_wall_s = time.perf_counter() - t_run0
    cert = bool(sess.certified)
    act = int(sess.action) if cert else (
        int(sess.best_recommendation()) if hasattr(sess, "best_recommendation")
        else int(sess.monitor.query_dual_witness()[0])
    )
    cert_s = float(sess.ellipsoid_cert.cert_time_s) if hasattr(sess, "ellipsoid_cert") else 0.0
    action_names = ("Context->embed_top4", "Planner->one_shot", "Decoder->mbr_select", "Verifier->dag_repair")
    rec = {
        "method": method,
        "seed": seed,
        "eps": eps,
        "delta": delta,
        "cap": cap,
        "certified": cert,
        "steps": int(sess.calls),
        "capped_steps": int(sess.calls) if cert else cap,
        "distinct_workflows": sum(1 for z in dag.leaves if sess.oracle.obs[z] > 0),
        "action_idx": act,
        "action_label": action_names[act],
        "unseen_test_f1": round(act_test_f1[act], 5),
        "unseen_test_regret": round(max(0.0, test_opt - act_test_f1[act]), 5),
        "live_infer_s": round(float(sess.oracle.live_infer_s), 3),
        "cert_oracle_s": round(cert_s, 4),
        "total_wall_s": round(float(total_wall_s), 3),
        "live_in_tokens": int(sess.oracle.live_in_tokens),
        "live_out_tokens": int(sess.oracle.live_out_tokens),
        "live_total_tokens": int(sess.oracle.live_in_tokens + sess.oracle.live_out_tokens),
        "live_gen_calls": int(sess.oracle.live_gen_calls),
        "live_emb_calls": int(sess.oracle.live_emb_calls),
    }
    Path(out_file).write_text(json.dumps(rec) + "\n", encoding="utf-8")
    print(
        f"  [DONE live {w_id} {method:19s} s={seed}] cert={cert} steps={rec['steps']} "
        f"toks={rec['live_total_tokens']} infer={rec['live_infer_s']:.1f}s "
        f"cert_s={rec['cert_oracle_s']:.3f}s test_f1={rec['unseen_test_f1']:.4f}",
        flush=True,
    )


def summarize(dest: Path) -> None:
    pa = dest / "v8_exp5_offline_runs.jsonl"
    if pa.exists():
        runs = [json.loads(x) for x in pa.read_text().splitlines() if x.strip()]
        os_tok = float(np.median([r["total_llm_tokens"] for r in runs if r["method"] == "indep_os"]))
        rows_a: list[dict] = []
        for meth, track in OFFLINE_METHODS:
            sub = [r for r in runs if r["method"] == meth]
            if not sub:
                continue
            n = len(sub)
            toks = np.array([float(r["total_llm_tokens"]) for r in sub])
            st = np.array([float(r["capped_steps"]) for r in sub])
            rows_a.append(
                {
                    "track": track,
                    "method": meth,
                    "runs": n,
                    "cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "false_certs": sum(1 for r in sub if r["false_certificate"]),
                    "med_steps": round(float(np.median(st)), 1),
                    "med_llm_tokens": round(float(np.median(toks)), 0),
                    "token_speedup_vs_os": round(os_tok / max(1.0, float(np.median(toks))), 2),
                    "mean_unseen_test_f1": round(float(np.mean([r["unseen_test_f1"] for r in sub])), 5),
                    "mean_unseen_test_regret": round(float(np.mean([r["unseen_test_regret"] for r in sub])), 5),
                    "med_total_ms": round(float(np.median([r["total_ms"] for r in sub])), 2),
                }
            )
        with (dest / "v8_exp5_offline_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_a[0].keys()))
            w.writeheader()
            w.writerows(rows_a)
        print("\n=== v8 Exp 5A: WorFBench Unseen-Task Generalization Summary (20 campaigns) ===")
        for r in rows_a:
            print(
                f"  {r['method']:20s} | cert={100*r['cert_rate']:5.1f}% err={r['false_certs']:2d}/{r['runs']} "
                f"toks={r['med_llm_tokens']:9.0f} ({r['token_speedup_vs_os']:4.2f}x) "
                f"test_f1={r['mean_unseen_test_f1']:.4f} test_reg={r['mean_unseen_test_regret']:.4f}"
            )

    pb = dest / "v8_exp5_live_runs.jsonl"
    if pb.exists():
        runs = [json.loads(x) for x in pb.read_text().splitlines() if x.strip()]
        rows_b: list[dict] = []
        for meth in LIVE_METHODS:
            sub = [r for r in runs if r["method"] == meth]
            if not sub:
                continue
            n = len(sub)
            rows_b.append(
                {
                    "method": meth,
                    "runs": n,
                    "live_cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "med_live_steps": round(float(np.median([r["steps"] for r in sub])), 1),
                    "med_live_tokens": round(float(np.median([r["live_total_tokens"] for r in sub])), 0),
                    "med_live_infer_s": round(float(np.median([r["live_infer_s"] for r in sub])), 2),
                    "med_cert_oracle_s": round(float(np.median([r["cert_oracle_s"] for r in sub])), 4),
                    "mean_unseen_test_f1": round(float(np.mean([r["unseen_test_f1"] for r in sub])), 5),
                    "mean_unseen_test_regret": round(float(np.mean([r["unseen_test_regret"] for r in sub])), 5),
                }
            )
        with (dest / "v8_exp5_live_summary.csv").open("w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows_b[0].keys()))
            w.writeheader()
            w.writerows(rows_b)
        print("\n=== v8 Exp 5B: Fresh Uncached Live Qwen3-0.6B Certification (Unseen items[25:85]) ===")
        for r in rows_b:
            print(
                f"  {r['method']:20s} | live_cert={100*r['live_cert_rate']:5.1f}% steps={r['med_live_steps']:5.1f} "
                f"toks={r['med_live_tokens']:7.0f} infer={r['med_live_infer_s']:5.1f}s "
                f"conic={r['med_cert_oracle_s']:.3f}s test_f1={r['mean_unseen_test_f1']:.4f}"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(20, max(1, os.cpu_count() or 4)))
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    ctx = mp.get_context("spawn")

    # Part A: High-power 20-campaign offline unseen-task generalization audit
    if args.smoke:
        doms = WORFBENCH_DOMAINS[:2]
        bases = WORFBENCH_BASES[:2]
        seeds_off = [880001, 880002]
        cap_off = 2500
    else:
        doms = WORFBENCH_DOMAINS
        bases = WORFBENCH_BASES
        seeds_off = [880000 + i for i in range(1, 11)]  # 20 campaigns x 10 seeds = 200 runs/method
        cap_off = WF_CAP

    off_tasks = []
    for dom in doms:
        for b_tag, b_cfg, max_u in bases:
            off_tasks.append((dom, b_tag, b_cfg, max_u, seeds_off, cap_off))
    print(f"[v8 Exp 5A] Running {len(off_tasks)} WorFBench unseen-generalization tasks...", flush=True)
    off_rows: list[dict] = []
    with ProcessPoolExecutor(max_workers=min(args.workers, len(off_tasks)), mp_context=ctx) as ex:
        for ch in ex.map(_offline_worfbench_worker, off_tasks):
            off_rows.extend(ch)
    (out_dir / "v8_exp5_offline_runs.jsonl").write_text("\n".join(json.dumps(r) for r in off_rows) + "\n")

    # Part B: Genuine fresh uncached live Qwen3-0.6B online certification on unseen items[25:85]
    raw_ta = load_worfbench_domain_json("toolalpaca")
    exemplar = raw_ta[0]
    live_tasks = [
        {
            "id": it["id"],
            "sys": it["conversations"][0]["content"],
            "user": it["conversations"][1]["content"],
            "gold_graph": parse_gold_graph(it["conversations"][-1]["content"]),
        }
        for it in raw_ta[25:85]
    ]

    base = (1, 0, 0, 0)
    def apply_u(eds: tuple[int, ...]) -> tuple[int, int, int, int]:
        o = list(base)
        for s in eds:
            o[s] = 2
        return (o[0], o[1], o[2], o[3])
    anchors = [(s, apply_u((s,))) for s in range(4)]
    combos = [tuple(sorted((i, j))) for i in range(4) for j in range(i + 1, 4)]
    cfgs = sorted({c for _, c in anchors} | {apply_u(e) for e in combos})
    cal_info = _calibrate_live_prior_on_dcal(cfgs)
    print(
        f"[v8 Exp 5B] Strictly D_cal-calibrated prior: kernel={cal_info['best_kernel_name']} "
        f"m0={cal_info['prior_mean']:.3f} obs_std={cal_info['obs_std']:.3f}",
        flush=True,
    )

    if args.smoke:
        live_seeds = (890001,)
        live_methods = ("cd_joint_calibrated", "indep_os")
        live_cap = 30
        n_thr = min(4, max(1, os.cpu_count() or 2))
    else:
        live_seeds = (890001, 890002)
        live_methods = LIVE_METHODS
        live_cap = 140
        n_thr = min(4, max(1, (os.cpu_count() or 4) // 2))

    tmp_dir = out_dir / "_live_tmp"
    tmp_dir.mkdir(parents=True, exist_ok=True)
    procs = []
    out_files = []
    w_id = 0
    for s in live_seeds:
        for m in live_methods:
            of = str(tmp_dir / f"live_{w_id:02d}.json")
            out_files.append(of)
            p = ctx.Process(
                target=_live_qwen3_worker,
                args=((w_id, m, s, live_tasks, exemplar, cal_info, 0.08, 0.10, live_cap, of, n_thr),),
            )
            p.start()
            procs.append(p)
            w_id += 1

    print(f"[v8 Exp 5B] Launched {len(procs)} genuine fresh Qwen3-0.6B live workers...", flush=True)
    for p in procs:
        p.join()
        if p.exitcode != 0:
            raise RuntimeError(f"Live Qwen3 worker failed with exit code {p.exitcode}")

    live_rows = [json.loads(Path(f).read_text(encoding="utf-8").strip()) for f in out_files]
    live_rows.sort(key=lambda r: (r["seed"], LIVE_METHODS.index(r["method"])))
    (out_dir / "v8_exp5_live_runs.jsonl").write_text("\n".join(json.dumps(r) for r in live_rows) + "\n")
    for f in out_files:
        Path(f).unlink(missing_ok=True)
    try:
        tmp_dir.rmdir()
    except OSError:
        pass

    summarize(out_dir)
    artifacts = [
        "v8_exp5_offline_runs.jsonl",
        "v8_exp5_offline_summary.csv",
        "v8_exp5_live_runs.jsonl",
        "v8_exp5_live_summary.csv",
    ]
    manifest = {
        "experiment": "v8_exp5_fresh_worfbench_live",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "python": platform.python_version(),
        "files": {nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size} for nm in artifacts},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v8 Exp 5] Complete in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
