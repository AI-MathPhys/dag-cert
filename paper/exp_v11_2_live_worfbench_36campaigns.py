"""Experiment v11-2 (P1): 36-Campaign Multi-Domain Fresh Uncached Live Qwen3-0.6B Replication.

Expands the n=8 single-domain ToolAlpaca live cohort (v10-3) into a 36-campaign,
4-domain, multi-base, disjoint-pool genuine live uncached Qwen3-0.6B + Qwen3-Embedding-0.6B
evaluation across ALL FOUR WorFBench domains (`toolbench`, `toolalpaca`, `seal_tools`, `webshop`):

  - 4 domains x 3 distinct 4-stage workflow base configurations (`1000`, `0000`, `0100`)
    x 3 strictly disjoint live task-pool splits (`split_0`, `split_1`, `split_2`)
    = 36 independent paired live campaigns!
  - Strict 3-way disjoint splits per domain (zero data leakage):
      * Exemplar (`items[0]`)       : fixed one-shot prompt template only.
      * Calibration (`items[1:17]`) : Type-II ML stage-kernel & obs_std calibration (`D_cal`).
      * Untouched Test (`items[17:25]`): held-out out-of-sample WorFEval F1 evaluation (`D_test`).
      * Disjoint Live Pools (`items[25:]`): partitioned into 3 non-overlapping live task pools
        per domain (`split_0`, `split_1`, `split_2`), sampled i.i.d. uniformly with replacement
        step-by-step with ZERO precomputed score matrix and ZERO cross-step caching.
  - Predeclared live evaluation cap `cap = 60` (`eps = 0.08`, `delta = 0.10`).
  - Explicitly separates formal distribution-free certificates from model-based certificates:
      1. `indep_os`           [formal_df]: OS acquisition + DF Empirical Bernstein stopping.
      2. `eb_acq_df_stop`     [formal_df]: EB+LOO contrast-directed acquisition + DF Empirical
         Bernstein stopping ONLY (isolates acquisition vs. stopping-rule tightness live!).
      3. `cd_joint_calibrated`[model_based_eb]: EB+LOO contrast-directed acquisition +
         empirically calibrated EB+LOO joint ellipsoid stopping (NOT formally distribution-free).
      4. `cd_joint_eb_or_df`  [model_based_eb_fallback]: EB+LOO (delta/2) OR DF Empirical
         Bernstein (delta/2) stopping (empirically calibrated with DF fallback).
  - Exact coupled-stream execution: `cd_joint_calibrated`, `cd_joint_eb_or_df`, and
    `eb_acq_df_stop` share the exact same live EB+LOO observation trajectory up to `cap = 60`
    (recording exact cumulative tokens, wall time, calls, and action at each stopping rule's
    firing time), paired against an independent live `indep_os` trajectory on the same split/seed.
  - Reports per-domain, per-base, and overall (n=36) completion rates, censored medians/IQRs,
    paired bootstrap 95% CIs (10,000 resamples; no uncensored ratios against censored caps),
    exact Clopper-Pearson 95% CIs, live tokens, live CPU inference time, conic overhead, and
    untouched D_test F1 & regret.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("TOKENIZERS_PARALLELISM", "false")

import argparse
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
from scipy.stats import beta as beta_dist

from dag_mcts.graph import DAG, Problem
from dag_mcts.v3_extensions import splitmix_uniform01
from dag_mcts.v5_hybrid_and_os import DualWitnessCovers, HybridWitnessDAGLUCBSession
from dag_mcts.v7_bayesian_ucd import SupportStructure
from dag_mcts.v8_unified_experiments import (
    CalibratedGPPosteriorModel,
    RobustAwareJointCertifier,
    SmartHybridCertSession,
)
from paper.build_worfbench_llm_matrix import (
    CONTEXT_MODES,
    DECODE_MODES,
    DOMAINS,
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
from paper.exp_v8_5_fresh_worfbench_live import (
    CAL_NPZ_PATH,
    TEST_NPZ_PATH,
    _build_workflow_candidate_kernels,
)


ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "results/bayesian_ucd_v1/v11_exp2_live_worfbench_36campaigns"

DOMAIN_SLICES: dict[str, tuple[int, int, int, int]] = {
    "toolbench": (0, 16, 0, 8),
    "toolalpaca": (16, 32, 8, 16),
    "seal_tools": (32, 48, 16, 24),
    "webshop": (48, 64, 24, 32),
}

BASE_SPECS: tuple[tuple[str, tuple[int, int, int, int]], ...] = (
    ("base_1000", (1, 0, 0, 0)),
    ("base_0000", (0, 0, 0, 0)),
    ("base_0100", (0, 1, 0, 0)),
)

LIVE_METHODS: tuple[tuple[str, str], ...] = (
    ("indep_os", "formal_df"),
    ("eb_acq_df_stop", "formal_df"),
    ("cd_joint_calibrated", "model_based_eb"),
    ("cd_joint_eb_or_df", "model_based_eb_fallback"),
)

LIVE_EPS = 0.08
LIVE_DELTA = 0.10
LIVE_CAP = 60


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _cp_ci_95(k: int, n: int) -> tuple[float, float]:
    if n <= 0:
        return (0.0, 1.0)
    lo = 0.0 if k <= 0 else float(beta_dist.ppf(0.025, k, n - k + 1))
    hi = 1.0 if k >= n else float(beta_dist.ppf(0.975, k + 1, n - k))
    return (lo, hi)


def _paired_bootstrap_ci(
    a_vals: np.ndarray,
    b_vals: np.ndarray,
    stat_fn,
    n_boot: int = 10_000,
    seed: int = 20261120,
) -> tuple[float, float, float]:
    n = len(a_vals)
    pt = float(stat_fn(a_vals, b_vals))
    if n <= 1:
        return (pt, pt, pt)
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, n, size=(n_boot, n))
    samples = np.empty(n_boot, dtype=np.float64)
    for i in range(n_boot):
        ii = idx[i]
        samples[i] = float(stat_fn(a_vals[ii], b_vals[ii]))
    lo, hi = np.percentile(samples, [2.5, 97.5])
    return (pt, float(lo), float(hi))


def _build_base_configs(
    base: tuple[int, int, int, int],
) -> tuple[
    list[tuple[int, int, int, int]],
    list[tuple[int, tuple[int, int, int, int]]],
    list[tuple[int, int]],
]:
    def apply_u(eds: tuple[int, ...]) -> tuple[int, int, int, int]:
        o = list(base)
        for s in eds:
            o[s] = 2
        return (o[0], o[1], o[2], o[3])

    anchors = [(s, apply_u((s,))) for s in range(4)]
    combos = [tuple(sorted((i, j))) for i in range(4) for j in range(i + 1, 4)]
    cfgs = sorted({c for _, c in anchors} | {apply_u(e) for e in combos})
    return cfgs, anchors, combos


def _calibrate_domain_prior_on_dcal(
    domain: str,
    configs: list[tuple[int, int, int, int]],
) -> dict:
    """Strictly leak-free per-domain calibration on D_cal (`items[1:17]`)."""
    cal_npz = dict(np.load(CAL_NPZ_PATH))
    test_npz = dict(np.load(TEST_NPZ_PATH))
    c0, c1, t0, t1 = DOMAIN_SLICES[domain]

    idx_map = [c[0] * 27 + c[1] * 9 + c[2] * 3 + c[3] for c in configs]
    scores_cal = np.asarray(cal_npz["scores"], dtype=np.float64)[idx_map, c0:c1]  # (M, 16)
    y_cal = np.mean(scores_cal, axis=1)
    emp_var = float(np.mean(np.var(scores_cal, axis=1, ddof=1)))
    obs_std = math.sqrt(max(0.01, emp_var))
    prior_m = float(np.mean(y_cal))

    cands = _build_workflow_candidate_kernels(configs)
    noise_diag = np.full(len(configs), (obs_std * obs_std) / float(c1 - c0), dtype=np.float64)
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

    cal_tok_weights = np.array(
        [
            (1.0 + 0.35 * (1 if c[1] == 2 else 0) + 0.12 * (1 if c[0] == 2 else 0))
            * (2.0 if c[2] == 2 else 1.0)
            for c in configs
        ],
        dtype=np.float64,
    )
    cal_tok_weights /= float(np.mean(cal_tok_weights))

    scores_test = np.asarray(test_npz["scores"], dtype=np.float64)[idx_map, t0:t1]  # (M, 8)
    test_means = np.mean(scores_test, axis=1)
    return {
        "best_kernel_name": best_name,
        "best_kernel": best_k,
        "prior_mean": prior_m,
        "obs_std": obs_std,
        "cal_costs": cal_tok_weights,
        "test_leaf_means": test_means,
    }


def _partition_disjoint_pools(items: list[dict], n_splits: int = 3) -> list[list[dict]]:
    """Partition `items[25:]` into `n_splits` strictly disjoint live task pools."""
    tail = items[25:]
    pools: list[list[dict]] = [[] for _ in range(n_splits)]
    for i, it in enumerate(tail):
        pools[i % n_splits].append(
            {
                "id": it["id"],
                "sys": it["conversations"][0]["content"],
                "user": it["conversations"][1]["content"],
                "gold_graph": parse_gold_graph(it["conversations"][-1]["content"]),
            }
        )
    return pools


def _build_workflow_dag(
    base_cfg: tuple[int, int, int, int],
) -> tuple[DAG, list[tuple[int, int, int, int]], int]:
    cfgs, anchors, combos = _build_base_configs(base_cfg)

    def apply_u(eds: tuple[int, ...]) -> tuple[int, int, int, int]:
        o = list(base_cfg)
        for s in eds:
            o[s] = 2
        return (o[0], o[1], o[2], o[3])

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
    return DAG(dag_rows), cfgs, first_leaf


def _live_worker(job: tuple) -> None:
    (
        w_id,
        campaign_id,
        domain,
        base_tag,
        base_cfg,
        split_idx,
        seed,
        stream_kind,  # "indep_os" or "eb_coupled"
        live_tasks,
        exemplar,
        cal_info,
        eps,
        delta,
        cap,
        out_file,
        n_threads,
    ) = job

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

    dag, cfgs, first_leaf = _build_workflow_dag(base_cfg)
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
                    elif c_m == "raw_schema":
                        u_txt = re.sub(r"\s+", " ", t["user"]).strip()[:900]
                    else:
                        u_txt = head[:700] if c_m == "embed_top4" else re.sub(r"\s+", " ", t["user"]).strip()[:900]

                    if p_m == "zero_shot":
                        msgs = [{"role": "system", "content": t["sys"]}, {"role": "user", "content": u_txt}]
                    elif p_m == "step_cot":
                        msgs = [{"role": "system", "content": WORFBENCH_SYSTEM_COT}, {"role": "user", "content": u_txt}]
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
                                **inp,
                                max_new_tokens=52,
                                do_sample=True,
                                temperature=0.45,
                                top_p=0.85,
                                stop_strings=["\n\n"],
                                tokenizer=tok,
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

    prob = _FreshLiveProblem(f"worfbench_live_{domain}_{base_tag}_sp{split_idx}", dag, dummy_means)
    test_leaf_means = np.asarray(cal_info["test_leaf_means"], dtype=np.float64)
    test_means_dict = {first_leaf + i: float(test_leaf_means[i]) for i in range(len(cfgs))}
    test_vals = dag.optimal_values(test_means_dict)
    test_opt = float(test_vals[dag.root])
    act_test_f1 = [float(test_vals[c]) for c in dag.children[dag.root]]
    action_names = ("Context->embed_top4", "Planner->one_shot", "Decoder->mbr_select", "Verifier->dag_repair")

    def _make_rec(
        method_name: str,
        track: str,
        cert: bool,
        steps: int,
        act: int,
        oracle_obj,
        cert_s: float,
        wall_s: float,
        distinct_wf: int,
        switched_df: bool = False,
    ) -> dict:
        return {
            "campaign_id": campaign_id,
            "domain": domain,
            "base_tag": base_tag,
            "base_config": "".join(map(str, base_cfg)),
            "split_idx": split_idx,
            "live_pool_size": len(live_tasks),
            "method": method_name,
            "track": track,
            "seed": seed,
            "eps": eps,
            "delta": delta,
            "cap": cap,
            "certified": bool(cert),
            "steps": int(steps),
            "capped_steps": int(steps) if cert else int(cap),
            "distinct_workflows": int(distinct_wf),
            "action_idx": int(act),
            "action_label": action_names[int(act)],
            "unseen_test_f1": round(act_test_f1[int(act)], 5),
            "unseen_test_regret": round(max(0.0, test_opt - act_test_f1[int(act)]), 5),
            "live_infer_s": round(float(oracle_obj.live_infer_s), 3),
            "cert_oracle_s": round(float(cert_s), 4),
            "total_wall_s": round(float(wall_s), 3),
            "live_in_tokens": int(oracle_obj.live_in_tokens),
            "live_out_tokens": int(oracle_obj.live_out_tokens),
            "live_total_tokens": int(oracle_obj.live_in_tokens + oracle_obj.live_out_tokens),
            "live_gen_calls": int(oracle_obj.live_gen_calls),
            "live_emb_calls": int(oracle_obj.live_emb_calls),
            "switched_to_df": bool(switched_df),
        }

    records: list[dict] = []
    t_run0 = time.perf_counter()

    if stream_kind == "indep_os":
        sess = HybridWitnessDAGLUCBSession(prob, seed, eps, mode="opt_sep", delta=delta, schedule="emp_bernstein")
        while not sess.certified and not sess.monitor.evidence.conflict and sess.calls < cap:
            sess.step()
            if sess.calls % 20 == 0:
                print(
                    f"  [live {w_id:02d} {campaign_id} indep_os] step={sess.calls}/{cap} "
                    f"infer={sess.oracle.live_infer_s:.1f}s",
                    flush=True,
                )
        wall_s = time.perf_counter() - t_run0
        cert = bool(sess.certified)
        act = int(sess.action) if cert else int(sess.monitor.query_dual_witness()[0])
        dwf = sum(1 for z in dag.leaves if sess.oracle.obs[z] > 0)
        rec = _make_rec("indep_os", "formal_df", cert, sess.calls, act, sess.oracle, 0.0, wall_s, dwf, True)
        records.append(rec)
        print(
            f"  [DONE {w_id:02d} {campaign_id} indep_os] cert={cert} steps={rec['steps']} "
            f"toks={rec['live_total_tokens']} infer={rec['live_infer_s']:.1f}s test_reg={rec['unseen_test_regret']:.4f}",
            flush=True,
        )
    else:
        # Exact coupled live EB+LOO trajectory up to `cap`, monitoring:
        #   - `cd_joint_calibrated` [model_based_eb]: EB+LOO stopping at delta
        #   - `cd_joint_eb_or_df`   [model_based_eb_fallback]: EB+LOO (delta/2) OR DF EB (delta/2)
        #   - `eb_acq_df_stop`      [formal_df]: DF Empirical Bernstein stopping ONLY at full delta
        k_cands = _build_workflow_candidate_kernels(cfgs)
        gp_m = CalibratedGPPosteriorModel(
            kernel=np.asarray(cal_info["best_kernel"], dtype=np.float64),
            prior_mean=float(cal_info["prior_mean"]),
            obs_std=float(cal_info["obs_std"]),
            delta=delta,
            enable_eb_calib=True,
            kernel_candidates=k_cands,
            calib_steps=(24, 52),
            loo_inflate=True,
        )
        # Use SmartHybridCertSession in `df_cd_fallback` (with huge warmup so pure EB+LOO
        # contrast-directed acquisition drives the full stream up to `cap`, NEVER stopping early
        # on the GP so all three stopping rules are observed on the 100% identical live stream!).
        # Wait: we drive the exact `SmartHybridCertSession(..., cert_mode="joint_robust")` acquisition
        # step-by-step and maintain parallel monitors!
        sess = SmartHybridCertSession(
            prob,
            seed=seed,
            epsilon=eps,
            model=gp_m,
            cert_mode="joint_robust",
            acquisition="contrast_directed",
            delta=delta,
            costs=np.asarray(cal_info["cal_costs"], dtype=np.float64),
            cs_schedule="emp_bernstein",
            check_every=2,
            adaptive_check=False,
        )
        df_full_mon = DualWitnessCovers(dag, delta=delta, schedule="emp_bernstein", layout="best", track_separation=True)
        df_half_mon = DualWitnessCovers(dag, delta=0.5 * delta, schedule="emp_bernstein", layout="best", track_separation=False)
        half_cert = RobustAwareJointCertifier(
            sess.support_struct, epsilon=eps, solver="colgen_lazy", misspec_xi=0.0, exact_linear_mean=False
        )

        rec_eb: dict | None = None
        rec_hyb: dict | None = None
        rec_df: dict | None = None

        while sess.calls < cap:
            # Force continuation even after EB+LOO certifies so `eb_acq_df_stop` & `cd_joint_eb_or_df`
            # are evaluated on the exact same live trajectory!
            sess.certified = False
            arm_idx = sess._next_arm_idx
            leaf = sess.support_struct.leaves[arm_idx]
            reward = float(sess.oracle.sample(leaf))
            sess.calls += 1
            sess.total_cost += float(sess.support_struct.costs[arm_idx])
            sess.distinct_leaves_evaluated.add(leaf)

            sess.model.observe(arm_idx, reward)
            df_full_mon.step(leaf, reward)
            df_half_mon.step(leaf, reward)

            # Check DF Empirical Bernstein stopping every step (O(log M))
            if rec_df is None:
                a_df, r_df, _, _, _ = df_full_mon.query_dual_witness()
                if r_df <= eps:
                    rec_df = _make_rec(
                        "eb_acq_df_stop",
                        "formal_df",
                        True,
                        sess.calls,
                        a_df,
                        sess.oracle,
                        sess.ellipsoid_cert.cert_time_s,
                        time.perf_counter() - t_run0,
                        len(sess.distinct_leaves_evaluated),
                        True,
                    )

            # Evaluate EB+LOO conic certificate & plan next arm every `check_every = 2` steps
            if sess.calls % 2 == 0 or sess.calls == cap:
                sess._evaluate_certificate_and_plan()
                if rec_eb is None and sess.certified:
                    rec_eb = _make_rec(
                        "cd_joint_calibrated",
                        "model_based_eb",
                        True,
                        sess.calls,
                        int(sess.action),
                        sess.oracle,
                        sess.ellipsoid_cert.cert_time_s,
                        time.perf_counter() - t_run0,
                        len(sess.distinct_leaves_evaluated),
                        False,
                    )
                if sess.certified:
                    # Ensure contrast-directed acquisition continues updating `_next_arm_idx`
                    # after EB+LOO certifies so `eb_acq_df_stop` never stalls on a frozen arm!
                    means_p, psi_p = gp_m.terminal_means_and_psi()
                    stds_p = gp_m.terminal_stds()
                    beta_p = gp_m.beta()
                    sess._next_arm_idx = sess._select_next_arm(
                        means_p, psi_p, stds_p, beta_p, means_p + beta_p * stds_p
                    )

                if rec_hyb is None:
                    # Evaluate EB+LOO at delta/2 OR DF at delta/2
                    a_dh, r_dh, _, _, _ = df_half_mon.query_dual_witness()
                    if r_dh <= eps:
                        rec_hyb = _make_rec(
                            "cd_joint_eb_or_df",
                            "model_based_eb_fallback",
                            True,
                            sess.calls,
                            a_dh,
                            sess.oracle,
                            half_cert.cert_time_s,
                            time.perf_counter() - t_run0,
                            len(sess.distinct_leaves_evaluated),
                            True,
                        )
                    elif not getattr(gp_m, "needs_initial_calibration", False):
                        orig_d = gp_m.delta
                        gp_m.delta = 0.5 * delta
                        try:
                            beta_h = gp_m.beta()
                        finally:
                            gp_m.delta = orig_d
                        means, psi = gp_m.terminal_means_and_psi()
                        best_h_a, best_h_r = 0, math.inf
                        for a_cand in range(sess.support_struct.k):
                            ca = half_cert.certify_action_gp(a_cand, means, psi, beta_h, stop_if_above_eps=True)
                            if ca.regret < best_h_r:
                                best_h_r, best_h_a = ca.regret, a_cand
                            if best_h_r <= eps:
                                break
                        if best_h_r <= eps:
                            rec_hyb = _make_rec(
                                "cd_joint_eb_or_df",
                                "model_based_eb_fallback",
                                True,
                                sess.calls,
                                best_h_a,
                                sess.oracle,
                                half_cert.cert_time_s,
                                time.perf_counter() - t_run0,
                                len(sess.distinct_leaves_evaluated),
                                False,
                            )

                # If all three stopping rules have fired, stop early!
                if rec_eb is not None and rec_hyb is not None and rec_df is not None:
                    break

            if sess.calls % 20 == 0:
                print(
                    f"  [live {w_id:02d} {campaign_id} eb_coupled] step={sess.calls}/{cap} "
                    f"eb={rec_eb is not None} df={rec_df is not None} infer={sess.oracle.live_infer_s:.1f}s",
                    flush=True,
                )

        wall_s = time.perf_counter() - t_run0
        dwf = len(sess.distinct_leaves_evaluated)
        if rec_df is None:
            a_df, _, _, _, _ = df_full_mon.query_dual_witness()
            rec_df = _make_rec(
                "eb_acq_df_stop",
                "formal_df",
                False,
                sess.calls,
                a_df,
                sess.oracle,
                sess.ellipsoid_cert.cert_time_s,
                wall_s,
                dwf,
                True,
            )
        if rec_eb is None:
            rec_eb = _make_rec(
                "cd_joint_calibrated",
                "model_based_eb",
                False,
                sess.calls,
                int(sess.best_recommendation()),
                sess.oracle,
                sess.ellipsoid_cert.cert_time_s,
                wall_s,
                dwf,
                False,
            )
        if rec_hyb is None:
            rec_hyb = _make_rec(
                "cd_joint_eb_or_df",
                "model_based_eb_fallback",
                False,
                sess.calls,
                int(sess.best_recommendation()),
                sess.oracle,
                half_cert.cert_time_s,
                wall_s,
                dwf,
                False,
            )
        records.extend([rec_df, rec_eb, rec_hyb])
        print(
            f"  [DONE {w_id:02d} {campaign_id} eb_coupled] "
            f"eb=({rec_eb['certified']},{rec_eb['steps']}) "
            f"hyb=({rec_hyb['certified']},{rec_hyb['steps']}) "
            f"df=({rec_df['certified']},{rec_df['steps']}) infer={sess.oracle.live_infer_s:.1f}s",
            flush=True,
        )

    tmp_out = Path(f"{out_file}.tmp")
    tmp_out.write_text("\n".join(json.dumps(r) for r in records) + "\n", encoding="utf-8")
    tmp_out.replace(Path(out_file))


def summarize(dest: Path) -> None:
    pb = dest / "v11_exp2_live_runs.jsonl"
    if not pb.exists():
        return
    runs = [json.loads(x) for x in pb.read_text().splitlines() if x.strip()]
    method_order = [m for m, _ in LIVE_METHODS]
    track_map = dict(LIVE_METHODS)

    scopes: list[tuple[str, str]] = [("ALL", "ALL")]
    for dom in DOMAINS:
        scopes.append(("domain", dom))
    for b_tag, _ in BASE_SPECS:
        scopes.append(("base", b_tag))

    rows: list[dict] = []
    for scope_kind, scope_val in scopes:
        if scope_kind == "ALL":
            sc_runs = runs
        elif scope_kind == "domain":
            sc_runs = [r for r in runs if r["domain"] == scope_val]
        else:
            sc_runs = [r for r in runs if r["base_tag"] == scope_val]
        if not sc_runs:
            continue

        os_by_cid = {r["campaign_id"]: r for r in sc_runs if r["method"] == "indep_os"}
        for meth in method_order:
            sub = [r for r in sc_runs if r["method"] == meth]
            if not sub:
                continue
            n = len(sub)
            c_n = sum(1 for r in sub if r["certified"])
            cp_lo, cp_hi = _cp_ci_95(c_n, n)
            steps_arr = np.array([float(r["capped_steps"]) for r in sub])
            toks_arr = np.array([float(r["live_total_tokens"]) for r in sub])
            inf_arr = np.array([float(r["live_infer_s"]) for r in sub])
            conic_arr = np.array([float(r["cert_oracle_s"]) for r in sub])
            f1_arr = np.array([float(r["unseen_test_f1"]) for r in sub])
            reg_arr = np.array([float(r["unseen_test_regret"]) for r in sub])
            unc_reg = [float(r["unseen_test_regret"]) for r in sub if not r["certified"]]

            # Paired bootstrap 95% CIs vs `indep_os` on completion rate diff and token diff
            paired_cids = [r["campaign_id"] for r in sub if r["campaign_id"] in os_by_cid]
            m_by_cid = {r["campaign_id"]: r for r in sub}
            if paired_cids:
                c_m = np.array([1.0 if m_by_cid[c]["certified"] else 0.0 for c in paired_cids])
                c_o = np.array([1.0 if os_by_cid[c]["certified"] else 0.0 for c in paired_cids])
                cdiff_pt, cdiff_lo, cdiff_hi = _paired_bootstrap_ci(
                    c_m, c_o, lambda x, y: float(np.mean(x - y)), seed=11201
                )
                t_m = np.array([float(m_by_cid[c]["live_total_tokens"]) for c in paired_cids])
                t_o = np.array([float(os_by_cid[c]["live_total_tokens"]) for c in paired_cids])
                tdiff_pt, tdiff_lo, tdiff_hi = _paired_bootstrap_ci(
                    t_o, t_m, lambda x, y: float(np.median(x - y)), seed=11202
                )
            else:
                cdiff_pt = cdiff_lo = cdiff_hi = 0.0
                tdiff_pt = tdiff_lo = tdiff_hi = 0.0

            rows.append(
                {
                    "scope_kind": scope_kind,
                    "scope": scope_val,
                    "method": meth,
                    "track": track_map[meth],
                    "campaigns": n,
                    "certified_count": c_n,
                    "cert_rate": round(c_n / n, 4),
                    "cert_cp95_lo": round(cp_lo, 4),
                    "cert_cp95_hi": round(cp_hi, 4),
                    "cert_diff_vs_os": round(cdiff_pt, 4),
                    "cert_diff_ci95_lo": round(cdiff_lo, 4),
                    "cert_diff_ci95_hi": round(cdiff_hi, 4),
                    "med_capped_steps": round(float(np.median(steps_arr)), 1),
                    "q25_capped_steps": round(float(np.percentile(steps_arr, 25)), 1),
                    "q75_capped_steps": round(float(np.percentile(steps_arr, 75)), 1),
                    "med_live_tokens": round(float(np.median(toks_arr)), 0),
                    "q25_live_tokens": round(float(np.percentile(toks_arr, 25)), 0),
                    "q75_live_tokens": round(float(np.percentile(toks_arr, 75)), 0),
                    "med_paired_tok_saved_vs_os": round(tdiff_pt, 0),
                    "tok_saved_ci95_lo": round(tdiff_lo, 0),
                    "tok_saved_ci95_hi": round(tdiff_hi, 0),
                    "med_live_infer_s": round(float(np.median(inf_arr)), 2),
                    "med_cert_oracle_s": round(float(np.median(conic_arr)), 4),
                    "mean_unseen_test_f1": round(float(np.mean(f1_arr)), 5),
                    "mean_unseen_test_regret": round(float(np.mean(reg_arr)), 5),
                    "mean_uncert_test_regret": round(float(np.mean(unc_reg)), 5) if unc_reg else 0.0,
                }
            )

    with (dest / "v11_exp2_live_summary.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print("\n=== v11 Exp 2 (P1): 36-Campaign Multi-Domain Fresh Uncached Live Qwen3-0.6B Audit ===")
    for r in rows:
        if r["scope_kind"] in ("ALL", "domain"):
            print(
                f"  [{r['scope']:10s}] {r['method']:20s} ({r['track']:23s}) n={r['campaigns']:2d} | "
                f"cert={r['certified_count']:2d}/{r['campaigns']:2d} ({100*r['cert_rate']:5.1f}%, "
                f"CI95=[{100*r['cert_cp95_lo']:4.1f},{100*r['cert_cp95_hi']:4.1f}]%) "
                f"med_steps={r['med_capped_steps']:4.1f} [{r['q25_capped_steps']:4.1f},{r['q75_capped_steps']:4.1f}] "
                f"toks={r['med_live_tokens']:6.0f} infer={r['med_live_infer_s']:5.1f}s "
                f"test_reg={r['mean_unseen_test_regret']:.4f}"
            )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--max-concurrent", type=int, default=min(14, max(1, (os.cpu_count() or 4) // 3)))
    ap.add_argument("--threads-per-worker", type=int, default=min(3, max(1, os.cpu_count() or 3)))
    ap.add_argument("--cap", type=int, default=LIVE_CAP)
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
    domains = ("toolalpaca", "webshop") if args.smoke else DOMAINS
    bases = BASE_SPECS[:1] if args.smoke else BASE_SPECS
    n_splits = 1 if args.smoke else 3
    live_cap = 10 if args.smoke else int(args.cap)

    raw_by_dom: dict[str, list[dict]] = {}
    pools_by_dom: dict[str, list[list[dict]]] = {}
    exemplars: dict[str, dict] = {}
    for dom in domains:
        items = load_worfbench_domain_json(dom)
        raw_by_dom[dom] = items
        exemplars[dom] = items[0]
        pools_by_dom[dom] = _partition_disjoint_pools(items, n_splits=3)
        print(
            f"[v11 Exp 2] {dom:10s}: total={len(items)} disjoint live pools="
            f"{[len(p) for p in pools_by_dom[dom]]}",
            flush=True,
        )

    cal_map: dict[tuple[str, str], dict] = {}
    for dom in domains:
        for b_tag, b_cfg in bases:
            cfgs, _, _ = _build_base_configs(b_cfg)
            cal_map[(dom, b_tag)] = _calibrate_domain_prior_on_dcal(dom, cfgs)

    tmp_dir = out_dir / "_v11_live_tmp"
    tmp_dir.mkdir(parents=True, exist_ok=True)

    # Build 36 independent campaigns x 2 live streams (`indep_os` + coupled `eb_coupled`) = 72 worker jobs
    queue_jobs: list[tuple] = []
    out_files: list[str] = []
    w_id = 0
    for stream_kind in ("indep_os", "eb_coupled"):
        for d_i, dom in enumerate(domains):
            for b_i, (b_tag, b_cfg) in enumerate(bases):
                for sp_i in range(n_splits):
                    cid = f"{dom}_{b_tag}_sp{sp_i}"
                    seed = 910000 + d_i * 1000 + b_i * 100 + sp_i * 11 + 1
                    of = str(tmp_dir / f"job_{cid}_{stream_kind}.jsonl")
                    out_files.append(of)
                    if Path(of).is_file() and not args.smoke:
                        continue  # Resume cleanly from checkpoint if already completed
                    queue_jobs.append(
                        (
                            w_id,
                            cid,
                            dom,
                            b_tag,
                            b_cfg,
                            sp_i,
                            seed,
                            stream_kind,
                            pools_by_dom[dom][sp_i],
                            exemplars[dom],
                            cal_map[(dom, b_tag)],
                            LIVE_EPS,
                            LIVE_DELTA,
                            live_cap,
                            of,
                            args.threads_per_worker,
                        )
                    )
                    w_id += 1

    print(
        f"[v11 Exp 2] Running {len(queue_jobs)} live Qwen3-0.6B worker jobs "
        f"({len(domains)*len(bases)*n_splits} campaigns, cap={live_cap}, "
        f"{args.max_concurrent} concurrent x {args.threads_per_worker} threads)...",
        flush=True,
    )
    ctx = mp.get_context("spawn")
    active: list[mp.Process] = []
    pending = list(queue_jobs)

    while pending or active:
        while pending and len(active) < args.max_concurrent:
            job = pending.pop(0)
            p = ctx.Process(target=_live_worker, args=(job,))
            p.start()
            active.append(p)
        time.sleep(2.0)
        still_active: list[mp.Process] = []
        for p in active:
            if p.is_alive():
                still_active.append(p)
            else:
                p.join()
                if p.exitcode != 0:
                    raise RuntimeError(f"Live worker failed with exitcode {p.exitcode}")
        active = still_active

    live_rows: list[dict] = []
    for f in out_files:
        for line in Path(f).read_text(encoding="utf-8").splitlines():
            if line.strip():
                live_rows.append(json.loads(line))
    meth_idx = {m: i for i, (m, _) in enumerate(LIVE_METHODS)}
    live_rows.sort(key=lambda r: (r["domain"], r["base_tag"], r["split_idx"], meth_idx[r["method"]]))
    (out_dir / "v11_exp2_live_runs.jsonl").write_text("\n".join(json.dumps(r) for r in live_rows) + "\n")

    for f in out_files:
        Path(f).unlink(missing_ok=True)
    try:
        tmp_dir.rmdir()
    except OSError:
        pass

    summarize(out_dir)
    artifacts = ["v11_exp2_live_runs.jsonl", "v11_exp2_live_summary.csv"]
    manifest = {
        "experiment": "v11_exp2_live_worfbench_36campaigns",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "python": platform.python_version(),
        "files": {nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size} for nm in artifacts},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v11 Exp 2] Complete in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
