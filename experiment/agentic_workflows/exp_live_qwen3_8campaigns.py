"""Experiment v10-3: Expanded Genuine Fresh Uncached Live Qwen3-0.6B WorFBench Cohort.

Expands the n=2 live proof-of-concept from v8_5 into a statistically substantive
multi-campaign, multi-seed live uncached cohort (8 independent paired live campaigns:
2 distinct 4-stage workflow base configurations x 4 paired seeds x 3 methods = 24
completely fresh uncached Qwen3-0.6B + Qwen3-Embedding-0.6B online certification runs):

  - Strict 3-way disjoint ToolAlpaca split (zero data leakage):
      * Exemplar (`items[0]`): fixed one-shot prompt template only.
      * Calibration (`items[1:17]`): Type-II ML stage-kernel & token-cost calibration.
      * Untouched Test (`items[17:25]`): held-out WorFEval F1 generalization evaluation.
      * Fresh Live Pool (`items[25:85]`): 60 unseen tasks executed step-by-step live
        with ZERO precomputed score matrix and ZERO cross-step caching.
  - Base A `(1, 0, 0, 0)` x 4 seeds + Base B `(0, 0, 0, 0)` x 4 seeds = 8 paired
    live campaigns across `indep_os`, `cd_joint_calibrated`, and `cd_joint_hybrid`
    (eps=0.08, delta=0.10, cap=140 live evaluations per run).
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

from joint_root_cert import DAG, Problem
from joint_root_cert.search import splitmix_uniform01
from joint_root_cert import HybridWitnessDAGLUCBSession
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
from experiment.agentic_workflows.exp_worfbench_unseen_live import (
    _build_workflow_candidate_kernels,
    _calibrate_live_prior_on_dcal,
)


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "results/bayesian_ucd_v1/v10_exp3_live_worfbench_expanded"
LIVE_METHODS = ("indep_os", "cd_joint_calibrated", "cd_joint_hybrid")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _build_base_configs(base: tuple[int, int, int, int]) -> tuple[list[tuple[int, int, int, int]], list[tuple[int, tuple[int, int, int, int]]], list[tuple[int, int]]]:
    def apply_u(eds: tuple[int, ...]) -> tuple[int, int, int, int]:
        o = list(base)
        for s in eds:
            o[s] = 2
        return (o[0], o[1], o[2], o[3])

    anchors = [(s, apply_u((s,))) for s in range(4)]
    combos = [tuple(sorted((i, j))) for i in range(4) for j in range(i + 1, 4)]
    cfgs = sorted({c for _, c in anchors} | {apply_u(e) for e in combos})
    return cfgs, anchors, combos


def _live_worker_multi_base(args_tuple: tuple) -> None:
    (w_id, base_tag, base_cfg, method, seed, live_tasks, exemplar, cal_info, eps, delta, cap, out_file, n_threads) = args_tuple
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

    prob = _FreshLiveProblem(f"worfbench_live_{base_tag}", dag, dummy_means)
    k_cands = _build_workflow_candidate_kernels(cfgs)

    test_leaf_means = np.asarray(cal_info["test_leaf_means"], dtype=np.float64)
    test_means_dict = {first_leaf + i: float(test_leaf_means[i]) for i in range(len(cfgs))}
    test_vals = dag.optimal_values(test_means_dict)
    test_opt = float(test_vals[dag.root])
    act_test_f1 = [float(test_vals[c]) for c in dag.children[dag.root]]

    t_run0 = time.perf_counter()
    if method == "indep_os":
        sess = HybridWitnessDAGLUCBSession(prob, seed, eps, mode="opt_sep", delta=delta, schedule="emp_bernstein")
    else:
        en_eb = True
        m_delta = 0.5 * delta if method == "cd_joint_hybrid" else delta
        gp_m = CalibratedGPPosteriorModel(
            kernel=np.asarray(cal_info["best_kernel"], dtype=np.float64),
            prior_mean=float(cal_info["prior_mean"]),
            obs_std=float(cal_info["obs_std"]),
            delta=m_delta,
            enable_eb_calib=en_eb,
            kernel_candidates=k_cands,
            calib_steps=(24, 60),
            loo_inflate=True,
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
        if sess.calls % 20 == 0:
            print(
                f"  [live {w_id:02d} {base_tag} {method:19s} s={seed}] step={sess.calls}/{cap} "
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
        "base_tag": base_tag,
        "base_config": "".join(map(str, base_cfg)),
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
        f"  [DONE live {w_id:02d} {base_tag} {method:19s} s={seed}] cert={cert} steps={rec['steps']} "
        f"toks={rec['live_total_tokens']} infer={rec['live_infer_s']:.1f}s "
        f"cert_s={rec['cert_oracle_s']:.3f}s test_f1={rec['unseen_test_f1']:.4f} reg={rec['unseen_test_regret']:.4f}",
        flush=True,
    )


def summarize(dest: Path) -> None:
    pb = dest / "v10_exp3_live_runs.jsonl"
    if not pb.exists():
        return
    runs = [json.loads(x) for x in pb.read_text().splitlines() if x.strip()]
    rows: list[dict] = []
    for scope in ("ALL", "base_1000", "base_0000"):
        for meth in LIVE_METHODS:
            sub = [r for r in runs if r["method"] == meth and (scope == "ALL" or r["base_tag"] == scope)]
            if not sub:
                continue
            n = len(sub)
            rows.append(
                {
                    "scope": scope,
                    "method": meth,
                    "runs": n,
                    "live_cert_rate": round(sum(1 for r in sub if r["certified"]) / n, 4),
                    "med_live_steps": round(float(np.median([r["steps"] for r in sub])), 1),
                    "mean_live_steps": round(float(np.mean([r["steps"] for r in sub])), 1),
                    "med_live_tokens": round(float(np.median([r["live_total_tokens"] for r in sub])), 0),
                    "mean_live_tokens": round(float(np.mean([r["live_total_tokens"] for r in sub])), 0),
                    "med_live_infer_s": round(float(np.median([r["live_infer_s"] for r in sub])), 2),
                    "med_cert_oracle_s": round(float(np.median([r["cert_oracle_s"] for r in sub])), 4),
                    "mean_unseen_test_f1": round(float(np.mean([r["unseen_test_f1"] for r in sub])), 5),
                    "mean_unseen_test_regret": round(float(np.mean([r["unseen_test_regret"] for r in sub])), 5),
                }
            )
    with (dest / "v10_exp3_live_summary.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    print("\n=== v10 Exp 3: Expanded Fresh Uncached Live Qwen3-0.6B Certification ===")
    for r in rows:
        print(
            f"  [{r['scope']:9s}] {r['method']:20s} (n={r['runs']:2d}) | cert={100*r['live_cert_rate']:5.1f}% "
            f"med_steps={r['med_live_steps']:5.1f} toks={r['med_live_tokens']:7.0f} "
            f"infer={r['med_live_infer_s']:6.1f}s conic={r['med_cert_oracle_s']:.3f}s "
            f"test_f1={r['mean_unseen_test_f1']:.4f} reg={r['mean_unseen_test_regret']:.4f}"
        )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--max-concurrent", type=int, default=min(12, max(1, (os.cpu_count() or 4) // 4)))
    ap.add_argument("--threads-per-worker", type=int, default=min(4, max(1, os.cpu_count() or 4)))
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    if args.summarize_only:
        summarize(out_dir)
        return

    t0 = time.perf_counter()
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

    bases = [
        ("base_1000", (1, 0, 0, 0), [890101, 890102, 890103, 890104]),
        ("base_0000", (0, 0, 0, 0), [890201, 890202, 890203, 890204]),
    ]
    if args.smoke:
        bases = [("base_1000", (1, 0, 0, 0), [890101])]
        methods = ("cd_joint_hybrid", "indep_os")
        live_cap = 20
    else:
        methods = LIVE_METHODS
        live_cap = 140

    cal_map = {}
    for b_tag, b_cfg, _ in bases:
        cfgs, _, _ = _build_base_configs(b_cfg)
        cal_map[b_tag] = _calibrate_live_prior_on_dcal(cfgs)
        print(
            f"[v10 Exp 3] {b_tag} D_cal prior: kernel={cal_map[b_tag]['best_kernel_name']} "
            f"m0={cal_map[b_tag]['prior_mean']:.3f} obs_std={cal_map[b_tag]['obs_std']:.3f}",
            flush=True,
        )

    tmp_dir = out_dir / "_live_tmp"
    tmp_dir.mkdir(parents=True, exist_ok=True)

    # Schedule heaviest first (`indep_os` hits cap=140) for tight makespan across workers!
    method_order = [m for m in ("indep_os", "cd_joint_hybrid", "cd_joint_calibrated") if m in methods]
    queue_jobs: list[tuple] = []
    out_files: list[str] = []
    w_id = 0
    for m in method_order:
        for b_tag, b_cfg, seeds in bases:
            for s in seeds:
                of = str(tmp_dir / f"live_{w_id:02d}_{b_tag}_{m}_{s}.json")
                out_files.append(of)
                queue_jobs.append((
                    w_id, b_tag, b_cfg, m, s, live_tasks, exemplar,
                    cal_map[b_tag], 0.08, 0.10, live_cap, of, args.threads_per_worker,
                ))
                w_id += 1

    print(
        f"[v10 Exp 3] Running {len(queue_jobs)} genuine uncached Qwen3-0.6B live runs "
        f"({args.max_concurrent} concurrent x {args.threads_per_worker} threads)...",
        flush=True,
    )
    ctx = mp.get_context("spawn")
    active: list[mp.Process] = []
    pending = list(queue_jobs)

    while pending or active:
        while pending and len(active) < args.max_concurrent:
            job = pending.pop(0)
            p = ctx.Process(target=_live_worker_multi_base, args=(job,))
            p.start()
            active.append(p)
        time.sleep(2.0)
        still_active = []
        for p in active:
            if p.is_alive():
                still_active.append(p)
            else:
                p.join()
                if p.exitcode != 0:
                    raise RuntimeError(f"Live worker failed with exitcode {p.exitcode}")
        active = still_active

    live_rows = [json.loads(Path(f).read_text(encoding="utf-8").strip()) for f in out_files]
    live_rows.sort(key=lambda r: (r["base_tag"], r["seed"], LIVE_METHODS.index(r["method"])))
    (out_dir / "v10_exp3_live_runs.jsonl").write_text("\n".join(json.dumps(r) for r in live_rows) + "\n")
    for f in out_files:
        Path(f).unlink(missing_ok=True)
    try:
        tmp_dir.rmdir()
    except OSError:
        pass

    summarize(out_dir)
    artifacts = ["v10_exp3_live_runs.jsonl", "v10_exp3_live_summary.csv"]
    manifest = {
        "experiment": "v10_exp3_live_worfbench_expanded",
        "smoke": args.smoke,
        "elapsed_s": round(time.perf_counter() - t0, 2),
        "python": platform.python_version(),
        "files": {nm: {"sha256": _sha256(out_dir / nm), "bytes": (out_dir / nm).stat().st_size} for nm in artifacts},
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"[v10 Exp 3] Complete in {manifest['elapsed_s']:.1f}s.", flush=True)


if __name__ == "__main__":
    main()
