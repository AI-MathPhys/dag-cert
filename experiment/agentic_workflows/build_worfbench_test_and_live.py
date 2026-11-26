#!/usr/bin/env python3
"""Build disjoint unseen WorFBench test archive (81x32) + run genuine live online Qwen3-0.6B audit.

1. Phase 1 (`joint_root_cert/benchmarks/data/worfbench_qwen3_test_81x32.npz`):
   Evaluates all 81 = 3^4 canonical 4-stage Qwen3-0.6B workflows on 32 strictly
   disjoint unseen WorFBench tasks (`items[17:25]` in each of ToolBench, ToolAlpaca,
   Seal-Tools, and WebShop; disjoint from exemplar `0` and certification pool `1..16`),
   recording exact WorFEval subgraph F1 scores plus exact per-(workflow, task)
   input tokens, generated output tokens, LLM generation calls, and embedding calls.

2. Phase 2 (`results/uct_v4_icml_baselines/exp13_real_world_validation/worfbench_live_online_runs.jsonl`):
   Executes a genuine step-by-step live online certification subset (zero precomputed
   score matrix, zero cross-step caching) where every bandit pull draws an unseen
   ToolAlpaca task (`items[25:85]`), runs live `Qwen3-0.6B` + `Qwen3-Embedding-0.6B`
   inference (`1` generation pass for `greedy`, `2` passes for `mbr_select`), scores
   the output with `WorFEval`, updates confidence intervals, and logs actual CPU
   inference seconds, input/output tokens, and forward passes.
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "4")
os.environ.setdefault("MKL_NUM_THREADS", "4")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "4")
os.environ.setdefault("NUMEXPR_NUM_THREADS", "4")
os.environ.setdefault("TOKENIZERS_PARALLELISM", "false")

import argparse
import itertools
import json
import multiprocessing as mp
from pathlib import Path
import re
import tempfile
import time

import numpy as np

from joint_root_cert import DAG, Problem
from joint_root_cert.search import splitmix_uniform01
from joint_root_cert.tracking import LUCBMicroSession
from joint_root_cert import HybridWitnessDAGLUCBSession
from joint_root_cert.tracking import FlatLUCBSession
from experiment.agentic_workflows.build_worfbench_llm_matrix import (
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


REPO_ROOT = Path(__file__).resolve().parents[2]
DATA_DIR = REPO_ROOT / "joint_root_cert" / "benchmarks" / "data"
VAL_DIR = REPO_ROOT / "results" / "uct_v4_icml_baselines" / "exp13_real_world_validation"


def _build_unseen_test_archive(raw_by_dom: dict[str, list[dict]]) -> Path:
    t0 = time.perf_counter()
    exemplars = {dom: raw_by_dom[dom][0] for dom in DOMAINS}
    tasks = []
    for dom in DOMAINS:
        # Strictly disjoint from certification split [1:17]
        for it in raw_by_dom[dom][17:25]:
            tasks.append({
                "id": it["id"],
                "domain": dom,
                "sys": it["conversations"][0]["content"],
                "user": it["conversations"][1]["content"],
                "gold_text": it["conversations"][-1]["content"],
                "gold_graph": parse_gold_graph(it["conversations"][-1]["content"]),
            })
    print(f"[Phase 1] Loaded {len(tasks)} disjoint unseen WorFBench test tasks.", flush=True)

    import torch
    import transformers

    n_threads = min(32, max(1, os.cpu_count() or 4))
    local_only = hf_local_only()
    torch.set_num_threads(n_threads)
    emb_tok = transformers.AutoTokenizer.from_pretrained("Qwen/Qwen3-Embedding-0.6B", local_files_only=local_only)
    emb_model = transformers.AutoModel.from_pretrained(
        "Qwen/Qwen3-Embedding-0.6B", dtype=torch.float32, local_files_only=local_only
    ).eval()

    def encode_texts(texts: list[str], batch_size: int = 64) -> np.ndarray:
        vecs = []
        for i in range(0, len(texts), batch_size):
            sub = texts[i : i + batch_size]
            inp = emb_tok(sub, padding=True, truncation=True, max_length=192, return_tensors="pt")
            with torch.no_grad():
                out = emb_model(**inp)
                mask = inp["attention_mask"].unsqueeze(-1).float()
                pooled = (out.last_hidden_state * mask).sum(dim=1) / mask.sum(dim=1).clamp(min=1e-9)
                pooled = torch.nn.functional.normalize(pooled, p=2, dim=-1)
            vecs.append(pooled.cpu().numpy())
        return np.concatenate(vecs, axis=0)

    task_heads = []
    parsed_apis = []
    for t in tasks:
        head, apis = extract_task_and_apis(t["user"])
        task_heads.append(head)
        parsed_apis.append(apis)
    head_embs = encode_texts(task_heads)

    all_jobs = []
    for t_idx, t in enumerate(tasks):
        head, apis = task_heads[t_idx], parsed_apis[t_idx]
        if apis:
            api_texts = [f"{nm}: {ds}" for nm, ds in apis]
            api_embs = encode_texts(api_texts)
            sims = api_embs @ head_embs[t_idx]
            top_idx = np.argsort(-sims)[: min(4, len(apis))]
            top4_str = "\n".join(f"- {apis[j][0]}: {apis[j][1]}" for j in top_idx)
            compact_str = "\n".join(f"- {nm}: {ds}" for nm, ds in apis[:10])
            ctx_user = {
                "raw_schema": t["user"][:1400],
                "compact_sig": f"{head}\nAvailable tools:\n{compact_str}",
                "embed_top4": f"{head}\nTop retrieved tools:\n{top4_str}",
            }
        else:
            ctx_user = {
                "raw_schema": t["user"][:1400],
                "compact_sig": re.sub(r"\s+", " ", t["user"]).strip()[:900],
                "embed_top4": head[:700],
            }

        ex = exemplars[t["domain"]]
        ex_head, _ = extract_task_and_apis(ex["conversations"][1]["content"])
        ex_user = ex_head[:420]
        ex_gold = ex["conversations"][-1]["content"][:420]

        for c_mode in CONTEXT_MODES:
            u_txt = ctx_user[c_mode]
            for p_mode in PLAN_MODES:
                if p_mode == "zero_shot":
                    msgs = [{"role": "system", "content": t["sys"]}, {"role": "user", "content": u_txt}]
                elif p_mode == "step_cot":
                    msgs = [{"role": "system", "content": WORFBENCH_SYSTEM_COT}, {"role": "user", "content": u_txt}]
                else:
                    msgs = [
                        {"role": "system", "content": WORFBENCH_SYSTEM_COT},
                        {"role": "user", "content": f"Example task:\n{ex_user}"},
                        {"role": "assistant", "content": ex_gold},
                        {"role": "user", "content": f"Now plan this task:\n{u_txt}"},
                    ]
                all_jobs.append((t_idx, c_mode, p_mode, msgs))

    del emb_model
    tok = transformers.AutoTokenizer.from_pretrained("Qwen/Qwen3-0.6B", local_files_only=local_only, padding_side="left")
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    model = transformers.AutoModelForCausalLM.from_pretrained(
        "Qwen/Qwen3-0.6B", dtype=torch.float32, local_files_only=local_only
    ).eval()

    rendered = []
    for t_idx, c_mode, p_mode, msgs in all_jobs:
        p_str = tok.apply_chat_template(msgs, tokenize=False, add_generation_prompt=True, enable_thinking=False)
        rendered.append((len(p_str), t_idx, c_mode, p_mode, p_str))
    rendered.sort(key=lambda x: x[0])

    gen_lookup: dict[tuple[int, str, str], dict] = {}
    bs = 96
    t_gen = time.perf_counter()
    for start in range(0, len(rendered), bs):
        batch = rendered[start : start + bs]
        prompts = [x[4] for x in batch]
        inp = tok(prompts, return_tensors="pt", padding=True, truncation=True, max_length=520)
        in_len = inp["input_ids"].shape[1]
        attn_lens = inp["attention_mask"].sum(dim=1).tolist()
        with torch.no_grad():
            g_out = model.generate(
                **inp, max_new_tokens=68, do_sample=False, stop_strings=["\n\n"], tokenizer=tok
            )
        torch.manual_seed(20011 + start)
        with torch.no_grad():
            s_out = model.generate(
                **inp, max_new_tokens=68, do_sample=True, temperature=0.45, top_p=0.85,
                stop_strings=["\n\n"], tokenizer=tok,
            )
        for b_idx, (_, t_idx, c_mode, p_mode, _) in enumerate(batch):
            g_ids = g_out[b_idx][in_len:]
            s_ids = s_out[b_idx][in_len:]
            g_toks = int((g_ids != tok.pad_token_id).sum().item())
            s_toks = int((s_ids != tok.pad_token_id).sum().item())
            gen_lookup[(t_idx, c_mode, p_mode)] = {
                "greedy": tok.decode(g_ids, skip_special_tokens=True),
                "temp_sample": tok.decode(s_ids, skip_special_tokens=True),
                "in_tok": int(attn_lens[b_idx]),
                "g_out_tok": max(1, g_toks),
                "s_out_tok": max(1, s_toks),
            }
        print(
            f"  [Phase 1 batch {start // bs + 1}/{(len(rendered) + bs - 1) // bs}] "
            f"done in {time.perf_counter() - t_gen:.1f}s",
            flush=True,
        )
    del model

    emb_model = transformers.AutoModel.from_pretrained(
        "Qwen/Qwen3-Embedding-0.6B", dtype=torch.float32, local_files_only=local_only
    ).eval()
    unique_nodes: set[str] = {"START", "END"}
    parsed_cache: dict[tuple[int, str, str, str, str], dict] = {}
    for (t_idx, c_mode, p_mode), rec in gen_lookup.items():
        for d_mode in ("greedy", "temp_sample"):
            for v_mode in VERIFY_MODES:
                pg = parse_pred_graph(rec[d_mode], v_mode)
                parsed_cache[(t_idx, c_mode, p_mode, d_mode, v_mode)] = pg
                unique_nodes.update(pg["nodes"])
    for t in tasks:
        unique_nodes.update(t["gold_graph"]["nodes"])

    node_list = sorted(unique_nodes)
    node_vecs = encode_texts(node_list, batch_size=128)
    emb_map = {s: node_vecs[i] for i, s in enumerate(node_list)}

    workflows = list(itertools.product(CONTEXT_MODES, PLAN_MODES, DECODE_MODES, VERIFY_MODES))
    score_matrix = np.zeros((len(workflows), len(tasks)), dtype=np.float32)
    in_tok_matrix = np.zeros((len(workflows), len(tasks)), dtype=np.int32)
    out_tok_matrix = np.zeros((len(workflows), len(tasks)), dtype=np.int32)
    gen_calls_vec = np.zeros(len(workflows), dtype=np.int32)
    emb_calls_vec = np.zeros(len(workflows), dtype=np.int32)

    for w_idx, (c_m, p_m, d_m, v_m) in enumerate(workflows):
        gen_calls_vec[w_idx] = 2 if d_m == "mbr_select" else 1
        emb_calls_vec[w_idx] = (1 if c_m == "embed_top4" else 0) + (1 if d_m == "mbr_select" else 0)
        for t_idx, t in enumerate(tasks):
            rec = gen_lookup[(t_idx, c_m, p_m)]
            if d_m == "greedy":
                pg = parsed_cache[(t_idx, c_m, p_m, "greedy", v_m)]
                in_tok_matrix[w_idx, t_idx] = rec["in_tok"]
                out_tok_matrix[w_idx, t_idx] = rec["g_out_tok"]
            elif d_m == "temp_sample":
                pg = parsed_cache[(t_idx, c_m, p_m, "temp_sample", v_m)]
                in_tok_matrix[w_idx, t_idx] = rec["in_tok"]
                out_tok_matrix[w_idx, t_idx] = rec["s_out_tok"]
            else:
                pg_g = parsed_cache[(t_idx, c_m, p_m, "greedy", v_m)]
                pg_s = parsed_cache[(t_idx, c_m, p_m, "temp_sample", v_m)]
                def align_score(g_cand):
                    subs = [s for s in g_cand["nodes"] if s not in ("START", "END")]
                    if not subs or not g_cand["edges"]:
                        return -1.0
                    s_mat = np.stack([emb_map[s] for s in subs], axis=0)
                    return float(np.mean(s_mat @ head_embs[t_idx]))
                pg = pg_s if align_score(pg_s) > align_score(pg_g) + 0.01 else pg_g
                in_tok_matrix[w_idx, t_idx] = 2 * rec["in_tok"]
                out_tok_matrix[w_idx, t_idx] = rec["g_out_tok"] + rec["s_out_tok"]
            score_matrix[w_idx, t_idx] = worfeval_graph_f1(pg, t["gold_graph"], emb_map)

    out_npz = DATA_DIR / "worfbench_qwen3_test_81x32.npz"
    np.savez_compressed(
        out_npz,
        scores=score_matrix,
        in_tokens=in_tok_matrix,
        out_tokens=out_tok_matrix,
        gen_calls=gen_calls_vec,
        emb_calls=emb_calls_vec,
        workflows=np.array(["|".join(w) for w in workflows]),
        task_ids=np.array([t["id"] for t in tasks]),
        domains=np.array([t["domain"] for t in tasks]),
    )
    print(
        f"[Phase 1] Saved {out_npz} ({score_matrix.shape}), max unseen F1={score_matrix.mean(axis=1).max():.4f} "
        f"in {time.perf_counter()-t0:.1f}s!",
        flush=True,
    )
    return out_npz


def _live_worker(job_spec: tuple[int, str, int, list[dict], dict, str]) -> None:
    w_id, method, seed, live_tasks, exemplar, out_file = job_spec
    os.environ["OMP_NUM_THREADS"] = "4"
    os.environ["MKL_NUM_THREADS"] = "4"
    os.environ["OPENBLAS_NUM_THREADS"] = "4"
    import torch
    import transformers

    torch.set_num_threads(4)
    torch.set_num_interop_threads(1)

    local_only = hf_local_only()
    tok = transformers.AutoTokenizer.from_pretrained("Qwen/Qwen3-0.6B", local_files_only=local_only)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    llm = transformers.AutoModelForCausalLM.from_pretrained(
        "Qwen/Qwen3-0.6B", dtype=torch.float32, local_files_only=local_only
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
            pooled = (out.last_hidden_state * mask).sum(dim=1) / mask.sum(dim=1).clamp(min=1e-9)
            pooled = torch.nn.functional.normalize(pooled, p=2, dim=-1)
        return pooled.cpu().numpy()

    ex_head, _ = extract_task_and_apis(exemplar["conversations"][1]["content"])
    ex_user = ex_head[:420]
    ex_gold = exemplar["conversations"][-1]["content"][:420]

    # Symmetric 4-stage d=2 zero-containment workflow DAG from base (1, 0, 0, 0) [compact_sig|zero_shot|greedy|raw_parse]
    base = (1, 0, 0, 0)
    def apply_u(eds: tuple[int, ...]) -> tuple[int, int, int, int]:
        o = list(base)
        for s in eds:
            o[s] = 2
        return (o[0], o[1], o[2], o[3])

    anchors = [(s, apply_u((s,))) for s in range(4)]
    combos = [tuple(sorted((i, j))) for i in range(4) for j in range(i + 1, 4)]
    cfgs = sorted({c for _, c in anchors} | {apply_u(e) for e in combos})  # M = 10 workflows

    rows: list[tuple[int, ...]] = [()]
    a_ids = [1, 2, 3, 4]
    rows.extend([()] * 4)
    rows[0] = tuple(a_ids)
    c_id = {e: 5 + i for i, e in enumerate(combos)}
    rows.extend([()] * len(combos))
    first_leaf = 5 + len(combos)
    l_id = {c: first_leaf + i for i, c in enumerate(cfgs)}
    rows.extend([()] * len(cfgs))
    for idx, (s, c1) in enumerate(anchors):
        rows[a_ids[idx]] = tuple([l_id[c1]] + [c_id[tuple(sorted((s, s2)))] for s2 in range(4) if s2 != s])
    for e in combos:
        rows[c_id[e]] = (l_id[apply_u(e)],)
    dag = DAG(rows)
    dummy_means = {first_leaf + i: 0.5 for i in range(len(cfgs))}

    class _LiveProblem(Problem):
        def oracle(self, s_val: int):
            s64 = s_val & 0xFFFFFFFFFFFFFFFF
            n_pool = len(live_tasks)

            class _LiveOracle:
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

            return _LiveOracle()

    prob = _LiveProblem("worfbench_live_toolalpaca_u2", dag, dummy_means)
    eps = 0.08
    delta = 0.10
    cap = 235

    t_run0 = time.perf_counter()
    if method == "opt_sep":
        sess = HybridWitnessDAGLUCBSession(prob, seed, eps, mode="opt_sep", delta=delta, schedule="emp_bernstein")
    elif method == "flat_lucb_root":
        sess = FlatLUCBSession(prob, seed, eps, delta=delta, schedule="emp_bernstein", stop_rule="root_exact")
    elif method == "flat_lucb_term":
        sess = FlatLUCBSession(prob, seed, eps, delta=delta, schedule="emp_bernstein", stop_rule="terminal")
    elif method == "lucb_micro_marg":
        sess = LUCBMicroSession(prob, seed, eps, delta=delta, schedule="emp_bernstein", stop_rule="marginal")
    else:
        raise ValueError(method)

    while not sess.certified and sess.calls < cap:
        sess.step()
        if sess.calls % 50 == 0:
            print(
                f"  [live worker {w_id} {method} s={seed}] step {sess.calls}/{cap} "
                f"(infer_s={sess.oracle.live_infer_s:.1f}s, gen_calls={sess.oracle.live_gen_calls})",
                flush=True,
            )

    total_wall_s = time.perf_counter() - t_run0
    action_names = ("Context->embed_top4", "Planner->one_shot", "Decoder->mbr_select", "Verifier->dag_repair")
    rec = {
        "method": method,
        "seed": seed,
        "eps": eps,
        "delta": delta,
        "cap": cap,
        "certified": bool(sess.certified),
        "steps": int(sess.calls),
        "capped_steps": int(sess.calls) if sess.certified else cap,
        "action_idx": int(sess.action),
        "action_label": action_names[int(sess.action)],
        "live_infer_s": round(float(sess.oracle.live_infer_s), 3),
        "total_wall_s": round(float(total_wall_s), 3),
        "live_in_tokens": int(sess.oracle.live_in_tokens),
        "live_out_tokens": int(sess.oracle.live_out_tokens),
        "live_total_tokens": int(sess.oracle.live_in_tokens + sess.oracle.live_out_tokens),
        "live_gen_calls": int(sess.oracle.live_gen_calls),
        "live_emb_calls": int(sess.oracle.live_emb_calls),
    }
    Path(out_file).write_text(json.dumps(rec) + "\n", encoding="utf-8")
    print(
        f"  [DONE live worker {w_id} {method} s={seed}] cert={rec['certified']} "
        f"steps={rec['steps']} tokens={rec['live_total_tokens']} infer_s={rec['live_infer_s']:.1f}s",
        flush=True,
    )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--phase1-only", action="store_true", help="Only rebuild worfbench_qwen3_test_81x32.npz")
    args = ap.parse_args()

    VAL_DIR.mkdir(parents=True, exist_ok=True)
    raw_by_dom = {dom: load_worfbench_domain_json(dom) for dom in DOMAINS}

    _build_unseen_test_archive(raw_by_dom)
    if args.phase1_only:
        return

    # Phase 2: 8 parallel genuine live online Qwen3-0.6B runs
    exemplar = raw_by_dom["toolalpaca"][0]
    live_tasks = [
        {
            "id": it["id"],
            "sys": it["conversations"][0]["content"],
            "user": it["conversations"][1]["content"],
            "gold_graph": parse_gold_graph(it["conversations"][-1]["content"]),
        }
        for it in raw_by_dom["toolalpaca"][25:85]
    ]
    print(f"[Phase 2] Launching 8 genuine live online Qwen3-0.6B runs across {len(live_tasks)} unseen tasks...", flush=True)

    methods = ("opt_sep", "flat_lucb_root", "flat_lucb_term", "lucb_micro_marg")
    seeds = (810001, 810002)
    tmp_dir = Path(tempfile.gettempdir()) / "worfbench_live_runs"
    tmp_dir.mkdir(parents=True, exist_ok=True)

    ctx = mp.get_context("spawn")
    procs = []
    out_files = []
    w_id = 0
    for s in seeds:
        for m in methods:
            of = str(tmp_dir / f"live_{w_id:02d}.json")
            out_files.append(of)
            p = ctx.Process(target=_live_worker, args=((w_id, m, s, live_tasks, exemplar, of),))
            p.start()
            procs.append(p)
            w_id += 1

    for p in procs:
        p.join()
        if p.exitcode != 0:
            raise RuntimeError(f"Live worker failed with code {p.exitcode}")

    rows = [json.loads(Path(f).read_text(encoding="utf-8").strip()) for f in out_files]
    rows.sort(key=lambda r: (r["seed"], methods.index(r["method"])))
    live_jsonl = VAL_DIR / "worfbench_live_online_runs.jsonl"
    live_jsonl.write_text("\n".join(json.dumps(r) for r in rows) + "\n", encoding="utf-8")
    print(f"[Phase 2] Saved {len(rows)} genuine live online runs to {live_jsonl}!", flush=True)


if __name__ == "__main__":
    main()
