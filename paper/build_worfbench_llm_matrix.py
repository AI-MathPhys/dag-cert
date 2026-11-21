#!/usr/bin/env python3
"""Execute real Qwen3-0.6B + Qwen3-Embedding-0.6B agentic workflows on WorFBench.

Evaluates all 81 = 3 x 3 x 3 x 3 canonical 4-stage tool-workflow configurations:
  Stage 0 (Tool Context):   raw_schema | compact_sig | embed_top4
  Stage 1 (Planning):       zero_shot  | step_cot    | one_shot
  Stage 2 (Decoding/MBR):   greedy     | temp_sample | mbr_select
  Stage 3 (DAG Verifier):   raw_parse  | norm_endpts | dag_repair

Across 64 held-out multi-tool workflow planning tasks (16 each from ToolBench,
ToolAlpaca, Seal-Tools, and WebShop; exemplar index 0 held out strictly for one_shot),
scoring every (workflow, task) execution with the official WorFBench (ICLR 2025)
bipartite node-matching + largest-connected-subgraph F1 metric (`t_eval_graph`).
"""
from __future__ import annotations

import os

_DEFAULT_THREADS = str(min(32, max(1, os.cpu_count() or 4)))
os.environ.setdefault("OMP_NUM_THREADS", _DEFAULT_THREADS)
os.environ.setdefault("MKL_NUM_THREADS", _DEFAULT_THREADS)
os.environ.setdefault("OPENBLAS_NUM_THREADS", _DEFAULT_THREADS)
os.environ.setdefault("NUMEXPR_NUM_THREADS", _DEFAULT_THREADS)
os.environ.setdefault("TOKENIZERS_PARALLELISM", "false")

import ast
import itertools
import json
import multiprocessing as mp
from pathlib import Path
import re
import time

import networkx as nx
import numpy as np
import requests

REPO_ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = REPO_ROOT / "dag_mcts" / "data"
WORFBENCH_RAW_DIR = DATA_DIR / "worfbench_raw"

DOMAINS = ("toolbench", "toolalpaca", "seal_tools", "webshop")
TASKS_PER_DOMAIN = 16


def hf_local_only() -> bool:
    """Respect HF_HUB_OFFLINE=1 if set; otherwise auto-download into the local HF cache."""
    return os.environ.get("HF_HUB_OFFLINE", "").strip().lower() in ("1", "true", "yes")


def load_worfbench_domain_json(dom: str, timeout: int = 30) -> list[dict]:
    """Load WorFBench gold trajectories from local cache if fetched, else download from GitHub."""
    local_path = WORFBENCH_RAW_DIR / f"{dom}_graph_eval.json"
    if local_path.is_file():
        return json.loads(local_path.read_text(encoding="utf-8"))
    url = f"https://raw.githubusercontent.com/zjunlp/WorfBench/main/gold_traj/{dom}/graph_eval.json"
    resp = requests.get(url, timeout=timeout)
    resp.raise_for_status()
    items = resp.json()
    try:
        WORFBENCH_RAW_DIR.mkdir(parents=True, exist_ok=True)
        local_path.write_text(json.dumps(items), encoding="utf-8")
    except OSError:
        pass
    return items

CONTEXT_MODES = ("raw_schema", "compact_sig", "embed_top4")
PLAN_MODES = ("zero_shot", "step_cot", "one_shot")
DECODE_MODES = ("greedy", "temp_sample", "mbr_select")
VERIFY_MODES = ("raw_parse", "norm_endpts", "dag_repair")

WORFBENCH_SYSTEM_COT = (
    "You are an expert task planner. Decompose the assigned task into atomic subtasks "
    "using the provided tools/actions, then output their precedence DAG starting at START "
    "and ending at END.\n"
    "Strictly use this exact output format:\n"
    "Node:\n1. <subtask 1>\n2. <subtask 2>\n...\n"
    "Edges:\n(START,1) (1,2) ... (n,END)"
)


def parse_gold_graph(workflow: str) -> dict[str, list]:
    node_matches = re.findall(r"\d+[:.]\s*(.+)", workflow)
    nodes = ["START"] + [m.strip() for m in node_matches if m.strip()] + ["END"]
    edge_matches = re.findall(r"\(\s*(\d+|START)\s*,\s*(\d+|END)\s*\)", workflow)
    edges = []
    n_end = len(nodes) - 1
    for u_s, v_s in edge_matches:
        u = 0 if u_s == "START" else (n_end if u_s == "END" else int(u_s))
        v = 0 if v_s == "START" else (n_end if v_s == "END" else int(v_s))
        if 0 <= u <= n_end and 0 <= v <= n_end:
            edges.append((u, v))
    return {"nodes": nodes, "edges": edges}


def parse_pred_graph(text: str, mode: str) -> dict[str, list]:
    if mode == "raw_parse":
        if "Node" not in text:
            return {"nodes": [], "edges": []}
        node_matches = re.findall(r"\d+[:.] (.+)", text)
        if not node_matches:
            return {"nodes": [], "edges": []}
        nodes = ["START"] + [m.strip() for m in node_matches] + ["END"]
        edge_matches = re.findall(r"\(\s*(\d+|START)\s*,\s*(\d+|END)\s*\)", text)
        if not edge_matches:
            return {"nodes": [], "edges": []}
        n_end = len(nodes) - 1
        edges = []
        for u_s, v_s in edge_matches:
            u = 0 if u_s == "START" else int(u_s)
            v = n_end if v_s == "END" else int(v_s)
            if 0 <= u <= n_end and 0 <= v <= n_end:
                edges.append((u, v))
        return {"nodes": nodes, "edges": edges}

    # norm_endpts and dag_repair normalize common formatting variants
    cleaned = re.sub(r"<think>.*?</think>", "", text, flags=re.S).strip()
    node_matches = re.findall(r"(?:^|\n)\s*(\d+)\s*[:.)\-]\s*(.+)", cleaned)
    subtasks = []
    for _, desc in node_matches:
        d = desc.strip()
        if d and d.lower() not in ("start", "end", "finish", " edges", "edges:"):
            subtasks.append(d)
    if not subtasks:
        return {"nodes": [], "edges": []}
    nodes = ["START"] + subtasks + ["END"]
    n_end = len(nodes) - 1

    norm_e = re.sub(r"\b(?:Finish|finish|FINISH|End|end)\b", "END", cleaned)
    norm_e = re.sub(r"\b(?:Start|start)\b", "START", norm_e)
    raw_pairs = re.findall(r"[\(\[]\s*(\d+|START)\s*(?:,|->|to)\s*(\d+|END)\s*[\)\]]", norm_e)
    edges = []
    for u_s, v_s in raw_pairs:
        u = 0 if u_s == "START" else (n_end if u_s == "END" else int(u_s))
        v = 0 if v_s == "START" else (n_end if v_s == "END" else int(v_s))
        if 0 <= u <= n_end and 0 <= v <= n_end and u != v:
            edges.append((u, v))

    if mode == "norm_endpts":
        return {"nodes": nodes, "edges": edges} if edges else {"nodes": [], "edges": []}

    # dag_repair: enforce valid DAG (u < v topological order if cyclic), connect orphans
    dedup = []
    seen = set()
    dg = nx.DiGraph()
    dg.add_nodes_from(range(n_end + 1))
    for u, v in edges:
        if u == n_end or v == 0 or (u, v) in seen:
            continue
        dg.add_edge(u, v)
        if not nx.is_directed_acyclic_graph(dg):
            dg.remove_edge(u, v)
        else:
            seen.add((u, v))
            dedup.append((u, v))
    if not dedup:
        # Sequential fallback chain across extracted subtasks
        dedup = [(i, i + 1) for i in range(n_end)]
    else:
        in_deg = {i: 0 for i in range(1, n_end)}
        out_deg = {i: 0 for i in range(1, n_end)}
        for u, v in dedup:
            if 1 <= v < n_end:
                in_deg[v] += 1
            if 1 <= u < n_end:
                out_deg[u] += 1
        for i in range(1, n_end):
            if in_deg[i] == 0 and (0, i) not in seen:
                dedup.append((0, i))
            if out_deg[i] == 0 and (i, n_end) not in seen:
                dedup.append((i, n_end))
    return {"nodes": nodes, "edges": dedup}


def extract_task_and_apis(user_content: str) -> tuple[str, list[tuple[str, str]]]:
    for marker in ("api_list:", "The api list you can use:", "api_list ="):
        if marker in user_content:
            head, tail = user_content.split(marker, 1)
            apis = []
            try:
                parsed = ast.literal_eval(tail.strip())
                if isinstance(parsed, list):
                    for entry in parsed:
                        if isinstance(entry, dict):
                            nm = str(entry.get("name", entry.get("api_name", "tool")))
                            ds = str(entry.get("description", ""))[:140]
                            apis.append((nm, ds))
            except Exception:
                for m in re.finditer(r"'name'\s*:\s*'([^']+)'[^}]*?'description'\s*:\s*'([^']*)'", tail):
                    apis.append((m.group(1), m.group(2)[:140]))
            return head.strip(), apis
    return user_content.strip(), []


def worfeval_graph_f1(pred_g: dict, gt_g: dict, emb_map: dict[str, np.ndarray], thresh: float = 0.6) -> float:
    p_nodes, g_nodes = pred_g["nodes"], gt_g["nodes"]
    if len(p_nodes) <= 2 or len(g_nodes) <= 2 or not pred_g["edges"] or not gt_g["edges"]:
        return 0.0
    p_mat = np.stack([emb_map[s] for s in p_nodes], axis=0)
    g_mat = np.stack([emb_map[s] for s in g_nodes], axis=0)
    sim = np.maximum(p_mat @ g_mat.T, 0.0)

    bip = nx.Graph()
    for i in range(len(p_nodes)):
        for j in range(len(g_nodes)):
            if sim[i, j] > thresh:
                bip.add_edge(("p", i), ("g", j), weight=float(sim[i, j]))
    matching = nx.max_weight_matching(bip)
    p2g = {}
    for a, b in matching:
        if a[0] == "p":
            p2g[a[1]] = b[1]
        else:
            p2g[b[1]] = a[1]
    if not p2g:
        return 0.0
    matched_p = set(p2g.keys())
    matched_g = set(p2g.values())
    gt_edge_set = {(u, v) for u, v in gt_g["edges"] if u in matched_g and v in matched_g}
    public_p_edges = []
    public_g_edges = []
    for u, v in pred_g["edges"]:
        if u in matched_p and v in matched_p:
            gu, gv = p2g[u], p2g[v]
            if (gu, gv) in gt_edge_set:
                public_p_edges.append((u, v))
                public_g_edges.append((gu, gv))

    def lcc_size(nodes_sub, edges_sub):
        if not nodes_sub:
            return 0
        ug = nx.Graph()
        ug.add_nodes_from(nodes_sub)
        ug.add_edges_from(edges_sub)
        return max(len(c) for c in nx.connected_components(ug))

    prec = lcc_size(matched_p, public_p_edges) / len(p_nodes)
    rec = lcc_size(matched_g, public_g_edges) / len(g_nodes)
    return float(2.0 * prec * rec / (prec + rec)) if (prec + rec) > 0 else 0.0


def _gen_worker(proc_id: int, jobs: list[tuple[int, str, str, list[dict]]], out_path: str) -> None:
    import torch
    import transformers

    torch.set_num_threads(min(12, max(1, os.cpu_count() or 4)))
    torch.set_num_interop_threads(1)
    local_only = hf_local_only()
    tok = transformers.AutoTokenizer.from_pretrained("Qwen/Qwen3-0.6B", local_files_only=local_only, padding_side="left")
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    model = transformers.AutoModelForCausalLM.from_pretrained(
        "Qwen/Qwen3-0.6B", dtype=torch.float32, local_files_only=local_only
    ).eval()

    # Pre-render and sort by character length so short prompts never pad to 560 tokens
    rendered = []
    for t_idx, c_mode, p_mode, msgs in jobs:
        p_str = tok.apply_chat_template(msgs, tokenize=False, add_generation_prompt=True, enable_thinking=False)
        rendered.append((len(p_str), t_idx, c_mode, p_mode, p_str))
    rendered.sort(key=lambda x: x[0])

    results = []
    bs = 16
    t_w0 = time.perf_counter()
    for start in range(0, len(rendered), bs):
        batch = rendered[start : start + bs]
        prompts = [x[4] for x in batch]
        inp = tok(prompts, return_tensors="pt", padding=True, truncation=True, max_length=560)
        in_len = inp["input_ids"].shape[1]
        with torch.no_grad():
            g_out = model.generate(**inp, max_new_tokens=84, do_sample=False)
        torch.manual_seed(10007 + proc_id * 97 + start)
        with torch.no_grad():
            s_out = model.generate(**inp, max_new_tokens=84, do_sample=True, temperature=0.45, top_p=0.85)
        for b_idx, (_, t_idx, c_mode, p_mode, _) in enumerate(batch):
            g_txt = tok.decode(g_out[b_idx][in_len:], skip_special_tokens=True)
            s_txt = tok.decode(s_out[b_idx][in_len:], skip_special_tokens=True)
            results.append({
                "task_idx": t_idx,
                "ctx": c_mode,
                "plan": p_mode,
                "greedy": g_txt,
                "temp_sample": s_txt,
            })
        print(
            f"  [worker {proc_id}] completed {min(start + bs, len(rendered))}/{len(rendered)} "
            f"(seq_len={in_len}, elapsed={time.perf_counter() - t_w0:.1f}s)",
            flush=True,
        )
    Path(out_path).write_text(json.dumps(results), encoding="utf-8")


def main() -> None:
    t0 = time.perf_counter()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    raw_by_dom = {}
    exemplars = {}
    tasks = []
    for dom in DOMAINS:
        items = load_worfbench_domain_json(dom)
        raw_by_dom[dom] = items
        exemplars[dom] = items[0]
        for it in items[1 : 1 + TASKS_PER_DOMAIN]:
            tasks.append({
                "id": it["id"],
                "domain": dom,
                "sys": it["conversations"][0]["content"],
                "user": it["conversations"][1]["content"],
                "gold_text": it["conversations"][-1]["content"],
                "gold_graph": parse_gold_graph(it["conversations"][-1]["content"]),
            })
    print(f"Loaded {len(tasks)} held-out WorFBench tasks across {DOMAINS}.", flush=True)

    # Step 1: Embed task heads and API descriptions using Qwen3-Embedding-0.6B for embed_top4
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

    # Build all (task_idx, ctx, plan) prompt message lists (96 * 9 = 864 prompt pairs -> 1,728 LLM gens)
    all_jobs: list[tuple[int, str, str, list[dict]]] = []
    task_heads = []
    parsed_apis = []
    for t in tasks:
        head, apis = extract_task_and_apis(t["user"])
        task_heads.append(head)
        parsed_apis.append(apis)

    head_embs = encode_texts(task_heads)
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
                    msgs = [
                        {"role": "system", "content": t["sys"]},
                        {"role": "user", "content": u_txt},
                    ]
                elif p_mode == "step_cot":
                    msgs = [
                        {"role": "system", "content": WORFBENCH_SYSTEM_COT},
                        {"role": "user", "content": u_txt},
                    ]
                else:
                    msgs = [
                        {"role": "system", "content": WORFBENCH_SYSTEM_COT},
                        {"role": "user", "content": f"Example task:\n{ex_user}"},
                        {"role": "assistant", "content": ex_gold},
                        {"role": "user", "content": f"Now plan this task:\n{u_txt}"},
                    ]
                all_jobs.append((t_idx, c_mode, p_mode, msgs))

    del emb_model
    print(
        f"Prepared {len(all_jobs)} prompt jobs ({2 * len(all_jobs)} Qwen3-0.6B generations) "
        f"in {time.perf_counter()-t0:.1f}s.",
        flush=True,
    )

    # Step 2: Batched inference (length-sorted) to minimize DRAM weight reads
    torch.set_num_threads(n_threads)
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
        with torch.no_grad():
            g_out = model.generate(
                **inp, max_new_tokens=68, do_sample=False, stop_strings=["\n\n"], tokenizer=tok
            )
        torch.manual_seed(10007 + start)
        with torch.no_grad():
            s_out = model.generate(
                **inp,
                max_new_tokens=68,
                do_sample=True,
                temperature=0.45,
                top_p=0.85,
                stop_strings=["\n\n"],
                tokenizer=tok,
            )
        for b_idx, (_, t_idx, c_mode, p_mode, _) in enumerate(batch):
            g_txt = tok.decode(g_out[b_idx][in_len:], skip_special_tokens=True)
            s_txt = tok.decode(s_out[b_idx][in_len:], skip_special_tokens=True)
            gen_lookup[(t_idx, c_mode, p_mode)] = {
                "task_idx": t_idx,
                "ctx": c_mode,
                "plan": p_mode,
                "greedy": g_txt,
                "temp_sample": s_txt,
            }
        print(
            f"  [batch {start // bs + 1}/{(len(rendered) + bs - 1) // bs}] "
            f"completed {min(start + bs, len(rendered))}/{len(rendered)} prompt pairs "
            f"(seq_len={in_len}, elapsed={time.perf_counter() - t_gen:.1f}s)",
            flush=True,
        )
    del model
    print(
        f"Finished {2 * len(all_jobs)} Qwen3-0.6B generations in {time.perf_counter()-t_gen:.1f}s!",
        flush=True,
    )

    # Step 3: Score all 81 x 64 (workflow, task) pairs via WorFEval + Qwen3-Embedding-0.6B
    emb_model = transformers.AutoModel.from_pretrained(
        "Qwen/Qwen3-Embedding-0.6B", dtype=torch.float32, local_files_only=local_only
    ).eval()

    # Collect all unique node strings across gold + parsed outputs for batched embedding
    unique_nodes: set[str] = {"START", "END"}
    parsed_cache: dict[tuple[int, str, str, str, str], dict] = {}
    for (t_idx, c_mode, p_mode), rec in gen_lookup.items():
        for d_mode in ("greedy", "temp_sample"):
            txt = rec[d_mode]
            for v_mode in VERIFY_MODES:
                pg = parse_pred_graph(txt, v_mode)
                parsed_cache[(t_idx, c_mode, p_mode, d_mode, v_mode)] = pg
                unique_nodes.update(pg["nodes"])
    for t in tasks:
        unique_nodes.update(t["gold_graph"]["nodes"])

    node_list = sorted(unique_nodes)
    node_vecs = encode_texts(node_list, batch_size=128)
    emb_map = {s: node_vecs[i] for i, s in enumerate(node_list)}

    workflows = list(itertools.product(CONTEXT_MODES, PLAN_MODES, DECODE_MODES, VERIFY_MODES))
    score_matrix = np.zeros((len(workflows), len(tasks)), dtype=np.float32)

    for w_idx, (c_m, p_m, d_m, v_m) in enumerate(workflows):
        for t_idx, t in enumerate(tasks):
            if d_m in ("greedy", "temp_sample"):
                pg = parsed_cache[(t_idx, c_m, p_m, d_m, v_m)]
            else:
                # mbr_select: pick between greedy and temp_sample via task-to-subtask semantic alignment
                pg_g = parsed_cache[(t_idx, c_m, p_m, "greedy", v_m)]
                pg_s = parsed_cache[(t_idx, c_m, p_m, "temp_sample", v_m)]
                def align_score(g_cand):
                    subs = [s for s in g_cand["nodes"] if s not in ("START", "END")]
                    if not subs or not g_cand["edges"]:
                        return -1.0
                    s_mat = np.stack([emb_map[s] for s in subs], axis=0)
                    return float(np.mean(s_mat @ head_embs[t_idx]))
                pg = pg_s if align_score(pg_s) > align_score(pg_g) + 0.01 else pg_g
            score_matrix[w_idx, t_idx] = worfeval_graph_f1(pg, t["gold_graph"], emb_map)

    out_npz = DATA_DIR / "worfbench_qwen3_81x64.npz"
    np.savez_compressed(
        out_npz,
        scores=score_matrix,
        workflows=np.array(["|".join(w) for w in workflows]),
        task_ids=np.array([t["id"] for t in tasks]),
        domains=np.array([t["domain"] for t in tasks]),
    )
    means = score_matrix.mean(axis=1)
    best_i = int(np.argmax(means))
    print(
        f"Saved {out_npz} ({score_matrix.shape}): min mean F1={means.min():.4f}, "
        f"median={np.median(means):.4f}, max={means.max():.4f} ({workflows[best_i]}) "
        f"in {time.perf_counter()-t0:.1f}s!",
        flush=True,
    )


if __name__ == "__main__":
    main()
