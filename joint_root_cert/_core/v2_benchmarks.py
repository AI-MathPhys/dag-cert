"""Benchmark DAG generators for Exact Regret, PUCT, Depth-3/4 SameGame, and Factorized Selection."""
from __future__ import annotations

from collections import Counter
from functools import lru_cache
import hashlib
from pathlib import Path
import random

from .graph import DAG, Problem
from joint_root_cert._core._samegame_engine import Game, Moves, finish
from joint_root_cert._core._uct_families import binary_root


ROOT = Path(__file__).resolve().parents[1]
STANDARD_SAMEGAME_PATH = Path(__file__).resolve().parents[1] / "benchmarks" / "data" / "samegame" / "StandardTestset.txt"
STANDARD_SAMEGAME_SHA256 = "d20270c2d3ddff9add5d77fa85593574f85de7fbf8b0db0729e6d8c85b2a4d35"


def _join_any(rows: list[tuple[int, ...]], nodes: list[int]) -> int:
    """Join a non-empty list of vertices via a balanced binary tree of MAX gates."""
    if not nodes:
        raise ValueError("Cannot build MAX hub over an empty node list")
    cur = list(nodes)
    while len(cur) > 1:
        nxt: list[int] = []
        for i in range(0, len(cur), 2):
            if i + 1 < len(cur):
                nxt.append(len(rows))
                rows.append((cur[i], cur[i + 1]))
            else:
                nxt.append(cur[i])
        cur = nxt
    return cur[0]


def overlap_dag(m: int, rho: float, gap: float, seed: int,
                noisy: bool = True, block_size: int = 8) -> tuple[Problem, float]:
    """Controlled terminal-support overlap DAG O_{M, rho, g} for Experiment 1.

    - M terminals are partitioned into K = M // block_size blocks of b = block_size leaves
      (keeping per-action private fanout O(1) as M scales across {64, 256, 1024}).
    - Within each block c, s_sh = round(rho * b) leaves belong to a shared subgate under
      a common transposition hub H_sh reachable from EVERY root action, while
      s_priv = b - s_sh leaves belong ONLY to action c's private subgraph.
    - Thus:
      * rho = 0.0 -> completely disjoint supports of size b (no-overlap control).
      * 0 < rho < 1 -> exact fraction round(rho * b) / b of all M terminals are shared
        across all root actions; optimal action a* remains uniquely epsilon-optimal
        with mu_opt + eps < 1.0 (avoiding upper-clipping shortcuts).
      * rho = 1.0 -> identical supports S(a) = Z for all actions.
    """
    if m < block_size or m % block_size != 0:
        raise ValueError(f"m must be a positive multiple of block_size={block_size}")
    if not 0.0 <= rho <= 1.0:
        raise ValueError("rho must lie in [0, 1]")
    if not 0.12 <= gap <= 0.60:
        raise ValueError("gap must lie in [0.12, 0.60]")

    b = block_size
    k_actions = m // b
    s_sh = round(rho * b)
    s_priv = b - s_sh
    rng = random.Random(seed * 1009 + int(round(rho * 1000)) * 37 + m)

    rows: list[tuple[int, ...]] = [()]  # placeholder for root 0
    blocks_sh: list[list[int]] = []
    blocks_priv: list[list[int]] = []
    for _ in range(k_actions):
        sh_leaves = list(range(len(rows), len(rows) + s_sh))
        rows.extend([()] * s_sh)
        priv_leaves = list(range(len(rows), len(rows) + s_priv))
        rows.extend([()] * s_priv)
        blocks_sh.append(sh_leaves)
        blocks_priv.append(priv_leaves)

    shared_hub = None
    if s_sh > 0:
        sh_subgates = []
        for grp in blocks_sh:
            sh_subgates.append(len(rows))
            rows.append(tuple(grp))
        shared_hub = _join_any(rows, sh_subgates)

    action_nodes: list[int] = []
    for c in range(k_actions):
        ch: list[int] = []
        if c == 0 and s_priv >= 1:
            ch.append(blocks_priv[0][0])
            if s_priv > 1:
                pg = len(rows)
                rows.append(tuple(blocks_priv[0][1:]))
                ch.append(pg)
        elif s_priv >= 1:
            pg = len(rows)
            rows.append(tuple(blocks_priv[c]))
            ch.append(pg)
        if shared_hub is not None:
            ch.append(shared_hub)
        aid = len(rows)
        rows.append(tuple(ch))
        action_nodes.append(aid)

    order = list(range(k_actions))
    rng.shuffle(order)
    rows[0] = tuple(action_nodes[c] for c in order)
    graph = DAG(rows)

    # Strict non-clipping regime: mu_opt + eps = 0.87 + 0.10 = 0.97 < 1.00.
    # Shared terminals have mean mu_opt - gap (e.g., gap=0.42 -> 0.45, gap=0.32 -> 0.55),
    # keeping every rival's true regret >= gap > eps = 0.10 so a* is uniquely eps-optimal.
    mu_opt = 0.87
    eps = 0.10
    sh_mean = mu_opt - gap
    priv_mean = 0.06 if gap >= 0.38 else 0.11

    means: dict[int, float] = {}
    for c in range(k_actions):
        for idx, leaf in enumerate(blocks_priv[c]):
            if c == 0 and idx == 0:
                means[leaf] = mu_opt
            elif c == 0:
                means[leaf] = 0.16 + 0.04 * rng.random()
            else:
                means[leaf] = priv_mean + 0.03 * rng.random()
        for leaf in blocks_sh[c]:
            means[leaf] = sh_mean + 0.02 * rng.random()

    det = () if noisy else graph.leaves
    kind = "bernoulli" if noisy else "deterministic"
    return Problem(f"overlap_M{m}_rho{rho:.2f}_g{gap:.2f}_{kind}", graph, means, det), eps


def puct_root_funnel(m: int, seed: int = 0, alpha: float = 0.25,
                     scale: float = 0.25) -> tuple[Problem, float]:
    """Exact deterministic Root-PUCT funnel of Theorem 4.1 / Appendix E (0 < g <= 1/8).

    - Root has 3 actions (A, B, C); A and B are direct terminals with deterministic
      rewards 3/4 and 3/4 - g_m (where g_m = scale * m^{-alpha} <= 1/8 for m >= 16);
      below C is a balanced binary tree of m unary leaves b_1..b_m all pointing to
      shared terminal z with deterministic reward 1/4.
    - Exactly M = 3 distinct terminals.
    """
    if m < 1 or (m & (m - 1)):
        raise ValueError("m must be a power of two >= 1")
    gap = min(0.125, scale * (m ** (-alpha)))
    rows: list[tuple[int, ...]] = [(), (), (), ()]  # 0=root, 1=A, 2=B, 3=z
    means = {1: 0.75, 2: 0.75 - gap, 3: 0.25}
    unary = []
    for _ in range(m):
        unary.append(len(rows))
        rows.append((3,))
    c_node = unary[0] if m == 1 else binary_root(rows, unary)
    actions = [1, 2, c_node]
    if seed:
        random.Random(seed).shuffle(actions)
    rows[0] = tuple(actions)
    graph = DAG(rows)
    return Problem(f"puct_root_funnel_{m}", graph, means, graph.leaves), 0.5 * gap


def puct_noisy_funnel(m: int, seed: int, gap: float = 0.10, noisy: bool = True) -> tuple[Problem, float]:
    """Two-exit multi-level funnel for testing noisy Recursive-PUCT and Protected vs. Decision pruning.

    Each of the m fanout parents below C connects to two low terminals z_1 (0.15) and z_2 (0.28):
    - Protected-Selective retires (b_i, z_1) once u(z_1) < l(z_2) (50% of fanout edges) while keeping C live.
    - Decision-Selective retires root action C once U(C) < max(L(A), L(B)), releasing 100% of C's fanout!
    """
    if m < 2 or (m & (m - 1)):
        raise ValueError("m must be a power of two >= 2")
    rows: list[tuple[int, ...]] = [(), (), (), (), ()]  # 0=root, 1=A, 2=B, 3=z1, 4=z2
    means = {1: 0.82, 2: 0.82 - gap, 3: 0.14, 4: 0.28}
    bottom = []
    for _ in range(m):
        bottom.append(len(rows))
        rows.append((3, 4))
    c_node = binary_root(rows, bottom)
    actions = [1, 2, c_node]
    random.Random(seed).shuffle(actions)
    rows[0] = tuple(actions)
    graph = DAG(rows)
    det = () if noisy else graph.leaves
    return Problem(f"puct_noisy_funnel_{m}", graph, means, det), 0.5 * gap


def contiguous_window_dag(m: int = 256, k_actions: int = 16,
                          seed: int = 0, noisy: bool = True) -> tuple[Problem, float]:
    """Overlapping contiguous-window DAG without intermediate biclique gates (for Experiment 4).

    Each rival root action a connects directly to a contiguous window of m // 2 low-payoff
    shared leaves, while the optimal root action connects to a contiguous window plus one
    exclusive winning leaf. Dyadic covers compress each support and complement into O(log m)
    blocks, whereas gate factorization finds no support-disjoint internal gates.
    """
    if m < 16 or (m & (m - 1)):
        raise ValueError("m must be a power of two >= 16")
    rng = random.Random(seed * 7919 + m)
    rows: list[tuple[int, ...]] = [()]
    leaves = list(range(1, m + 1))
    rows.extend([()] * m)
    win_leaf = len(rows)
    rows.append(())
    span = m // 2
    actions = []
    for a in range(k_actions):
        start = round(a * (m - span) / max(1, k_actions - 1))
        win = (win_leaf, *leaves[start:start + span]) if a == 0 else tuple(leaves[start:start + span])
        aid = len(rows)
        rows.append(win)
        actions.append(aid)
    rng.shuffle(actions)
    rows[0] = tuple(actions)
    graph = DAG(rows)
    means = {leaf: 0.12 + 0.16 * rng.random() for leaf in leaves}
    means[win_leaf] = 0.90
    det = () if noisy else graph.leaves
    return Problem(f"contiguous_window_{m}", graph, means, det), 0.14


def _populate_samegame_means(game: Game) -> None:
    moves = Moves()

    @lru_cache(None)
    def expected(b):
        options = moves(b)
        if not options:
            return float(finish(b))
        return sum(g + expected(nxt) for nxt, g in options) / len(options)

    game.means = {
        j: (score + expected(b) + game.B) / game.scale
        for j in game.graph.leaves
        for b, score, _ in (game.states[j],)
    }
    game.audit_states = len(moves.cache)


def samegame_depth_case(side: int, depth: int, seed: int, eps: float = 0.08) -> tuple[Game, float]:
    """Unselected random 3-color SameGame board with depth-h lookahead DAG."""
    rng = random.Random(seed)
    mv = Moves()
    while True:
        board = tuple(tuple(rng.randrange(3) for _ in range(side)) for _ in range(side))
        if len(mv(board)) >= 2:
            break
    game = Game(board, depth)
    game.name = f"samegame_{side}x{side}_d{depth}"
    _populate_samegame_means(game)
    return game, eps


def load_standard_samegame_boards() -> list[tuple[tuple[int, ...], ...]]:
    raw = STANDARD_SAMEGAME_PATH.read_bytes()
    if hashlib.sha256(raw).hexdigest() != STANDARD_SAMEGAME_SHA256:
        raise ValueError("StandardTestset.txt checksum mismatch")
    rows = [list(map(int, line.split())) for line in raw.decode("utf-8").splitlines() if line.strip()]
    if len(rows) != 300 or any(len(r) != 15 for r in rows):
        raise ValueError("Invalid StandardTestset.txt board dimensions")
    return [tuple(tuple(col) for col in zip(*rows[i:i + 15][::-1])) for i in range(0, 300, 15)]


def samegame_standard_endgame(index_1based: int, depth: int = 3, eps: float = 0.05) -> tuple[Game, float]:
    """Audited endgame position from board `index_1based` (1..20) of StandardTestset.txt."""
    boards = load_standard_samegame_boards()
    if not 1 <= index_1based <= len(boards):
        raise ValueError("index_1based must be in 1..20")
    initial = boards[index_1based - 1]
    rng = random.Random(226000 + index_1based)
    moves = Moves()
    board = initial
    choices = []
    while (actions := moves(board)):
        if len(actions) >= 2:
            choices.append(board)
        board = actions[rng.randrange(len(actions))][0]
    eligible = [b for b in choices if len(moves(b)) >= 3]
    if not eligible:
        raise ValueError(f"Standard board {index_1based} had no >=3-action state")
    chosen = next((b for b in eligible if sum(map(len, b)) <= 36), eligible[-1])
    game = Game(chosen, depth)
    game.name = f"samegame_std{index_1based:02d}_d{depth}"
    _populate_samegame_means(game)
    return game, eps


def structural_diagnostics(graph: DAG) -> dict[str, float | int]:
    """Compute exact DAG transposition, overlap, and support-fragmentation features."""
    paths = [0] * len(graph)
    paths[graph.root] = 1
    for u in graph.order:
        for c in graph.children[u]:
            paths[c] += paths[u]
    tree_leaf_paths = sum(paths[z] for z in graph.leaves)
    tree_nodes = sum(paths)

    supports: dict[int, frozenset[int]] = {}
    for v in reversed(graph.order):
        ch = graph.children[v]
        supports[v] = frozenset((v,)) if not ch else frozenset().union(*(supports[c] for c in ch))
    acts = [supports[a] for a in graph.children[graph.root]]
    k = len(acts)
    m = len(graph.leaves)
    memberships = sum(len(s) for s in acts)

    jaccards = []
    containments = 0
    identical_pairs = 0
    for i in range(k):
        for j in range(k):
            if i == j:
                continue
            if acts[j] <= acts[i]:
                containments += 1
            if i < j:
                if acts[i] == acts[j]:
                    identical_pairs += 1
                union_sz = len(acts[i] | acts[j])
                if union_sz:
                    jaccards.append(len(acts[i] & acts[j]) / union_sz)

    # Fragmentation under ID terminal order: number of maximal contiguous runs across root supports
    leaf_rank = {leaf: idx for idx, leaf in enumerate(graph.leaves)}
    total_runs = 0
    for s in acts:
        idxs = sorted(leaf_rank[z] for z in s)
        runs = 0
        prev = -2
        for x in idxs:
            if x != prev + 1:
                runs += 1
            prev = x
        total_runs += runs

    edges = sum(map(len, graph.children))
    nonroot_in = [len(graph.parents[v]) for v in range(len(graph)) if v != graph.root]
    return {
        "nodes": len(graph),
        "edges": edges,
        "leaves": m,
        "root_actions": k,
        "tree_nodes": tree_nodes,
        "tree_leaf_paths": tree_leaf_paths,
        "leaf_transposition_rate": 1.0 - (m / max(1, tree_leaf_paths)),
        "node_transposition_rate": 1.0 - (len(graph) / max(1, tree_nodes)),
        "mean_membership": memberships / max(1, m),
        "mean_jaccard": sum(jaccards) / max(1, len(jaccards)),
        "containment_pairs": containments,
        "identical_pairs": identical_pairs,
        "root_runs_id": total_runs,
        "runs_per_edge": total_runs / max(1, edges),
        "mean_fanin": sum(nonroot_in) / max(1, len(nonroot_in)),
    }
