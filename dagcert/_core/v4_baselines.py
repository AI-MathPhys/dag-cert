"""v4 ICML Baselines & Harder Zero-Containment SameGame Extensions.

Implements:
1. `CppSameGameRunner` & `FastSameGameProblem` & `samegame_midgame_case`:
   On-demand `-O3 -std=c++17` SameGame playout & reference-mean evaluator enabling
   apples-to-apples certification experiments on large (200--1,600+ vertex) mid-game
   15x15 SameGame DAGs with strictly ZERO root-support containments (`S(b) not subseteq S(a)`),
   as well as 1,099-vertex 6x6 depth-4 boards.
2. External Structured Pure-Exploration Baselines (supporting 2x2 `Sampler x Certificate`
   ablation under matched terminal reward tapes and confidence boxes):
   - `LUCBMicroSession`: Huang, Ajallooeian, Szepesvari, & Muller (ALT 2017) `LUCB-micro`
     with DAG transposition pooling (`stop_rule in {'marginal', 'exact'}`).
   - `UGapEMCTSSession`: Kaufmann & Koolen (NeurIPS 2017) `UGapE-MCTS` recursive
     representative-child descent, in both DAG-pooled (`mode='dag'`) and original
     tree-unrolled (`mode='tree'`) forms (`stop_rule in {'marginal', 'exact'}`).
   - `VarDEDAGSession`: Variance-driven exploration baseline inspired by VarDE (ICML 2026),
     allocating pulls by marginal empirical variance decrement `sigma_hat^2 / (n * (n + 1))`
     under either marginal witnesses (`witness_mode='marginal'`) or exact-regret witnesses
     (`witness_mode='exact'`).
3. `InsideWitnessDAGLUCBSession`: Ablation of `Exact-Regret-DAG-LUCB` comparing
   optimistic (`ucb`: argmax_{z in S(a*)} u_t(z)), lower-bound certificate
   (`lcb`: argmax_{z in S(a*)} l_t(z)), and empirical-mean (`mean`: argmax_{z in S(a*)} mu_hat_t(z))
   inside-support witness selection.
"""
from __future__ import annotations

from collections import deque
import ctypes
import hashlib
import math
from pathlib import Path
import random
import subprocess
import tempfile

from .certified_uct import UCTWork
from .graph import DAG, Problem
from .v2_benchmarks import (
    load_standard_samegame_boards,
    structural_diagnostics,
)
from .v2_monitors import NestedIntervals
from .v3_extensions import (
    WitnessDualCovers,
    WitnessMarginalGraph,
)
from dagcert._core._samegame_engine import Game, Moves


CPP_SG_SOURCE = Path(__file__).resolve().parents[1] / "_native" / "_cpp_samegame.cpp"


class CppSameGameRunner:
    """Compiles `_cpp_samegame.cpp` with a C++17 compiler (`$CXX`, `g++`, or `clang++`) into tempdir and binds ctypes."""

    _lib = None

    @classmethod
    def ensure_loaded(cls):
        if cls._lib is not None:
            return cls._lib
        import os
        import shutil
        import sys

        src_bytes = CPP_SG_SOURCE.read_bytes()
        sha = hashlib.sha256(src_bytes).hexdigest()[:16]
        ext = ".dylib" if sys.platform == "darwin" else ".so"
        so_path = Path(tempfile.gettempdir()) / f"dag_mcts_cpp_samegame_{sha}{ext}"
        if not so_path.is_file():
            cxx = os.environ.get("CXX") or shutil.which("g++") or shutil.which("clang++")
            if not cxx:
                raise RuntimeError(
                    "C++17 compiler not found (tried $CXX, g++, clang++). "
                    "Install g++ or clang++ to build the native SameGame playout kernel."
                )
            tmp_so = so_path.with_name(f"{so_path.stem}_{os.getpid()}.tmp{ext}")
            subprocess.run(
                [
                    cxx, "-O3", "-std=c++17", "-Wall", "-Wextra", "-Werror",
                    "-shared", "-fPIC", str(CPP_SG_SOURCE), "-o", str(tmp_so),
                ],
                check=True,
            )
            tmp_so.replace(so_path)
        lib = ctypes.CDLL(str(so_path))

        lib.cpp_samegame_register_game.argtypes = [
            ctypes.c_int,
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_uint8),
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_uint8),
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_int),
            ctypes.c_int,
            ctypes.c_double,
        ]
        lib.cpp_samegame_register_game.restype = ctypes.c_int

        lib.cpp_samegame_sample_fast.argtypes = [
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_int,
            ctypes.c_uint64,
        ]
        lib.cpp_samegame_sample_fast.restype = ctypes.c_double

        lib.cpp_samegame_batch_means.argtypes = [
            ctypes.c_int,
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_uint8),
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_uint8),
            ctypes.POINTER(ctypes.c_int),
            ctypes.POINTER(ctypes.c_int),
            ctypes.c_int,
            ctypes.c_double,
            ctypes.c_int,
            ctypes.c_uint64,
            ctypes.POINTER(ctypes.c_double),
        ]
        lib.cpp_samegame_batch_means.restype = None

        cls._lib = lib
        return lib


class FastSameGameProblem(Problem):
    """Wraps a SameGame lookahead `Game` with native `-O3` C++17 SplitMix64 playouts."""

    def __init__(self, game: Game, name: str | None = None, ref_samples: int = 8192):
        lib = CppSameGameRunner.ensure_loaded()
        graph = game.graph
        leaves = graph.leaves
        m = len(leaves)

        cell_offsets = [0]
        flat_cells: list[int] = []
        col_offsets = [0]
        col_lens: list[int] = []
        ncols_list: list[int] = []
        points_list: list[int] = []

        for leaf in leaves:
            board, pts, _ = game.states[leaf]
            ncols_list.append(len(board))
            points_list.append(int(pts))
            for col in board:
                col_lens.append(len(col))
                flat_cells.extend(col)
            cell_offsets.append(len(flat_cells))
            col_offsets.append(len(col_lens))

        c_cell_off = (ctypes.c_int * len(cell_offsets))(*cell_offsets)
        c_cells = (ctypes.c_uint8 * max(1, len(flat_cells)))(*(flat_cells if flat_cells else [0]))
        c_col_off = (ctypes.c_int * len(col_offsets))(*col_offsets)
        c_clens = (ctypes.c_uint8 * max(1, len(col_lens)))(*(col_lens if col_lens else [0]))
        c_ncols = (ctypes.c_int * max(1, m))(*(ncols_list if ncols_list else [0]))
        c_pts = (ctypes.c_int * max(1, m))(*(points_list if points_list else [0]))

        inv_scale = 1.0 / float(game.scale)
        self._handle = lib.cpp_samegame_register_game(
            m, c_cell_off, c_cells, c_col_off, c_clens, c_ncols, c_pts, int(game.B), inv_scale
        )
        self._leaf_rank = {leaf: idx for idx, leaf in enumerate(leaves)}
        self._sample_fn = lib.cpp_samegame_sample_fast

        if hasattr(game, "means") and game.means and len(game.means) == m:
            means = dict(game.means)
        else:
            out_means = (ctypes.c_double * m)()
            lib.cpp_samegame_batch_means(
                m, c_cell_off, c_cells, c_col_off, c_clens, c_ncols, c_pts,
                int(game.B), inv_scale, int(ref_samples),
                ctypes.c_uint64(0x20261117A5A5A5A5), out_means,
            )
            means = {leaf: float(out_means[idx]) for idx, leaf in enumerate(leaves)}

        super().__init__(name or getattr(game, "name", "fast_samegame"), graph, means, ())
        self.game = game

    def oracle(self, seed: int):
        prob = self
        s64 = ctypes.c_uint64(seed & 0xFFFFFFFFFFFFFFFF)
        handle = prob._handle
        rank_map = prob._leaf_rank
        sample_fn = prob._sample_fn

        class _FastSGOracle:
            def __init__(self):
                self.obs = [0] * len(prob.graph)
                self.operations = 0

            def sample(self, leaf: int) -> float:
                self.obs[leaf] += 1
                k = self.obs[leaf]
                self.operations += 24
                return float(sample_fn(handle, rank_map[leaf], leaf, k, s64))

        return _FastSGOracle()


def samegame_midgame_case(
    index_1based: int,
    depth: int = 4,
    tile_cap: int = 70,
    eps: float = 0.04,
    ref_samples: int = 8192,
) -> tuple[FastSameGameProblem, float, dict]:
    """Extract canonical mid-game decision state from StandardTestset.txt board `1..20`.

    Uses the exact canonical rollout seed `226000 + index_1based` from `samegame_gate.py`
    and selects the first reachable state with `tiles <= tile_cap` and `>= 4` legal moves.
    """
    boards = load_standard_samegame_boards()
    if not 1 <= index_1based <= len(boards):
        raise ValueError("index_1based must be in 1..20")
    initial = boards[index_1based - 1]
    rng = random.Random(226000 + index_1based)
    mv = Moves()
    board = initial
    cands = []
    while (actions := mv(board)):
        t = sum(map(len, board))
        if 45 <= t <= 95 and len(actions) >= 4:
            cands.append((t, board))
        board = actions[rng.randrange(len(actions))][0]
    if not cands:
        raise ValueError(f"Board {index_1based} had no mid-game state in [45, 95] tiles")
    _, chosen = min(cands, key=lambda item: (abs(item[0] - tile_cap), item[0]))

    game = Game(chosen, depth)
    game.name = f"samegame_mid{tile_cap}_b{index_1based:02d}_d{depth}"
    diag = structural_diagnostics(game.graph)
    diag["tiles"] = sum(map(len, chosen))
    prob = FastSameGameProblem(game, name=game.name, ref_samples=ref_samples)
    return prob, eps, diag


class BoundedNoiseProblem(Problem):
    """Continuous bounded reward problem on [0, 1] with half-width `noise_halfwidth`."""

    def __init__(self, name: str, graph: DAG, means: dict[int, float], noise_halfwidth: float = 0.12):
        super().__init__(name, graph, means, ())
        self.noise_halfwidth = noise_halfwidth

    def oracle(self, seed: int):
        prob = self
        hw = prob.noise_halfwidth
        from .v3_extensions import splitmix_uniform01

        s64 = seed & 0xFFFFFFFFFFFFFFFF

        class _BoundedOracle:
            def __init__(self):
                self.obs = [0] * len(prob.graph)
                self.operations = 0

            def sample(self, leaf: int) -> float:
                self.obs[leaf] += 1
                u = splitmix_uniform01(s64, leaf, self.obs[leaf])
                self.operations += 8
                return min(1.0, max(0.0, prob.means[leaf] + hw * (2.0 * u - 1.0)))

        return _BoundedOracle()


def stochastic_routing_dag(
    scale_w: int = 32,
    k_corridors: int = 12,
    seed: int = 0,
    eps: float = 0.06,
) -> tuple[BoundedNoiseProblem, float, dict]:
    """5-layer multi-hop stochastic transit/routing DAG with strictly ZERO support containment.

    Root chooses among `k_corridors` initial corridors; each corridor connects to 1 exclusive
    regional hub (guaranteeing `S(b) not subseteq S(a)` for all `a != b`) plus a sliding
    geographic neighborhood of shared regional hubs, feeding a layer of transfer stations
    and `6 * scale_w` destination terminals with continuous congestion noise (`+-0.12`).
    """
    if scale_w < k_corridors * 2:
        raise ValueError("scale_w must be >= 2 * k_corridors")
    rng = random.Random(seed * 104729 + scale_w)
    rows: list[tuple[int, ...]] = [()]

    m_leaves = 6 * scale_w
    leaves = list(range(1, m_leaves + 1))
    rows.extend([()] * m_leaves)

    # Layer 2: transfer stations (each serving a local cluster + cross-town links)
    n_stations = 2 * scale_w
    stations: list[int] = []
    exclusives = leaves[:k_corridors * 3]
    shared_pool = leaves[k_corridors * 3:]

    # First `k_corridors` stations are exclusive local terminals for each corridor
    for c in range(k_corridors):
        st = len(rows)
        rows.append(tuple(exclusives[3 * c: 3 * c + 3]))
        stations.append(st)

    # Remaining shared transfer stations connect across `shared_pool`
    n_rem_st = n_stations - k_corridors
    for j in range(n_rem_st):
        base = (j * len(shared_pool)) // n_rem_st
        ch = sorted({shared_pool[(base + off) % len(shared_pool)] for off in (0, 1, 2, 5, 11)})
        st = len(rows)
        rows.append(tuple(ch))
        stations.append(st)

    # Layer 1: regional hubs (`k_corridors` exclusive hubs + `scale_w` shared regional hubs)
    excl_hubs: list[int] = []
    for c in range(k_corridors):
        eh = len(rows)
        rows.append((stations[c],))
        excl_hubs.append(eh)

    shared_st = stations[k_corridors:]
    shared_hubs: list[int] = []
    for h in range(scale_w):
        base = (h * len(shared_st)) // scale_w
        ch = sorted({shared_st[(base + off) % len(shared_st)] for off in (0, 1, 3, 7)})
        rh = len(rows)
        rows.append(tuple(ch))
        shared_hubs.append(rh)

    # Root corridors: 1 exclusive hub + geographic window of `scale_w // 2` shared hubs
    win = scale_w // 2
    actions: list[int] = []
    for c in range(k_corridors):
        start = (c * scale_w) // k_corridors
        hubs_c = [excl_hubs[c]] + [shared_hubs[(start + j) % scale_w] for j in range(win)]
        act = len(rows)
        rows.append(tuple(hubs_c))
        actions.append(act)

    rng.shuffle(actions)
    rows[0] = tuple(actions)
    graph = DAG(rows)

    means: dict[int, float] = {}
    for z in shared_pool:
        means[z] = 0.25 + 0.35 * rng.random()
    # Two central shared destinations have high throughput (0.84, 0.83)
    means[shared_pool[0]] = 0.84
    means[shared_pool[len(shared_pool) // 2]] = 0.83

    # Corridor 0's exclusive destination achieves optimal throughput 0.90;
    # rival corridors' exclusive destinations achieve near-optimal [0.76, 0.80]
    for c in range(k_corridors):
        triple = exclusives[3 * c: 3 * c + 3]
        if c == 0:
            means[triple[0]] = 0.90
            means[triple[1]] = 0.45 + 0.10 * rng.random()
            means[triple[2]] = 0.40 + 0.10 * rng.random()
        else:
            means[triple[0]] = 0.76 + 0.04 * rng.random()
            means[triple[1]] = 0.35 + 0.15 * rng.random()
            means[triple[2]] = 0.30 + 0.15 * rng.random()

    diag = structural_diagnostics(graph)
    assert diag["containment_pairs"] == 0, "stochastic_routing_dag must have 0 containments"
    prob = BoundedNoiseProblem(f"routing_w{scale_w}_s{seed}", graph, means, noise_halfwidth=0.10)
    return prob, eps, diag


def _shortest_leaf_paths(graph: DAG, w: UCTWork) -> dict[int, tuple[int, ...]]:
    parent_step: dict[int, int] = {graph.root: -1}
    q = deque([graph.root])
    while q:
        u = q.popleft()
        w.edge_reads += len(graph.children[u])
        for c in graph.children[u]:
            if c not in parent_step:
                parent_step[c] = u
                q.append(c)
                w.statistic_writes += 1
    paths: dict[int, tuple[int, ...]] = {}
    for z in graph.leaves:
        cur = z
        rev = []
        while cur != -1:
            rev.append(cur)
            cur = parent_step[cur]
        paths[z] = tuple(reversed(rev))
        w.initialization += len(rev)
    return paths


class LUCBMicroSession:
    """Huang, Ajallooeian, Szepesvari, & Muller (ALT 2017) `LUCB-micro` on a DAG.

    - Candidate best arm: `B_t = argmax_a L_t(a)`
    - Marginal challenger: `C_t = argmax_{b != B_t} U_t(b)`
    - Active micro-observables: `z(B_t) = argmax_{z in S(B_t)} u_t(z)`,
      `z(C_t) = argmax_{z in S(C_t)} u_t(z)` (canonical `-z` tie-breaking).
    - Queries whichever of `{z(B_t), z(C_t)}` has larger interval width `u_t(z) - l_t(z)`.
    - Supports `stop_rule='marginal'` (native Huang et al. stopping `U_t(C_t) - L_t(B_t) <= eps`)
      or `stop_rule='exact'` (`min_a R_t(a) <= eps`, isolating certificate vs. sampler gain).
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        delta: float = 0.05,
        schedule: str = "box",
        stop_rule: str = "marginal",
    ):
        if stop_rule not in ("marginal", "exact"):
            raise ValueError(f"Unsupported stop_rule: {stop_rule}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = epsilon
        self.stop_rule = stop_rule
        self.oracle = problem.oracle(seed)
        self.policy_work = UCTWork()
        self.leaf_paths = _shortest_leaf_paths(self.graph, self.policy_work)

        self.monitor = WitnessMarginalGraph(self.graph, delta=delta, schedule=schedule)
        self.exact_stopper = (
            WitnessDualCovers(self.graph, delta=delta, schedule=schedule, layout="best")
            if stop_rule == "exact"
            else None
        )
        self.calls = 0
        self._refresh_state()

    def _refresh_state(self) -> None:
        self.marg_query = self.monitor.query_witness()  # (leader, marg_gap, z_lead, z_chal)
        ev = self.monitor.evidence
        if self.stop_rule == "marginal":
            self.certified = (not ev.conflict) and (self.marg_query[1] <= self.epsilon)
            self.action = self.marg_query[0]
        else:
            assert self.exact_stopper is not None
            eq = self.exact_stopper.query_witness()
            self.certified = (not ev.conflict) and (eq[1] <= self.epsilon)
            self.action = eq[0]

    def step(self) -> tuple[tuple[int, ...], float]:
        if self.certified or self.monitor.evidence.conflict:
            raise RuntimeError("LUCBMicroSession already terminated")
        _, _, z_lead, z_chal = self.marg_query
        ev = self.monitor.evidence
        if z_chal < 0:
            target = z_lead
        else:
            w_l = ev.upper[z_lead] - ev.lower[z_lead]
            w_c = ev.upper[z_chal] - ev.lower[z_chal]
            self.policy_work.query_reads += 4
            self.policy_work.heap_comparisons += 1
            target = z_lead if w_l >= w_c else z_chal

        path = self.leaf_paths[target]
        self.policy_work.edge_reads += len(path) - 1
        reward = self.oracle.sample(target)
        self.calls += 1
        self.policy_work.oracle_calls += 1

        self.monitor.step(target, reward)
        if self.exact_stopper is not None:
            self.exact_stopper.step(target, reward)
        self._refresh_state()
        return path, reward

    @property
    def work(self) -> int:
        extra = self.exact_stopper.work.total - self.calls if self.exact_stopper is not None else 0
        return (
            self.policy_work.total
            + self.monitor.work.total
            + extra
            - self.calls
            + getattr(self.oracle, "operations", 0)
        )


class UGapEMCTSSession:
    """Kaufmann & Koolen (NeurIPS 2017) `UGapE-MCTS` recursive representative-child BAI.

    Supports:
    - `mode='dag'`: Transposition-pooled DAG bounds `[L_t(v), U_t(v)]` with recursive
      optimistic representative-child descent `c_v(t) = argmax_{c in E(v)} U_t(c)`.
    - `mode='tree'`: Original tree-unrolled `UGapE-MCTS` without transposition sharing
      (only valid when total tree paths `<= max_tree_leaves`).
    - `stop_rule in {'marginal', 'exact'}` (on `mode='dag'`).
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        delta: float = 0.05,
        schedule: str = "box",
        mode: str = "dag",
        stop_rule: str = "marginal",
        max_tree_leaves: int = 8192,
    ):
        if mode not in ("dag", "tree"):
            raise ValueError(f"Unsupported mode: {mode}")
        if mode == "tree" and stop_rule != "marginal":
            raise ValueError("Tree-unrolled UGapE-MCTS only supports marginal stopping")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = epsilon
        self.mode = mode
        self.stop_rule = stop_rule
        self.oracle = problem.oracle(seed)
        self.policy_work = UCTWork()
        self.calls = 0

        if mode == "dag":
            self._init_dag(delta, schedule)
        else:
            self._init_tree(delta, schedule, max_tree_leaves)
        self._refresh_state()

    def _init_dag(self, delta: float, schedule: str) -> None:
        g = self.graph
        self.evidence = NestedIntervals(g, self.policy_work, delta=delta, schedule=schedule)
        n = len(g)
        self.lower = [0.0] * n
        self.upper = [1.0] * n
        self.parents: list[list[int]] = [[] for _ in range(n)]
        for u in range(n):
            for c in g.children[u]:
                self.parents[c].append(u)
                self.policy_work.initialization += 1
        self.topo_rank = {v: i for i, v in enumerate(g.order)}
        self.exact_stopper = (
            WitnessDualCovers(g, delta=delta, schedule=schedule, layout="best")
            if self.stop_rule == "exact"
            else None
        )

    def _init_tree(self, delta: float, schedule: str, max_tree_leaves: int) -> None:
        # Unroll DAG into explicit decision tree up to `max_tree_leaves`.
        g = self.graph
        tree_children: list[list[int]] = [[]]
        orig_node: list[int] = [g.root]
        stack = [(0, g.root)]
        leaf_count = 0
        while stack:
            tu, gu = stack.pop()
            ch = g.children[gu]
            if not ch:
                leaf_count += 1
                if leaf_count > max_tree_leaves:
                    raise ValueError(f"Tree unrolling exceeded {max_tree_leaves} leaves")
                continue
            t_ch = []
            for gc in ch:
                tc = len(tree_children)
                tree_children.append([])
                orig_node.append(gc)
                t_ch.append(tc)
                self.policy_work.initialization += 2
            tree_children[tu] = t_ch
            for tc, gc in reversed(list(zip(t_ch, ch))):
                stack.append((tc, gc))

        self.tree_dag = DAG([tuple(row) for row in tree_children], root=0)
        self.tree_orig = orig_node
        self.evidence = NestedIntervals(self.tree_dag, self.policy_work, delta=delta, schedule=schedule)
        nt = len(self.tree_dag)
        self.lower = [0.0] * nt
        self.upper = [1.0] * nt
        self.tree_parent = [-1] * nt
        for u, row in enumerate(self.tree_dag.children):
            for c in row:
                self.tree_parent[c] = u
        self.exact_stopper = None

    def _ugape_root_pair(self, root_children: tuple[int, ...]) -> tuple[int, float, int]:
        k = len(root_children)
        if k == 0:
            return (-1, 0.0, -1)
        if k == 1:
            return (0, 0.0, -1)
        # Compute top-2 upper bounds across root actions in O(K)
        top1_a, top1_u = -1, -math.inf
        top2_a, top2_u = -1, -math.inf
        for a, c in enumerate(root_children):
            u_val = self.upper[c]
            self.policy_work.query_reads += 1
            if u_val > top1_u:
                top2_a, top2_u = top1_a, top1_u
                top1_a, top1_u = a, u_val
            elif u_val > top2_u:
                top2_a, top2_u = a, u_val

        best_j = 0
        best_bgap = math.inf
        for a, c in enumerate(root_children):
            max_other_u = top2_u if a == top1_a else top1_u
            bgap = max(0.0, max_other_u - self.lower[c])
            self.policy_work.query_reads += 2
            if bgap < best_bgap:
                best_bgap = bgap
                best_j = a

        chal_a = top2_a if best_j == top1_a else top1_a
        return (best_j, best_bgap, chal_a)

    def _descend_representative(self, dag_obj: DAG, action_idx: int) -> tuple[int, list[int]]:
        u = dag_obj.children[dag_obj.root][action_idx]
        path = [dag_obj.root, u]
        while dag_obj.children[u]:
            row = dag_obj.children[u]
            best_c = row[0]
            best_u = self.upper[best_c]
            self.policy_work.edge_reads += len(row)
            for c in row[1:]:
                if self.upper[c] > best_u:
                    best_u = self.upper[c]
                    best_c = c
            u = best_c
            path.append(u)
        return u, path

    def _refresh_state(self) -> None:
        dag_obj = self.graph if self.mode == "dag" else self.tree_dag
        self.ugap_pair = self._ugape_root_pair(dag_obj.children[dag_obj.root])
        ev = self.evidence
        if self.stop_rule == "marginal":
            self.certified = (not ev.conflict) and (self.ugap_pair[1] <= self.epsilon)
            self.action = self.ugap_pair[0]
        else:
            assert self.exact_stopper is not None
            eq = self.exact_stopper.query_witness()
            self.certified = (not ev.conflict) and (eq[1] <= self.epsilon)
            self.action = eq[0]

    def _propagate_dag(self, leaf: int, lo: float, hi: float) -> None:
        if lo == self.lower[leaf] and hi == self.upper[leaf]:
            return
        self.lower[leaf] = lo
        self.upper[leaf] = hi
        import heapq

        pq = [(-self.topo_rank[p], p) for p in self.parents[leaf]]
        seen = set(self.parents[leaf])
        heapq.heapify(pq)
        while pq:
            _, u = heapq.heappop(pq)
            row = self.graph.children[u]
            nl = max(self.lower[c] for c in row)
            nu = max(self.upper[c] for c in row)
            self.policy_work.edge_reads += 2 * len(row)
            if nl != self.lower[u] or nu != self.upper[u]:
                self.lower[u] = nl
                self.upper[u] = nu
                self.policy_work.statistic_writes += 2
                for p in self.parents[u]:
                    if p not in seen:
                        seen.add(p)
                        heapq.heappush(pq, (-self.topo_rank[p], p))

    def _propagate_tree(self, tleaf: int, lo: float, hi: float) -> None:
        self.lower[tleaf] = lo
        self.upper[tleaf] = hi
        u = self.tree_parent[tleaf]
        while u != -1:
            row = self.tree_dag.children[u]
            nl = max(self.lower[c] for c in row)
            nu = max(self.upper[c] for c in row)
            self.policy_work.edge_reads += 2 * len(row)
            if nl == self.lower[u] and nu == self.upper[u]:
                break
            self.lower[u] = nl
            self.upper[u] = nu
            self.policy_work.statistic_writes += 2
            u = self.tree_parent[u]

    def step(self) -> tuple[tuple[int, ...], float]:
        if self.certified or self.evidence.conflict:
            raise RuntimeError("UGapEMCTSSession already terminated")
        dag_obj = self.graph if self.mode == "dag" else self.tree_dag
        best_j, _, chal_a = self.ugap_pair
        lj, path_j = self._descend_representative(dag_obj, best_j)
        if chal_a < 0:
            chosen_leaf, chosen_path = lj, path_j
        else:
            lc, path_c = self._descend_representative(dag_obj, chal_a)
            wj = self.upper[lj] - self.lower[lj]
            wc = self.upper[lc] - self.lower[lc]
            self.policy_work.query_reads += 4
            chosen_leaf, chosen_path = (lj, path_j) if wj >= wc else (lc, path_c)

        orig_leaf = chosen_leaf if self.mode == "dag" else self.tree_orig[chosen_leaf]
        orig_path = tuple(chosen_path) if self.mode == "dag" else tuple(self.tree_orig[v] for v in chosen_path)
        reward = self.oracle.sample(orig_leaf)
        self.calls += 1
        self.policy_work.oracle_calls += 1

        iv = self.evidence.observe(chosen_leaf, reward)
        if iv is not None:
            if self.mode == "dag":
                self._propagate_dag(chosen_leaf, *iv)
            else:
                self._propagate_tree(chosen_leaf, *iv)
        if self.exact_stopper is not None:
            self.exact_stopper.step(orig_leaf, reward)
        self._refresh_state()
        return orig_path, reward

    @property
    def work(self) -> int:
        extra = self.exact_stopper.work.total - self.calls if self.exact_stopper is not None else 0
        return self.policy_work.total + extra + getattr(self.oracle, "operations", 0)


class VarDEDAGSession:
    """Variance-driven pure-exploration controller on a DAG (inspired by VarDE, ICML 2026).

    Allocates each sample between the active decision pair `(z_1, z_2)` by maximizing
    the marginal empirical decision-variance decrement `sigma_hat_z^2 / (n_z * (n_z + 1))`
    (prioritizing unvisited `n_z = 0`), under either:
    - `witness_mode='marginal'`: marginal candidate/challenger witnesses + marginal stopping, or
    - `witness_mode='exact'`: exact shared-support witnesses `(z_in, z_out)` + exact stopping.
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        delta: float = 0.05,
        schedule: str = "emp_bernstein",
        witness_mode: str = "marginal",
    ):
        if witness_mode not in ("marginal", "exact"):
            raise ValueError(f"Unsupported witness_mode: {witness_mode}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = epsilon
        self.witness_mode = witness_mode
        self.oracle = problem.oracle(seed)
        self.policy_work = UCTWork()
        self.leaf_paths = _shortest_leaf_paths(self.graph, self.policy_work)

        n = len(self.graph)
        self.n_obs = [0] * n
        self.mean_hat = [0.5] * n
        self.var_sum = [0.25] * n  # weak Beta(1,1)-style variance prior 1/4

        if witness_mode == "marginal":
            self.monitor = WitnessMarginalGraph(self.graph, delta=delta, schedule=schedule)
        else:
            self.monitor = WitnessDualCovers(self.graph, delta=delta, schedule=schedule, layout="best")

        self.calls = 0
        self.query = self.monitor.query_witness()
        self.certified = (not self.monitor.evidence.conflict) and (self.query[1] <= epsilon)
        self.action = self.query[0]

    def _var_decrement_score(self, z: int) -> float:
        cnt = self.n_obs[z]
        self.policy_work.query_reads += 2
        if cnt == 0:
            return math.inf
        sigma2 = self.var_sum[z] / (cnt + 1)
        return sigma2 / (cnt * (cnt + 1))

    def step(self) -> tuple[tuple[int, ...], float]:
        if self.certified or self.monitor.evidence.conflict:
            raise RuntimeError("VarDEDAGSession already terminated")
        _, _, z1, z2 = self.query
        if z2 < 0:
            target = z1
        else:
            s1 = self._var_decrement_score(z1)
            s2 = self._var_decrement_score(z2)
            self.policy_work.heap_comparisons += 1
            target = z1 if s1 >= s2 else z2

        path = self.leaf_paths[target]
        self.policy_work.edge_reads += len(path) - 1
        reward = self.oracle.sample(target)
        self.calls += 1
        self.policy_work.oracle_calls += 1

        # Update online variance tracker
        c_old = self.n_obs[target]
        mu_prev = self.mean_hat[target]
        self.var_sum[target] += (reward - mu_prev) ** 2
        self.n_obs[target] = c_old + 1
        self.mean_hat[target] = (0.5 + c_old * mu_prev + reward) / (c_old + 2)
        self.policy_work.statistic_writes += 3

        self.monitor.step(target, reward)
        self.query = self.monitor.query_witness()
        self.certified = (not self.monitor.evidence.conflict) and (self.query[1] <= self.epsilon)
        self.action = self.query[0]
        return path, reward

    @property
    def work(self) -> int:
        return (
            self.policy_work.total
            + self.monitor.work.total
            - self.calls
            + getattr(self.oracle, "operations", 0)
        )


class InsideWitnessDAGLUCBSession:
    """Ablation of `Exact-Regret-DAG-LUCB` across inside-witness selection rules.

    Compares three choices of `z_t^{in} in S(a*_t)` paired with `z_t^{out} = argmax_{z notin S(a*_t)} u_t(z)`:
    - `inside_mode='ucb'` (Proposed optimistic witness): `argmax_{z in S(a*_t)} (u_t(z), -z)`
    - `inside_mode='lcb'` (Certificate lower-bound witness): `argmax_{z in S(a*_t)} (l_t(z), u_t(z), -z)`
    - `inside_mode='mean'` (Plug-in empirical-mean witness): `argmax_{z in S(a*_t)} (mu_hat_t(z), u_t(z), -z)`
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        inside_mode: str = "ucb",
        delta: float = 0.05,
        schedule: str = "box",
    ):
        if inside_mode not in ("ucb", "lcb", "mean"):
            raise ValueError(f"Unknown inside_mode: {inside_mode}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = epsilon
        self.inside_mode = inside_mode
        self.oracle = problem.oracle(seed)
        self.policy_work = UCTWork()
        self.leaf_paths = _shortest_leaf_paths(self.graph, self.policy_work)
        self.monitor = WitnessDualCovers(self.graph, delta=delta, schedule=schedule, layout="best")

        # Precompute exact reachable leaf sets S(a) for clean LCB/Mean witness lookup
        supports: dict[int, tuple[int, ...]] = {}
        for v in reversed(self.graph.order):
            ch = self.graph.children[v]
            if not ch:
                supports[v] = (v,)
            else:
                merged = sorted({z for c in ch for z in supports[c]})
                supports[v] = tuple(merged)
            self.policy_work.initialization += 1
        self.action_supports = [supports[c] for c in self.graph.children[self.graph.root]]

        n = len(self.graph)
        self.sums = [0.0] * n
        self.counts = [0] * n

        self.calls = 0
        self.query = self.monitor.query_witness()
        self.certified = (not self.monitor.evidence.conflict) and (self.query[1] <= epsilon)
        self.action = self.query[0]

    def _select_inside_witness(self, best_a: int, default_z_in: int) -> int:
        if self.inside_mode == "ucb":
            return default_z_in
        ev = self.monitor.evidence
        sup = self.action_supports[best_a]
        self.policy_work.query_reads += len(sup)
        if self.inside_mode == "lcb":
            return max(sup, key=lambda z: (ev.lower[z], ev.upper[z], -z))
        # inside_mode == "mean" (unvisited leaves default to neutral prior 0.5)
        return max(
            sup,
            key=lambda z: (
                (self.sums[z] / self.counts[z]) if self.counts[z] > 0 else 0.5,
                ev.upper[z],
                -z,
            ),
        )

    def step(self) -> tuple[tuple[int, ...], float]:
        if self.certified or self.monitor.evidence.conflict:
            raise RuntimeError("InsideWitnessDAGLUCBSession already terminated")
        best_a, _, ucb_z_in, z_out = self.query
        z_in = self._select_inside_witness(best_a, ucb_z_in)
        ev = self.monitor.evidence
        if z_out < 0:
            target = z_in
        else:
            w_in = ev.upper[z_in] - ev.lower[z_in]
            w_out = ev.upper[z_out] - ev.lower[z_out]
            self.policy_work.query_reads += 4
            target = z_in if w_in >= w_out else z_out

        path = self.leaf_paths[target]
        self.policy_work.edge_reads += len(path) - 1
        reward = self.oracle.sample(target)
        self.calls += 1
        self.policy_work.oracle_calls += 1
        self.sums[target] += reward
        self.counts[target] += 1

        self.monitor.step(target, reward)
        self.query = self.monitor.query_witness()
        self.certified = (not ev.conflict) and (self.query[1] <= self.epsilon)
        self.action = self.query[0]
        return path, reward

    @property
    def work(self) -> int:
        return (
            self.policy_work.total
            + self.monitor.work.total
            - self.calls
            + getattr(self.oracle, "operations", 0)
        )
