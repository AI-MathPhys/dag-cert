"""v6 Real-World Shared-Support Certification Benchmarks & Flat-LUCB Control.

Implements two real-world all-MAX (`V(a) = max_{z in S(a)} mu_z`) benchmarks with
strictly zero root-support containments (`S(b) not subseteq S(a)` for all `a != b`),
paired with a `FlatLUCBSession` best-arm identification control over `Z`:

1. `FlatLUCBSession`:
   Flat best-arm identification (`LUCB1`, Kalyanakrishnan et al. 2012) over the
   `M` canonical terminal designs `Z` using the exact same `NestedIntervals`
   terminal confidence box `[l_t(z), u_t(z)]` as the DAG-aware methods. Stops when
   `max_{z != z_hat_t} u_t(z) - l_t(z_hat_t) <= eps` and recommends the canonical
   root action `min {a : z_hat_t in S(a)}`.

2. `GB1MutationCampaignProblem`:
   Multi-round combinatorial site-directed mutagenesis library commitment on the
   experimentally measured 4-site Protein G domain B1 (`GB1`: V39, D40, G41, V54)
   IgG-Fc binding fitness landscape of Wu et al. (*eLife* 2016, `149,361` measured
   variants). Root actions commit to a Round-1 single-site anchor mutation
   `a = (site, aa)` from starting variant `start_seq`, followed by up to
   `max_edits - 1` substitutions at distinct remaining sites. Commutativity of
   mutations at distinct positions merges paths onto canonical protein sequences
   `z`, while each anchor's 1-point mutant belongs uniquely to `S(a)` (guaranteeing
   zero support containments). Observations draw unbiased, sequencing-depth-calibrated
   retrospective assay replicates in `[0, 1]` around `mu_z = Fitness_z / 10.0`.

3. `WorFBenchWorkflowProblem`:
   Behaviorally exact multi-stage LLM agent tool-workflow commitment over `81 = 3^4`
   canonical 4-stage `Qwen3-0.6B` + `Qwen3-Embedding-0.6B` workflows evaluated on
   held-out `WorFBench` (*ICLR 2025*) graph-planning tasks (`ToolBench`, `ToolAlpaca`,
   `Seal-Tools`, `WebShop`) with the official `WorFEval` subgraph-matching F1 metric.
   Root actions commit to an initial stage module upgrade `a = (stage, module)` from a
   baseline workflow `base_config`, followed by up to `max_upgrades - 1` upgrades on
   remaining stages. Terminal `z` is a complete canonical 4-stage workflow whose
   behavior depends solely on its 4 module settings; each sample draws an i.i.d.
   held-out task and returns its real `WorFEval` F1 score in `[0, 1]`.
"""
from __future__ import annotations

from functools import lru_cache
import math
from pathlib import Path

import numpy as np

from .certified_uct import UCTWork
from .graph import DAG, Problem
from .v2_benchmarks import structural_diagnostics
from .v2_monitors import NestedIntervals
from .v3_extensions import WitnessMaxHeap, splitmix_uniform01
from .v4_baselines import _shortest_leaf_paths
from .v5_hybrid_and_os import DualWitnessCovers


DATA_DIR = Path(__file__).resolve().parents[1] / "benchmarks" / "data"
GB1_NPZ_PATH = DATA_DIR / "gb1_wu2016_measured.npz"
TRPB_NPZ_PATH = DATA_DIR / "trpb_johnston2024_measured.npz"
WORFBENCH_NPZ_PATH = DATA_DIR / "worfbench_qwen3_81x64.npz"
WORFBENCH_TEST_NPZ_PATH = DATA_DIR / "worfbench_qwen3_test_81x32.npz"

GB1_FITNESS_MAX = 8.761966133117676  # Global max measured GB1 fitness (`FWAA`) in Wu et al. (2016)
GB1_ASSAY_OFFSET = 0.10              # Baseline nonspecific assay readout in [0, 1]
GB1_ASSAY_SPAN = 0.80                # Linear assay span: mu_z = 0.10 + 0.80 * (Fitness_z / F_max) in [0.10, 0.90]
GB1_SITES = ("V39", "D40", "G41", "V54")
GB1_PANELS: dict[str, tuple[str, ...]] = {
    "panel4": ("A", "G", "W", "Y"),
    "panel5": ("A", "C", "G", "W", "Y"),
    "panel6": ("A", "C", "F", "G", "W", "Y"),
    "panel8": ("A", "C", "F", "G", "L", "V", "W", "Y"),
    "panel12": ("A", "C", "F", "G", "I", "L", "M", "S", "T", "V", "W", "Y"),
    "panel16": ("A", "C", "D", "E", "F", "G", "H", "I", "L", "M", "N", "Q", "S", "T", "V", "W"),
    "full20": tuple("ACDEFGHIKLMNPQRSTVWY"),
}


TRPB_FITNESS_MAX = 1.0               # Max-normalized fitness (`AIKG` = 1.0, parent `VFVS` = 0.4081) in Johnston et al. (2024)
TRPB_SITES = ("V183", "F184", "V227", "S228")
TRPB_PANELS: dict[str, tuple[str, ...]] = {
    "panel5": ("A", "G", "I", "K", "L"),
    "panel6": ("A", "C", "G", "I", "K", "L"),
    "panel8": ("A", "C", "G", "I", "K", "L", "S", "V"),
    "full20": tuple("ACDEFGHIKLMNPQRSTVWY"),
}


def gb1_mean_to_raw_fitness(mu: float, fitness_max: float = GB1_FITNESS_MAX) -> float:
    """Invert `mu_z = 0.10 + 0.80 * (Fitness_z / F_max)` back to measured fitness."""
    return max(0.0, (mu - GB1_ASSAY_OFFSET) / GB1_ASSAY_SPAN * fitness_max)

WORFBENCH_STAGES = ("Context", "Planner", "Decoder", "Verifier")
WORFBENCH_MODULES = (
    ("raw_schema", "compact_sig", "embed_top4"),
    ("zero_shot", "step_cot", "one_shot"),
    ("greedy", "temp_sample", "mbr_select"),
    ("raw_parse", "norm_endpts", "dag_repair"),
)


class _FlatLeaderHeap:
    """Indexed max-heap over `0..M-1` ordered by `(lo[j], hi[j], -orig_leaf[j])`."""

    def __init__(self, lo: list[float], hi: list[float], orig_leaves: list[int], work: UCTWork):
        self.lo = list(lo)
        self.hi = list(hi)
        self.orig_leaves = list(orig_leaves)
        n = len(self.lo)
        self.ids = list(range(n))
        self.positions = list(range(n))
        self.work = work
        work.initialization += 5 * n
        for i in reversed(range(n // 2)):
            self._down(i)

    def _better(self, a: int, b: int) -> bool:
        self.work.heap_comparisons += 1
        return (self.lo[a], self.hi[a], -self.orig_leaves[a]) > (
            self.lo[b],
            self.hi[b],
            -self.orig_leaves[b],
        )

    def _swap(self, i: int, j: int) -> None:
        a, b = self.ids[i], self.ids[j]
        self.ids[i], self.ids[j] = b, a
        self.positions[a], self.positions[b] = j, i
        self.work.heap_writes += 4

    def _down(self, i: int) -> None:
        size = len(self.ids)
        while 2 * i + 1 < size:
            ch = 2 * i + 1
            if ch + 1 < size and self._better(self.ids[ch + 1], self.ids[ch]):
                ch += 1
            if not self._better(self.ids[ch], self.ids[i]):
                break
            self._swap(i, ch)
            i = ch

    def update(self, item: int, lo_val: float, hi_val: float) -> None:
        old_key = (self.lo[item], self.hi[item], -self.orig_leaves[item])
        new_key = (lo_val, hi_val, -self.orig_leaves[item])
        if new_key == old_key:
            return
        self.lo[item] = lo_val
        self.hi[item] = hi_val
        self.work.heap_writes += 2
        pos = self.positions[item]
        if new_key > old_key:
            while pos and self._better(item, self.ids[(pos - 1) // 2]):
                par = (pos - 1) // 2
                self._swap(pos, par)
                pos = par
        else:
            self._down(pos)

    @property
    def top(self) -> int:
        return self.ids[0]


class FlatLUCBSession:
    """Flat Best-Arm Identification (`LUCB1`) over terminal leaves `Z`.

    Supports two stopping rules under identical terminal-level sampling:
    - `stop_rule='terminal'` (default): standard flat BAI stopping
      `max_{z != z_hat_t} u_t(z) - l_t(z_hat_t) <= eps`, recommending
      `min {a : z_hat_t in S(a)}`.
    - `stop_rule='root_exact'` (`Flat-LUCB + Root Certificate`): keeps the exact
      same terminal-level `Flat-LUCB` sample allocation over `Z`, but stops as soon
      as exact root-level regret satisfies `min_{a in A} R_t(a) <= eps` (via
      `DualWitnessCovers`), isolating decision abstraction from graph-aware witness
      allocation.
    """

    def __init__(
        self,
        problem: Problem,
        seed: int,
        epsilon: float,
        delta: float = 0.05,
        schedule: str = "box",
        stop_rule: str = "terminal",
    ):
        if stop_rule not in ("terminal", "root_exact"):
            raise ValueError(f"Unsupported FlatLUCBSession stop_rule: {stop_rule!r}")
        self.problem = problem
        self.graph = problem.graph
        self.epsilon = epsilon
        self.stop_rule = stop_rule
        self.oracle = problem.oracle(seed)
        self.policy_work = w = UCTWork()
        self.evidence = NestedIntervals(self.graph, w, delta=delta, schedule=schedule)
        self.root_stopper = (
            DualWitnessCovers(self.graph, delta=delta, schedule=schedule, layout="best")
            if stop_rule == "root_exact"
            else None
        )
        self.leaf_paths = _shortest_leaf_paths(self.graph, w)

        self.leaves = list(self.graph.leaves)
        self.leaf_to_idx = {z: j for j, z in enumerate(self.leaves)}
        m = len(self.leaves)

        # Map each terminal leaf z to the lowest-index root action a whose support contains z
        root_ch = self.graph.children[self.graph.root]
        reach_sets: list[set[int]] = [set() for _ in range(len(self.graph))]
        for v in reversed(self.graph.order):
            ch = self.graph.children[v]
            w.edge_reads += len(ch)
            if not ch:
                reach_sets[v].add(v)
            else:
                for c in ch:
                    reach_sets[v].update(reach_sets[c])
        self.leaf_first_action: dict[int, int] = {}
        for a_idx, c in enumerate(root_ch):
            for z in reach_sets[c]:
                if z not in self.leaf_first_action:
                    self.leaf_first_action[z] = a_idx
                    w.initialization += 1

        self.lead_heap = _FlatLeaderHeap([0.0] * m, [1.0] * m, self.leaves, w)
        self.upper_heap = WitnessMaxHeap([1.0] * m, self.leaves, w)
        self.calls = 0
        self._refresh()

    def _refresh(self) -> None:
        lead_j = self.lead_heap.top
        z_lead = self.leaves[lead_j]
        top_u_j = self.upper_heap.top
        if top_u_j != lead_j:
            chal_j = top_u_j
        else:
            chal_j = self.upper_heap.second()

        self.policy_work.query_reads += 3
        if chal_j is None:
            gap = 0.0
            z_chal = -1
        else:
            z_chal = self.leaves[chal_j]
            gap = max(0.0, self.evidence.upper[z_chal] - self.evidence.lower[z_lead])
        self._state = (z_lead, z_chal, gap)
        self.recommended_leaf = z_lead
        if self.root_stopper is None:
            self.action = self.leaf_first_action[z_lead]
            self.certified = (not self.evidence.conflict) and (gap <= self.epsilon)
        else:
            a_stop, reg, _, _, _ = self.root_stopper.query_dual_witness()
            self.action = a_stop
            self.certified = (not self.evidence.conflict) and (reg <= self.epsilon)

    def step(self) -> tuple[tuple[int, ...], float]:
        if self.certified or self.evidence.conflict:
            raise RuntimeError("FlatLUCBSession already terminated")
        z_lead, z_chal, _ = self._state
        if z_chal < 0:
            target = z_lead
        else:
            w_l = self.evidence.upper[z_lead] - self.evidence.lower[z_lead]
            w_c = self.evidence.upper[z_chal] - self.evidence.lower[z_chal]
            self.policy_work.query_reads += 4
            self.policy_work.heap_comparisons += 1
            target = z_lead if w_l >= w_c else z_chal

        path = self.leaf_paths[target]
        self.policy_work.edge_reads += len(path) - 1
        reward = self.oracle.sample(target)
        self.calls += 1
        self.policy_work.oracle_calls += 1

        iv = self.evidence.observe(target, reward)
        if iv is not None:
            j = self.leaf_to_idx[target]
            lo, hi = iv
            self.lead_heap.update(j, lo, hi)
            self.upper_heap.update(j, hi, target)
        if self.root_stopper is not None:
            self.root_stopper.step(target, reward)
        self._refresh()
        return path, reward

    @property
    def work(self) -> int:
        extra = self.root_stopper.work.total - self.calls if self.root_stopper is not None else 0
        return self.policy_work.total - self.calls + extra + getattr(self.oracle, "operations", 0)


@lru_cache(maxsize=1)
def _load_gb1_table() -> dict[str, tuple[float, int, int]]:
    if not GB1_NPZ_PATH.is_file():
        raise FileNotFoundError(
            f"Missing GB1 dataset {GB1_NPZ_PATH}; run `paper/build_gb1_dataset.py` first."
        )
    data = np.load(GB1_NPZ_PATH)
    variants = data["variants"]
    fitness = data["fitness"]
    count_in = data["count_in"]
    count_sel = data["count_sel"]
    return {
        str(variants[i]): (float(fitness[i]), int(count_in[i]), int(count_sel[i]))
        for i in range(len(variants))
    }


@lru_cache(maxsize=1)
def _load_trpb_table() -> dict[str, tuple[float, int, int]]:
    if not TRPB_NPZ_PATH.is_file():
        raise FileNotFoundError(
            f"Missing TrpB dataset {TRPB_NPZ_PATH}; run `paper/build_trpb_dataset.py` first."
        )
    data = np.load(TRPB_NPZ_PATH)
    variants = data["variants"]
    fitness = data["fitness"]
    return {str(variants[i]): (float(fitness[i]), 100, 100) for i in range(len(variants))}


@lru_cache(maxsize=4)
def _load_worfbench_archive(path_str: str | None = None) -> dict[str, np.ndarray]:
    target = Path(path_str) if path_str is not None else WORFBENCH_NPZ_PATH
    if not target.is_file():
        raise FileNotFoundError(
            f"Missing WorFBench archive {target}; "
            "run `paper/build_worfbench_llm_matrix.py` first."
        )
    data = np.load(target)
    return {k: data[k] for k in data.files}


def _apply_edits(base_seq: str, edits: tuple[tuple[int, str], ...]) -> str:
    chars = list(base_seq)
    for pos, aa in edits:
        chars[pos] = aa
    return "".join(chars)


class GB1MutationCampaignProblem(Problem):
    """Combinatorial site-directed mutagenesis DAG on measured 4-site protein fitnesses.

    Supports three retrospective observation models sharing the exact same mean `mu_z`:
    - `'calibrated'` (default): sequencing-depth-calibrated bounded assay replicates
    - `'bernoulli'`: pure binary `Bernoulli(mu_z)` draws (zero count dependence)
    - `'low_var_uniform'`: constant-variance symmetric `Uniform(mu_z - 0.08, mu_z + 0.08)`
    """

    VALID_NOISE_MODELS = ("calibrated", "bernoulli", "low_var_uniform")

    def __init__(
        self,
        start_seq: str = "FDGV",
        max_edits: int = 3,
        panel: str | tuple[str, ...] = "full20",
        noise_scale: float = 1.0,
        noise_model: str = "calibrated",
        name: str | None = None,
        *,
        _landscape: str = "gb1",
    ):
        if len(start_seq) != 4:
            raise ValueError("start_seq must be a 4-letter sequence")
        if max_edits not in (2, 3, 4):
            raise ValueError("max_edits must lie in {2, 3, 4}")
        if noise_model not in self.VALID_NOISE_MODELS:
            raise ValueError(f"Unknown noise_model {noise_model!r}; expected {self.VALID_NOISE_MODELS}")

        if _landscape == "gb1":
            panels_dict = GB1_PANELS
            sites = GB1_SITES
            fit_max = GB1_FITNESS_MAX
            table = _load_gb1_table()
        elif _landscape == "trpb":
            panels_dict = TRPB_PANELS
            sites = TRPB_SITES
            fit_max = TRPB_FITNESS_MAX
            table = _load_trpb_table()
        else:
            raise ValueError(f"Unknown protein landscape {_landscape!r}")

        aa_panel = panels_dict[panel] if isinstance(panel, str) else tuple(panel)
        panel_tag = panel if isinstance(panel, str) else f"custom{len(aa_panel)}"

        # Step 1: Valid Round-1 anchor substitutions a = (pos, aa) whose 1-mutant is measured
        anchors: list[tuple[int, str, str]] = []
        for pos in range(4):
            wt_aa = start_seq[pos]
            for aa in aa_panel:
                if aa == wt_aa:
                    continue
                seq1 = _apply_edits(start_seq, ((pos, aa),))
                if seq1 in table:
                    anchors.append((pos, aa, seq1))
        if len(anchors) < 2:
            raise ValueError(f"Starting sequence {start_seq!r} has fewer than 2 measured 1-mutants")

        # Build canonical multi-edit intermediate states and measured stop-leaves
        # Node 0 = root
        # Nodes 1..K = Round-1 committed anchor nodes
        # Intermediate k-edit nodes (2 <= k <= max_edits): canonical sorted tuple of (pos, aa)
        # Stop-leaves: canonical 4-letter sequence strings
        combo_children_edits: dict[tuple[tuple[int, str], ...], list[tuple[tuple[int, str], ...]]] = {}
        combo_seq: dict[tuple[tuple[int, str], ...], str] = {}

        def ensure_combo(edits: tuple[tuple[int, str], ...]) -> bool:
            """Return True iff `edits` or one of its deeper descendants is measured in GB1."""
            if edits in combo_seq:
                return combo_seq[edits] != ""
            seq = _apply_edits(start_seq, edits)
            used_pos = {p for p, _ in edits}
            sub_valid: list[tuple[tuple[int, str], ...]] = []
            if len(edits) < max_edits:
                for p in range(4):
                    if p in used_pos:
                        continue
                    wt_aa = start_seq[p]
                    for aa in aa_panel:
                        if aa == wt_aa:
                            continue
                        nxt = tuple(sorted(edits + ((p, aa),)))
                        if ensure_combo(nxt):
                            sub_valid.append(nxt)
            has_any = (seq in table) or bool(sub_valid)
            combo_seq[edits] = seq if has_any else ""
            if has_any:
                # Deduplicate preserving order
                combo_children_edits[edits] = list(dict.fromkeys(sub_valid))
            return has_any

        anchor_next: list[list[tuple[tuple[int, str], ...]]] = []
        measured_seqs: set[str] = set()
        for pos, aa, seq1 in anchors:
            measured_seqs.add(seq1)
            subs: list[tuple[tuple[int, str], ...]] = []
            for p2 in range(4):
                if p2 == pos:
                    continue
                wt2 = start_seq[p2]
                for aa2 in aa_panel:
                    if aa2 == wt2:
                        continue
                    edits2 = tuple(sorted(((pos, aa), (p2, aa2))))
                    if ensure_combo(edits2):
                        subs.append(edits2)
            anchor_next.append(list(dict.fromkeys(subs)))

        for edits, seq in combo_seq.items():
            if seq and seq in table:
                measured_seqs.add(seq)

        # Assign vertex IDs
        rows: list[tuple[int, ...]] = [()]
        labels: list[str] = [f"start:{start_seq}"]

        action_ids: list[int] = []
        action_labels: list[str] = []
        for pos, aa, _ in anchors:
            aid = len(rows)
            rows.append(())
            lbl = f"{start_seq[pos]}{pos + 1}{aa} ({sites[pos]})"
            labels.append(lbl)
            action_ids.append(aid)
            action_labels.append(f"{start_seq[pos]}{sites[pos][1:]}{aa}")
        rows[0] = tuple(action_ids)

        valid_combos = sorted(
            [ed for ed, sq in combo_seq.items() if sq],
            key=lambda ed: (len(ed), ed),
        )
        combo_id: dict[tuple[tuple[int, str], ...], int] = {}
        for ed in valid_combos:
            cid = len(rows)
            combo_id[ed] = cid
            rows.append(())
            labels.append("+".join(f"{start_seq[p]}{p + 1}{a}" for p, a in ed))

        sorted_seqs = sorted(measured_seqs)
        leaf_id: dict[str, int] = {}
        means: dict[int, float] = {}
        raw_fitness: dict[int, float] = {}
        read_counts: dict[int, int] = {}
        variant_of_leaf: dict[int, str] = {}
        hamming_of_leaf: dict[int, int] = {}

        for seq in sorted_seqs:
            lid = len(rows)
            leaf_id[seq] = lid
            rows.append(())
            labels.append(f"seq:{seq}")
            fit, c_in, c_sel = table[seq]
            raw_fitness[lid] = fit
            means[lid] = min(
                0.90,
                max(
                    GB1_ASSAY_OFFSET,
                    GB1_ASSAY_OFFSET + GB1_ASSAY_SPAN * (fit / fit_max),
                ),
            )
            read_counts[lid] = max(1, c_in + c_sel)
            variant_of_leaf[lid] = seq
            hamming_of_leaf[lid] = sum(1 for i in range(4) if seq[i] != start_seq[i])

        for idx, (_, _, seq1) in enumerate(anchors):
            aid = action_ids[idx]
            ch = [leaf_id[seq1]] + [combo_id[ed] for ed in anchor_next[idx]]
            rows[aid] = tuple(ch)

        for ed in valid_combos:
            cid = combo_id[ed]
            seq = combo_seq[ed]
            ch = []
            if seq in leaf_id:
                ch.append(leaf_id[seq])
            ch.extend(combo_id[nxt] for nxt in combo_children_edits[ed])
            rows[cid] = tuple(ch)

        graph = DAG(rows, root=0, labels=labels)
        suffix = "" if noise_model == "calibrated" else f"_{noise_model}"
        prob_name = name or f"{_landscape}_{start_seq}_d{max_edits}_{panel_tag}{suffix}"
        super().__init__(prob_name, graph, means, ())

        self.landscape = _landscape
        self.fitness_max = fit_max
        self.start_seq = start_seq
        self.start_raw_fitness = table[start_seq][0] if start_seq in table else float("nan")
        self.max_edits = max_edits
        self.panel_name = panel_tag
        self.noise_scale = float(noise_scale)
        self.noise_model = noise_model
        self.action_labels = tuple(action_labels)
        self.raw_fitness = raw_fitness
        self.read_counts = read_counts
        self.variant_of_leaf = variant_of_leaf
        self.hamming_of_leaf = hamming_of_leaf

        # Precompute per-leaf unbiased assay noise parameters `(lam_z, hw_z)`:
        # X = (1 - lam_z) * (mu_z + hw_z * (2*U_2 - 1)) + lam_z * 1[U_1 < mu_z]
        # Exact E[X] = mu_z for every mu_z in [0, 1].
        self._lam: dict[int, float] = {}
        self._hw: dict[int, float] = {}
        for lid, mu in means.items():
            if noise_model == "bernoulli":
                self._lam[lid] = 1.0
                self._hw[lid] = 0.0
            elif noise_model == "low_var_uniform":
                self._lam[lid] = 0.0
                self._hw[lid] = min(0.08 * self.noise_scale, mu, 1.0 - mu)
            else:
                cnt = read_counts[lid]
                lam = min(0.65, self.noise_scale * (0.38 + 1.5 / math.sqrt(cnt + 4.0)))
                hw_raw = self.noise_scale * (0.10 + 0.20 / math.sqrt(cnt + 9.0))
                self._lam[lid] = lam
                self._hw[lid] = min(hw_raw, mu, 1.0 - mu)

    def oracle(self, seed: int):
        prob = self
        s64 = seed & 0xFFFFFFFFFFFFFFFF
        means = prob.means
        lam_map = prob._lam
        hw_map = prob._hw

        class _GB1AssayOracle:
            def __init__(self):
                self.obs = [0] * len(prob.graph)
                self.operations = 0

            def sample(self, leaf: int) -> float:
                self.obs[leaf] += 1
                k = self.obs[leaf]
                self.operations += 8
                mu = means[leaf]
                if prob.noise_scale <= 0.0:
                    return mu
                u1 = splitmix_uniform01(s64, leaf, 2 * k - 1)
                u2 = splitmix_uniform01(s64, leaf, 2 * k)
                lam = lam_map[leaf]
                hw = hw_map[leaf]
                y_sym = mu + hw * (2.0 * u2 - 1.0)
                bern = 1.0 if u1 < mu else 0.0
                return (1.0 - lam) * y_sym + lam * bern

        return _GB1AssayOracle()


class TrpBMutationCampaignProblem(GB1MutationCampaignProblem):
    """Combinatorial active-site mutagenesis DAG on measured 4-site TmTrpB fitnesses
    (Johnston et al., *PNAS* 2024; 159,129 stop-free variants across V183, F184, V227, S228).

    Uses the exact same graph-construction and observation-model code as `GB1MutationCampaignProblem`.
    """

    def __init__(
        self,
        start_seq: str = "VFVS",
        max_edits: int = 3,
        panel: str | tuple[str, ...] = "panel5",
        noise_scale: float = 1.0,
        noise_model: str = "low_var_uniform",
        name: str | None = None,
    ):
        super().__init__(
            start_seq=start_seq,
            max_edits=max_edits,
            panel=panel,
            noise_scale=noise_scale,
            noise_model=noise_model,
            name=name,
            _landscape="trpb",
        )


class WorFBenchWorkflowProblem(Problem):
    """Behaviorally exact 4-stage `Qwen3-0.6B` agentic workflow DAG on `WorFBench`."""

    def __init__(
        self,
        domain: str = "all",
        base_config: tuple[int, int, int, int] = (0, 0, 0, 0),
        max_upgrades: int = 3,
        name: str | None = None,
        archive_path: Path | None = None,
    ):
        if len(base_config) != 4 or any(c not in (0, 1, 2) for c in base_config):
            raise ValueError("base_config must be a 4-tuple of module indices in {0, 1, 2}")
        if max_upgrades not in (1, 2, 3, 4):
            raise ValueError("max_upgrades must lie in {1, 2, 3, 4}")

        archive = _load_worfbench_archive(str(archive_path) if archive_path is not None else None)
        all_scores = archive["scores"]  # (81, 96) float32
        all_domains = [str(d) for d in archive["domains"]]
        workflows = [str(w) for w in archive["workflows"]]

        if domain == "all":
            col_idx = np.arange(all_scores.shape[1], dtype=np.int64)
        else:
            col_idx = np.array(
                [j for j, d in enumerate(all_domains) if d == domain],
                dtype=np.int64,
            )
            if len(col_idx) == 0:
                raise ValueError(f"Unknown WorFBench domain {domain!r}")

        dom_scores = np.ascontiguousarray(all_scores[:, col_idx], dtype=np.float64)
        n_tasks = int(dom_scores.shape[1])

        def cfg_to_widx(cfg: tuple[int, int, int, int]) -> int:
            return ((cfg[0] * 3 + cfg[1]) * 3 + cfg[2]) * 3 + cfg[3]

        def apply_up(edits: tuple[tuple[int, int], ...]) -> tuple[int, int, int, int]:
            out = list(base_config)
            for stg, mod in edits:
                out[stg] = mod
            return (out[0], out[1], out[2], out[3])

        # Round-1 committed stage upgrades: 4 stages x 2 non-base modules = 8 root actions
        anchors: list[tuple[int, int, tuple[int, int, int, int]]] = []
        for stg in range(4):
            for mod in range(3):
                if mod != base_config[stg]:
                    anchors.append((stg, mod, apply_up(((stg, mod),))))

        combo_children: dict[tuple[tuple[int, int], ...], list[tuple[tuple[int, int], ...]]] = {}

        def build_combo(edits: tuple[tuple[int, int], ...]) -> None:
            if edits in combo_children:
                return
            used = {s for s, _ in edits}
            subs: list[tuple[tuple[int, int], ...]] = []
            if len(edits) < max_upgrades:
                for s in range(4):
                    if s in used:
                        continue
                    for m in range(3):
                        if m == base_config[s]:
                            continue
                        nxt = tuple(sorted(edits + ((s, m),)))
                        build_combo(nxt)
                        subs.append(nxt)
            combo_children[edits] = list(dict.fromkeys(subs))

        anchor_subs: list[list[tuple[tuple[int, int], ...]]] = []
        reachable_cfgs: set[tuple[int, int, int, int]] = set()
        for stg, mod, cfg1 in anchors:
            reachable_cfgs.add(cfg1)
            subs = []
            if max_upgrades >= 2:
                for s2 in range(4):
                    if s2 == stg:
                        continue
                    for m2 in range(3):
                        if m2 == base_config[s2]:
                            continue
                        ed2 = tuple(sorted(((stg, mod), (s2, m2))))
                        build_combo(ed2)
                        subs.append(ed2)
            anchor_subs.append(list(dict.fromkeys(subs)))

        for ed in combo_children:
            reachable_cfgs.add(apply_up(ed))

        rows: list[tuple[int, ...]] = [()]
        base_str = "|".join(WORFBENCH_MODULES[s][base_config[s]] for s in range(4))
        labels: list[str] = [f"base:{base_str}"]

        action_ids: list[int] = []
        action_labels: list[str] = []
        for stg, mod, _ in anchors:
            aid = len(rows)
            rows.append(())
            lbl = f"{WORFBENCH_STAGES[stg]}->{WORFBENCH_MODULES[stg][mod]}"
            labels.append(lbl)
            action_ids.append(aid)
            action_labels.append(lbl)
        rows[0] = tuple(action_ids)

        sorted_combos = sorted(combo_children.keys(), key=lambda ed: (len(ed), ed))
        combo_id: dict[tuple[tuple[int, int], ...], int] = {}
        for ed in sorted_combos:
            cid = len(rows)
            combo_id[ed] = cid
            rows.append(())
            labels.append(
                "+".join(f"{WORFBENCH_STAGES[s]}:{WORFBENCH_MODULES[s][m]}" for s, m in ed)
            )

        sorted_cfgs = sorted(reachable_cfgs)
        leaf_id: dict[tuple[int, int, int, int], int] = {}
        means: dict[int, float] = {}
        leaf_scores: dict[int, np.ndarray] = {}
        leaf_workflow_name: dict[int, str] = {}

        for cfg in sorted_cfgs:
            lid = len(rows)
            leaf_id[cfg] = lid
            rows.append(())
            w_idx = cfg_to_widx(cfg)
            labels.append(f"wf:{workflows[w_idx]}")
            row_scores = dom_scores[w_idx]
            leaf_scores[lid] = row_scores
            means[lid] = float(np.mean(row_scores))
            leaf_workflow_name[lid] = workflows[w_idx]

        for idx, (_, _, cfg1) in enumerate(anchors):
            aid = action_ids[idx]
            rows[aid] = tuple([leaf_id[cfg1]] + [combo_id[ed] for ed in anchor_subs[idx]])

        for ed in sorted_combos:
            cid = combo_id[ed]
            cfg = apply_up(ed)
            rows[cid] = tuple([leaf_id[cfg]] + [combo_id[nxt] for nxt in combo_children[ed]])

        graph = DAG(rows, root=0, labels=labels)
        base_code = "".join(map(str, base_config))
        prob_name = name or f"worfbench_{domain}_b{base_code}_u{max_upgrades}"
        super().__init__(prob_name, graph, means, ())

        self.domain = domain
        self.base_config = base_config
        self.base_mean_f1 = float(np.mean(dom_scores[cfg_to_widx(base_config)]))
        self.max_upgrades = max_upgrades
        self.num_tasks = n_tasks
        self.action_labels = tuple(action_labels)
        self.leaf_scores = leaf_scores
        self.leaf_workflow_name = leaf_workflow_name

    def oracle(self, seed: int):
        prob = self
        s64 = seed & 0xFFFFFFFFFFFFFFFF
        n_tasks = prob.num_tasks
        score_map = prob.leaf_scores

        class _WorFBenchTaskOracle:
            def __init__(self):
                self.obs = [0] * len(prob.graph)
                self.operations = 0

            def sample(self, leaf: int) -> float:
                self.obs[leaf] += 1
                k = self.obs[leaf]
                self.operations += 6
                u = splitmix_uniform01(s64, leaf, k)
                t_idx = min(n_tasks - 1, int(u * n_tasks))
                return float(score_map[leaf][t_idx])

        return _WorFBenchTaskOracle()


def real_world_problem_diagnostics(prob: Problem) -> dict[str, float | int | str]:
    """Compute structural & statistical difficulty diagnostics for a real-world DAG."""
    diag = structural_diagnostics(prob.graph)
    g = prob.graph
    root_ch = g.children[g.root]

    reach: list[set[int]] = [set() for _ in range(len(g))]
    for v in reversed(g.order):
        ch = g.children[v]
        if not ch:
            reach[v].add(v)
        else:
            for c in ch:
                reach[v].update(reach[c])

    supports = [reach[c] for c in root_ch]
    all_leaves = set(g.leaves)
    vals = [max(prob.means[z] for z in sup) for sup in supports]
    v_star = max(vals)
    sorted_vals = sorted(vals, reverse=True)
    marg_gap = sorted_vals[0] - sorted_vals[1] if len(sorted_vals) >= 2 else v_star

    gammas = []
    for sup in supports:
        inside = max(prob.means[z] for z in sup)
        outside_set = all_leaves - sup
        outside = max((prob.means[z] for z in outside_set), default=0.0)
        gammas.append(inside - outside)
    gamma_star = max(gammas)

    sorted_leaf_means = sorted((prob.means[z] for z in g.leaves), reverse=True)
    flat_gap = sorted_leaf_means[0] - sorted_leaf_means[1] if len(sorted_leaf_means) >= 2 else sorted_leaf_means[0]

    out: dict[str, float | int | str] = {
        "name": prob.name,
        "vertices": len(g),
        "edges": sum(len(r) for r in g.children),
        "root_actions": len(root_ch),
        "leaves": len(g.leaves),
        "containment_pairs": int(diag["containment_pairs"]),
        "mean_pairwise_jaccard": round(float(diag["mean_jaccard"]), 4),
        "mean_membership": round(float(diag["mean_membership"]), 3),
        "leaf_transposition_rate": round(float(diag["leaf_transposition_rate"]), 4),
        "v_star": round(v_star, 6),
        "marginal_gap": round(marg_gap, 6),
        "exterior_margin_gamma": round(gamma_star, 6),
        "flat_top2_gap": round(flat_gap, 6),
    }
    if hasattr(prob, "raw_fitness"):
        fmax = getattr(prob, "fitness_max", GB1_FITNESS_MAX)
        out["opt_raw_fitness"] = round(gb1_mean_to_raw_fitness(v_star, fmax), 4)
    return out
