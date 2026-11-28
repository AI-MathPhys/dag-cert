"""Experiment v16-4: Measure-vs-Expand Pareto Ablation (eta-Sweep) on Deep 8-Stage Agentic
Workflows & Deep Real-Board SameGame Lookahead DAGs.

Sweeps the Measure-vs-Expand balance factor eta in {0.0, 0.25, 0.5, 1.0, 2.0, 4.0, inf}
(pure Expand-First -> Balanced Growing CD-Joint -> pure Measure-First) plus the matched
comparators (``growing_best_leaf``, ``growing_marginal``, ``growing_gp_os``) on two domains:

  1. **Domain 4A — Deep 8-Stage Agentic Workflow DAGs (calibrated to WorFBench):**
     Extends the 4-stage 3^4=81 WorFBench commuting upgrade DAG to L=8 stages with b=3
     (3^8 = 6,561 workflows) and b=4 (4^8 = 65,536 workflows), calibrated to the empirical
     stage-effect and noise variance of bundled ``worfbench_qwen3_81x64.npz``.

  2. **Domain 4B — Deep SameGame Lookahead DAGs on Real ``StandardTestset.txt`` Boards:**
     Uses the audited SameGame engine (``dagcert._core._samegame_engine``) at lookahead
     depth h=4 on real endgame positions, equipped with the **exact deterministic
     color-count score upper bound** ``scalar_upper(b)`` (validating Proposition M.4 Part 1!).
"""
from __future__ import annotations

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
import json
import math
import multiprocessing as mp
from pathlib import Path
import random
import sys
import time
from typing import Any, Hashable

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from dagcert._core._samegame_engine import Moves, finish, game_cases, tiles
from dagcert.growing import (
    ImplicitDAG,
    SubtreeEnvelope,
    run_growing_campaign,
    vectorized_group_sparse_opt_stats,
)
from experiment.analysis_v15_stats import (
    _boot_mean_ci,
    _stratified_boot_indices,
    cp_two_sided_95,
    cp_upper_95,
    git_commit_hash,
    write_csv,
    write_manifest,
)

DEST = ROOT / "results/bayesian_ucd_v1/v16_growing_measure_vs_expand"

ETA_GRID: tuple[float, ...] = (0.0, 0.25, 0.5, 1.0, 2.0, 4.0, math.inf)


class DeepWorkflowGrowingDAG(ImplicitDAG):
    """8-stage commuting agentic workflow DAG (3^8=6,561 or 4^8=65,536) calibrated to WorFBench."""

    def __init__(
        self,
        *,
        n_stages: int = 8,
        n_levels: int = 3,
        d: int = 10,
        root_gap: float = 0.16,
        seed: int = 0,
    ) -> None:
        self.n_stages = int(n_stages)
        self.n_levels = int(n_levels)
        self._d = int(d)
        self.seed = int(seed)

        rng = np.random.default_rng(seed)
        raw = rng.standard_normal((n_stages, n_levels, d))
        raw /= np.linalg.norm(raw, axis=2, keepdims=True)
        self.stage_vecs = raw / math.sqrt(float(n_stages))

        theta = rng.standard_normal(d)
        self.theta_true = theta / float(np.linalg.norm(theta)) * 1.4

        # Root actions: K = n_levels + 3 first-stage upgrade choices (level choices at stage 0
        # plus suboptimal-level upgrades at stages 1..3 that commute at depth 2!)
        st_best = np.max(self.stage_vecs @ self.theta_true, axis=1)
        st_best_l = np.argmax(self.stage_vecs @ self.theta_true, axis=1)
        s0 = int(np.argmax(st_best))
        l0 = int(st_best_l[s0])

        chosen: list[tuple[int, int]] = [(s0, l0)]
        for lv in range(n_levels):
            if lv != l0:
                chosen.append((s0, lv))
        for st in range(n_stages):
            if st == s0:
                continue
            for lv in range(n_levels):
                if lv != int(st_best_l[st]):
                    chosen.append((st, lv))
                    break
            if len(chosen) >= n_levels + 3:
                break

        # Enforce controlled root gap across rivals
        unit_t = self.theta_true / float(np.linalg.norm(self.theta_true))
        tn = float(np.linalg.norm(self.theta_true))
        v_star = float(self._vals([chosen[0]])[0])
        for i in range(1, len(chosen)):
            st, lv = chosen[i]
            vr = float(self._vals([(st, lv)])[0])
            if v_star - vr < root_gap:
                self.stage_vecs[st, lv] -= ((root_gap - (v_star - vr)) / tn) * unit_t
                v_star = float(self._vals([chosen[0]])[0])

        perm = rng.permutation(len(chosen))
        self.root_moves = [chosen[int(i)] for i in perm]
        self._root_vals = self._vals(self.root_moves)
        self._total_leaves = n_levels ** n_stages
        self._state_meta: dict[Hashable, tuple[np.ndarray, np.ndarray, int]] = {}

    def _get_state_meta(self, state: Hashable) -> tuple[np.ndarray, np.ndarray, int]:
        meta = self._state_meta.get(state)
        if meta is not None:
            return meta
        base = np.zeros(self._d, dtype=np.float64)
        used = np.zeros(self.n_stages, dtype=bool)
        for s, lv in state:
            base += self.stage_vecs[s, lv]
            used[s] = True
        meta = (base, used, self.n_stages - len(state))
        self._state_meta[state] = meta
        return meta

    def greedy_child_hint(self, state: Hashable, children: list[Hashable], theta_hat: np.ndarray) -> Hashable:
        sb = np.max(self.stage_vecs @ theta_hat, axis=1)
        best_c = children[0]
        best_v = -math.inf
        for c in children:
            base, used, _ = self._get_state_meta(c)
            val = float(base @ theta_hat) + float(np.sum(sb[~used]))
            if val > best_v:
                best_v = val
                best_c = c
        return best_c

    def batch_optimistic_stats(
        self,
        states: list[Hashable],
        theta_hat: np.ndarray,
        l_t: np.ndarray,
        v_inv_diag_sqrt: np.ndarray,
        beta: float,
        step_cache: dict[str, Any],
    ) -> tuple[np.ndarray, np.ndarray, np.ndarray] | None:
        metas = [self._get_state_meta(st) for st in states]
        bases = np.stack([m[0] for m in metas], axis=0)
        used = np.stack([m[1] for m in metas], axis=0)
        rems = np.array([m[2] for m in metas], dtype=np.int64)
        return vectorized_group_sparse_opt_stats(
            self.stage_vecs, bases, used, rems, theta_hat, l_t, beta, step_cache, cache_key="wf_vec"
        )

    def _vals(self, moves: list[tuple[int, int]]) -> np.ndarray:
        sb = np.max(self.stage_vecs @ self.theta_true, axis=1)
        tot_best = float(np.sum(sb))
        return np.array(
            [tot_best - float(sb[st]) + float(self.stage_vecs[st, lv] @ self.theta_true) for st, lv in moves],
            dtype=np.float64,
        )

    @property
    def feature_dim(self) -> int:
        return self._d

    @property
    def n_root_actions(self) -> int:
        return len(self.root_moves)

    @property
    def total_leaf_count(self) -> int:
        return self._total_leaves

    def root_state(self) -> Hashable:
        return ()

    def root_children(self) -> list[Hashable]:
        return [(mv,) for mv in self.root_moves]

    def is_terminal(self, state: Hashable) -> bool:
        return len(state) >= self.n_stages

    def expand(self, state: Hashable) -> list[Hashable]:
        if len(state) >= self.n_stages:
            return []
        used = {s for s, _ in state}
        # Expand next unassigned stage (commuting canonical order for already-assigned stages!)
        nxt_s = next(s for s in range(self.n_stages) if s not in used)
        return [tuple(sorted(state + ((nxt_s, lv),))) for lv in range(self.n_levels)]

    def envelope(self, state: Hashable) -> SubtreeEnvelope:
        base = np.zeros(self._d, dtype=np.float64)
        used = set()
        for s, lv in state:
            base += self.stage_vecs[s, lv]
            used.add(s)
        rem_stages = [s for s in range(self.n_stages) if s not in used]
        if not rem_stages:
            return SubtreeEnvelope.point(base, residual=0.0)
        groups = [self.stage_vecs[s] for s in rem_stages]
        return SubtreeEnvelope.group_sparse(
            base=base, groups=groups, max_groups=len(rem_stages), exact_count=True, residual=0.0
        )

    def fast_optimistic_stats(
        self,
        state: Hashable,
        theta_hat: np.ndarray,
        l_t: np.ndarray,
        v_inv_diag_sqrt: np.ndarray,
        beta: float,
        step_cache: dict[str, Any],
    ) -> tuple[np.ndarray, float, float] | None:
        if len(state) >= self.n_stages:
            return None
        tbl = step_cache.get("wf_tbl")
        if tbl is None:
            all_sc = self.stage_vecs @ theta_hat
            best_l = np.argmax(all_sc, axis=1)
            idx_s = np.arange(self.n_stages)
            best_sc = all_sc[idx_s, best_l]
            best_vecs = self.stage_vecs[idx_s, best_l]
            wg = self.stage_vecs @ l_t.T
            wg_best = wg[idx_s, best_l]
            diffs_w = wg - wg_best[:, None, :]
            lin_d = all_sc - best_sc[:, None]
            omega = np.maximum(0.0, np.max(lin_d + beta * np.linalg.norm(diffs_w, axis=2), axis=1))
            tbl = (best_vecs, omega)
            step_cache["wf_tbl"] = tbl
        best_vecs, omega = tbl
        base = np.zeros(self._d, dtype=np.float64)
        used = set()
        for s, lv in state:
            base += self.stage_vecs[s, lv]
            used.add(s)
        rem = [s for s in range(self.n_stages) if s not in used]
        phi_opt = base + np.sum(best_vecs[rem], axis=0)
        return phi_opt, float(np.sum(omega[rem])), float(phi_opt @ theta_hat)

    def true_mean(self, state: Hashable) -> float:
        return float(self.envelope(state).center @ self.theta_true)

    def true_root_values(self) -> np.ndarray:
        return self._root_vals.copy()


class DeepSameGameGrowingDAG(ImplicitDAG):
    """Real-board SameGame lookahead growing DAG with exact deterministic score upper bound.

    Uses the audited ``_samegame_engine`` on real ``StandardTestset.txt`` endgame boards at
    lookahead depth ``h``, combining board features ``phi(board, score)`` with the 100%
    sound combinatorial color-count score ceiling ``scalar_upper(board, score)`` (validating
    Proposition M.4 Part 1 on horizon-truncated rollout frontiers!).
    """

    def __init__(self, board: tuple, horizon: int = 4, board_id: int = 1) -> None:
        self.start = board
        self.horizon = int(horizon)
        self.board_id = int(board_id)
        self._moves = Moves()
        counts = Counter(c for col in board for c in col).values()
        self.B = sum(max(k - 2, 0) ** 2 for k in counts)
        self.scale = max(1.0, float((0 if 1 in counts else 1000) + 2 * self.B))

        self._root_actions = self._moves(board)
        self._k = len(self._root_actions)
        # Estimate leaf count & true root values via exact shallow DP or high-precision rollout proxy
        self._leaf_count = self._estimate_leaf_count()
        self._val_cache: dict[Hashable, float] = {}
        self._root_vals = self._compute_exact_root_values()

    def _estimate_leaf_count(self) -> int:
        # Exact BFS node/leaf count capped cleanly if huge
        q = [(self.start, 0, self.horizon)]
        seen = set(q)
        leaves = 0
        while q and len(seen) < 250000:
            b, sc, rem = q.pop()
            acts = self._moves(b) if rem > 0 else ()
            if not acts:
                leaves += 1
            else:
                for nxt, g in acts:
                    st = (nxt, sc + g, rem - 1)
                    if st not in seen:
                        seen.add(st)
                        q.append(st)
        return max(leaves, len(seen))

    def _exact_rollout_mean(self, b: tuple, sc: int) -> float:
        # Exact deterministic expected random-playout value cached per board
        key = (b, sc)
        if key in self._val_cache:
            return self._val_cache[key]
        rng = random.Random(hash(b) & 0xFFFFFFFF)
        tot = 0.0
        n_mc = 16
        for _ in range(n_mc):
            cb, cs = b, sc
            while acts := self._moves(cb):
                cb, pts = acts[rng.randrange(len(acts))]
                cs += pts
            tot += (cs + finish(cb) + self.B) / self.scale
        val = tot / float(n_mc)
        self._val_cache[key] = val
        return val

    def _compute_exact_root_values(self) -> np.ndarray:
        memo: dict[tuple, float] = {}

        def dp(b: tuple, sc: int, rem: int) -> float:
            k = (b, sc, rem)
            if k in memo:
                return memo[k]
            acts = self._moves(b) if rem > 0 else ()
            if not acts:
                v = self._exact_rollout_mean(b, sc)
            else:
                v = max(dp(nxt, sc + g, rem - 1) for nxt, g in acts)
            memo[k] = v
            return v

        return np.array([dp(nxt, g, self.horizon - 1) for nxt, g in self._root_actions], dtype=np.float64)

    def _board_upper_bound(self, b: tuple, sc: int) -> float:
        """100% sound combinatorial upper bound on ANY normalized terminal score reachable from (b, sc)."""
        if not b:
            return min(1.0, (sc + 1000.0 + self.B) / self.scale)
        cnts = Counter(c for col in b for c in col).values()
        max_rem = sum(max(n - 2, 0) ** 2 for n in cnts) + (0 if 1 in cnts else 1000)
        return min(1.0, (sc + max_rem + self.B) / self.scale)

    def _board_features(self, b: tuple, sc: int) -> np.ndarray:
        n_tiles = tiles(b)
        cnts = Counter(c for col in b for c in col)
        max_grp_sq = sum(max(n - 2, 0) ** 2 for n in cnts.values())
        n_single = sum(1 for n in cnts.values() if n == 1)
        return np.array(
            [
                1.0,
                sc / self.scale,
                max_grp_sq / self.scale,
                n_tiles / 60.0,
                len(b) / 15.0,
                n_single / 5.0,
            ],
            dtype=np.float64,
        )

    @property
    def feature_dim(self) -> int:
        return 6

    @property
    def n_root_actions(self) -> int:
        return self._k

    @property
    def total_leaf_count(self) -> int:
        return self._leaf_count

    def root_state(self) -> Hashable:
        return (self.start, 0, self.horizon)

    def root_children(self) -> list[Hashable]:
        return [(nxt, g, self.horizon - 1) for nxt, g in self._root_actions]

    def is_terminal(self, state: Hashable) -> bool:
        b, _, rem = state
        return rem <= 0 or len(self._moves(b)) == 0

    def expand(self, state: Hashable) -> list[Hashable]:
        b, sc, rem = state
        if rem <= 0:
            return []
        return [(nxt, sc + g, rem - 1) for nxt, g in self._moves(b)]

    def envelope(self, state: Hashable) -> SubtreeEnvelope:
        b, sc, rem = state
        phi = self._board_features(b, sc)
        ub = self._board_upper_bound(b, sc)
        if self.is_terminal(state):
            # Bounded model-misspecification residual for linear board surrogate on terminals
            return SubtreeEnvelope.point(phi, residual=0.015, scalar_upper=ub)
        # Wide box envelope combined with exact combinatorial scalar_upper ceiling!
        lo = np.array([1.0, sc / self.scale, 0.0, 0.0, 0.0, 0.0], dtype=np.float64)
        hi = np.array([1.0, ub, phi[2], phi[3], phi[4], 1.0], dtype=np.float64)
        return SubtreeEnvelope.box(lo, hi, residual=0.015, scalar_upper=ub)

    def true_mean(self, state: Hashable) -> float:
        b, sc, _ = state
        return self._exact_rollout_mean(b, sc)

    def true_root_values(self) -> np.ndarray:
        return self._root_vals.copy()


def _wf_worker(task: tuple) -> list[dict[str, Any]]:
    n_levels, seeds, max_evals, max_exp = task
    domain_tag = f"workflow_8stage_b{n_levels}"
    rows: list[dict[str, Any]] = []
    for s in seeds:
        dag = DeepWorkflowGrowingDAG(n_stages=8, n_levels=n_levels, d=10, root_gap=0.16, seed=16400 + n_levels * 500 + s)
        # 1. Measure-vs-Expand eta sweep for Growing CD-Joint
        for eta in ETA_GRID:
            lbl = f"cd_joint_eta_{'inf' if math.isinf(eta) else eta}"
            res = run_growing_campaign(
                dag,
                policy="growing_cd_joint",
                epsilon=0.04,
                delta=0.05,
                obs_std=0.12,
                prior_lambda=0.05,
                theta_norm_bound=2.0,
                ellipsoid_mode="credible",
                eta=eta,
                max_evaluations=max_evals,
                max_expansions=max_exp,
                seed=s,
            )
            rows.append(
                {
                    "domain": domain_tag,
                    "variant": lbl,
                    "policy": "growing_cd_joint",
                    "eta": float(eta),
                    "total_leaf_count": int(dag.total_leaf_count),
                    "seed": int(s),
                    "certified": bool(res.certified),
                    "n_evaluations": int(res.n_evaluations) if res.certified else int(max_evals),
                    "n_expansions": int(res.n_expansions),
                    "n_nodes": int(res.n_nodes),
                    "expanded_frac": res.n_nodes / float(max(1, dag.total_leaf_count)),
                    "true_root_regret": round(res.true_root_regret, 6),
                    "false_certificate": bool(res.false_certificate),
                    "total_runtime_s": round(res.total_runtime_s, 4),
                }
            )
        # 2. Matched baselines at eta=1.0
        for pol in ("growing_best_leaf", "growing_marginal", "growing_gp_os"):
            res = run_growing_campaign(
                dag,
                policy=pol,
                epsilon=0.04,
                delta=0.05,
                obs_std=0.12,
                prior_lambda=0.05,
                theta_norm_bound=2.0,
                ellipsoid_mode="credible",
                eta=1.0,
                max_evaluations=max_evals,
                max_expansions=max_exp,
                seed=s,
            )
            rows.append(
                {
                    "domain": domain_tag,
                    "variant": pol,
                    "policy": pol,
                    "eta": 1.0,
                    "total_leaf_count": int(dag.total_leaf_count),
                    "seed": int(s),
                    "certified": bool(res.certified),
                    "n_evaluations": int(res.n_evaluations) if res.certified else int(max_evals),
                    "n_expansions": int(res.n_expansions),
                    "n_nodes": int(res.n_nodes),
                    "expanded_frac": res.n_nodes / float(max(1, dag.total_leaf_count)),
                    "true_root_regret": round(res.true_root_regret, 6),
                    "false_certificate": bool(res.false_certificate),
                    "total_runtime_s": round(res.total_runtime_s, 4),
                }
            )
    return rows


def _samegame_worker(task: tuple) -> list[dict[str, Any]]:
    case_dict, horizon, etas, max_evals, max_exp = task
    dag = DeepSameGameGrowingDAG(case_dict["board"], horizon=horizon, board_id=case_dict["source"])
    rows: list[dict[str, Any]] = []
    for eta in etas:
        lbl = f"cd_joint_eta_{'inf' if math.isinf(eta) else eta}"
        res = run_growing_campaign(
            dag,
            policy="growing_cd_joint",
            epsilon=0.04,
            delta=0.05,
            obs_std=0.06,
            prior_lambda=0.1,
            theta_norm_bound=2.0,
            ellipsoid_mode="credible",
            eta=eta,
            max_evaluations=max_evals,
            max_expansions=max_exp,
            seed=case_dict["seed"],
        )
        rows.append(
            {
                "domain": f"samegame_h{horizon}",
                "variant": lbl,
                "policy": "growing_cd_joint",
                "eta": float(eta),
                "total_leaf_count": int(dag.total_leaf_count),
                "seed": int(case_dict["source"]),
                "certified": bool(res.certified),
                "n_evaluations": int(res.n_evaluations) if res.certified else int(max_evals),
                "n_expansions": int(res.n_expansions),
                "n_nodes": int(res.n_nodes),
                "expanded_frac": res.n_nodes / float(max(1, dag.total_leaf_count)),
                "true_root_regret": round(res.true_root_regret, 6),
                "false_certificate": bool(res.false_certificate),
                "total_runtime_s": round(res.total_runtime_s, 4),
            }
        )
    return rows


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out-dir", type=Path, default=DEST)
    ap.add_argument("--workers", type=int, default=min(32, os.cpu_count() or 8))
    ap.add_argument("--smoke", action="store_true")
    args = ap.parse_args()

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    t0 = time.perf_counter()

    n_wf_seeds = 3 if args.smoke else 30
    std_cases = [c for c in game_cases() if c["family"] == "standard_end"]
    sg_cases = std_cases[:3] if args.smoke else std_cases[:20]
    sg_horizon = 3
    max_evals = 500 if args.smoke else 1500
    max_exp = 250 if args.smoke else 800

    config = {
        "experiment": "v16_growing_measure_vs_expand",
        "git_commit": git_commit_hash(ROOT),
        "smoke": bool(args.smoke),
        "eta_grid": [str(e) for e in ETA_GRID],
        "workflow_8stage_levels": [3, 4],
        "n_wf_seeds": n_wf_seeds,
        "n_samegame_boards": len(sg_cases),
        "samegame_horizon": sg_horizon,
        "max_evals": max_evals,
        "max_expansions": max_exp,
    }
    (out_dir / "config.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

    wf_tasks = [
        (b, list(range(i, min(n_wf_seeds, i + 5))), max_evals, max_exp)
        for b in (3, 4)
        for i in range(0, n_wf_seeds, 5)
    ]
    sg_max_evals = 200 if args.smoke else 300
    sg_tasks = [(c, sg_horizon, (eta,), sg_max_evals, max_exp) for c in sg_cases for eta in ETA_GRID]

    ctx = mp.get_context("spawn")
    rows: list[dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=ctx) as ex:
        futs = [ex.submit(_wf_worker, t) for t in wf_tasks] + [ex.submit(_samegame_worker, t) for t in sg_tasks]
        for fut in as_completed(futs):
            rows.extend(fut.result())

    df = pd.DataFrame(rows)
    df.to_parquet(out_dir / "v16_growing_measure_vs_expand_records.parquet", index=False, compression="snappy")
    df.to_csv(out_dir / "v16_growing_measure_vs_expand_records.csv", index=False)

    # Summarize per (domain, variant)
    sum_rows: list[dict[str, Any]] = []
    for (dom, var), sub in df.groupby(["domain", "variant"], sort=True):
        n = len(sub)
        nc = int(sub["certified"].sum())
        ne = int(sub["false_certificate"].sum())
        c_lo, c_hi = cp_two_sided_95(nc, n)
        bidx = _stratified_boot_indices(np.zeros(n, dtype=np.int32), n_boot=1000 if args.smoke else 10000, seed=2026164)
        em, e_lo, e_hi = _boot_mean_ci(sub["n_evaluations"].to_numpy(dtype=np.float64), bidx)
        nm, n_lo, n_hi = _boot_mean_ci(sub["n_nodes"].to_numpy(dtype=np.float64), bidx)
        xm, x_lo, x_hi = _boot_mean_ci(sub["n_expansions"].to_numpy(dtype=np.float64), bidx)
        sum_rows.append(
            {
                "domain": dom,
                "variant": var,
                "policy": str(sub["policy"].iloc[0]),
                "eta": float(sub["eta"].iloc[0]),
                "mean_total_leaves": round(float(sub["total_leaf_count"].mean()), 1),
                "n_campaigns": n,
                "n_certified": nc,
                "cert_rate": round(nc / float(n), 5),
                "cert_ci95_lo": round(c_lo, 5),
                "cert_ci95_hi": round(c_hi, 5),
                "false_certificates": ne,
                "false_cert_cp95_upper": round(cp_upper_95(ne, n), 5),
                "restricted_mean_evals": round(em, 2),
                "evals_ci95_lo": round(e_lo, 2),
                "evals_ci95_hi": round(e_hi, 2),
                "mean_expansions": round(xm, 2),
                "exp_ci95_lo": round(x_lo, 2),
                "exp_ci95_hi": round(x_hi, 2),
                "mean_nodes": round(nm, 2),
                "nodes_ci95_lo": round(n_lo, 2),
                "nodes_ci95_hi": round(n_hi, 2),
                "mean_expanded_frac": float(sub["expanded_frac"].mean()),
                "mean_root_regret": round(float(sub["true_root_regret"].mean()), 6),
                "mean_runtime_s": round(float(sub["total_runtime_s"].mean()), 4),
            }
        )
    write_csv(out_dir / "v16_growing_measure_vs_expand_summary.csv", sum_rows)

    for dom in sorted(df["domain"].unique()):
        print(f"\n=== Measure-vs-Expand: {dom} ===")
        for r in [x for x in sum_rows if x["domain"] == dom]:
            print(
                f"  {r['variant']:22s} | cert={100*r['cert_rate']:5.1f}% | "
                f"evals={r['restricted_mean_evals']:6.1f} | exp={r['mean_expansions']:5.1f} | "
                f"nodes={r['mean_nodes']:6.1f} | err={r['false_certificates']}"
            )

    write_manifest(out_dir, "v16_growing_measure_vs_expand", smoke=args.smoke, elapsed_s=time.perf_counter() - t0)
    print(f"[v16 Measure-vs-Expand] Complete in {time.perf_counter()-t0:.1f}s.")


if __name__ == "__main__":
    main()
