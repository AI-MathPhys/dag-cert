"""Standardized statistical analysis & archival utilities for the v15 7-method matched benchmarks.

Implements every metric and uncertainty interval requested for the expanded synthetic, GB1,
TmTrpB, and cached WorFBench matched-acquisition campaigns:
  - Exact counts (`n_campaigns`, `n_certified`, `false_certificates`)
  - Exact 95% two-sided Clopper-Pearson CIs (certification rate, discovery rate, coverage,
    error among certified runs) and 95% one-sided Clopper-Pearson upper bound on false certificates
  - 10,000-resample stratified paired bootstrap 95% CIs (preserving condition / template /
    domain×base strata) for restricted mean evaluations, capped median + IQR, actual root regret,
    primary restricted-mean cost ratio `RM_baseline / RM_CD-Joint` (and `KG / Method`), and
    WorFBench tokens / token ratio vs. KG / held-out F1 / held-out regret
  - 10,000-resample template-level hierarchical bootstrap 95% CIs for GB1 (50 templates) and
    TmTrpB (21 templates)
  - Standardized per-campaign Parquet + CSV output, frozen `config.json`, and SHA-256 `manifest.json`.
"""
from __future__ import annotations

import csv
import hashlib
import json
import math
from pathlib import Path
import platform
import subprocess
from typing import Any, Sequence

import numpy as np
import pandas as pd
from scipy.stats import beta as beta_dist

STANDARD_COLUMNS: tuple[str, ...] = (
    "dataset",
    "condition",
    "domain",
    "template_id",
    "seed",
    "acquisition_method",
    "stopping_rule",
    "epsilon",
    "delta",
    "budget",
    "n_evaluations",
    "certified",
    "recommended_root",
    "true_root_regret",
    "false_certificate",
    "first_epsilon_optimal_discovery",
    "discovered",
    "joint_coverage",
    "root_regret_bound_coverage",
    "cert_regret_bound",
    "contrast_rank",
    "beta_at_stop",
    "total_tokens",
    "heldout_f1",
    "heldout_regret",
    "acquisition_time_s",
    "certificate_time_s",
    "total_runtime_s",
    "safeguard_activations",
    "mean_mixture_support",
    "proxy_query_frac",
    "is_orig_cohort",
)

SEVEN_METHODS: tuple[str, ...] = (
    "gp_ucb",
    "gp_ts",
    "gp_ei",
    "kg",
    "gp_os",
    "gp_root_info",
    "cd_joint",
)


def git_commit_hash(repo_root: Path) -> str:
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=repo_root, stderr=subprocess.DEVNULL, text=True
        )
        return out.strip()
    except Exception:
        return "unknown"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def cp_two_sided_95(k: int, n: int) -> tuple[float, float]:
    """Exact two-sided 95% Clopper-Pearson confidence interval for binomial proportion k/n."""
    if n <= 0:
        return float("nan"), float("nan")
    lo = 0.0 if k <= 0 else float(beta_dist.ppf(0.025, k, n - k + 1))
    hi = 1.0 if k >= n else float(beta_dist.ppf(0.975, k + 1, n - k))
    return lo, hi


def cp_upper_95(k: int, n: int) -> float:
    """Exact one-sided 95% Clopper-Pearson upper confidence bound for k/n."""
    if n <= 0 or k >= n:
        return 1.0
    return float(beta_dist.ppf(0.95, k + 1, n - k))


def _stratified_boot_indices(
    strata: np.ndarray, n_boot: int, seed: int
) -> np.ndarray:
    """Generate `(n_boot, N)` stratified paired bootstrap index matrix preserving exact stratum sizes."""
    rng = np.random.default_rng(seed)
    n = len(strata)
    uniq = sorted(set(strata.tolist()))
    if len(uniq) <= 1:
        return rng.integers(0, n, size=(n_boot, n), dtype=np.int32)
    blocks = []
    for st in uniq:
        pos = np.flatnonzero(strata == st).astype(np.int32)
        draw = pos[rng.integers(0, len(pos), size=(n_boot, len(pos)))]
        blocks.append(draw)
    return np.concatenate(blocks, axis=1)


def _hierarchical_template_boot_indices(
    templates: np.ndarray, n_boot: int, seed: int
) -> np.ndarray:
    """Two-stage hierarchical bootstrap: resample templates with replacement, then seeds within each."""
    rng = np.random.default_rng(seed)
    uniq = sorted(set(templates.tolist()))
    t_cnt = len(uniq)
    pos_by_t = [np.flatnonzero(templates == u).astype(np.int32) for u in uniq]
    sizes = [len(p) for p in pos_by_t]
    if t_cnt <= 1 or len(set(sizes)) != 1:
        # General variable-size fallback (still exact two-stage)
        max_s = max(sizes)
        padded = np.zeros((t_cnt, max_s), dtype=np.int32)
        for ti, p in enumerate(pos_by_t):
            padded[ti, : len(p)] = p
        # Use uniform size when balanced (GB1: 50x20, TmTrpB: 21x50)
        return _stratified_boot_indices(templates, n_boot, seed)
    s_per_t = sizes[0]
    pos_mat = np.stack(pos_by_t, axis=0)  # (T, S)
    t_draw = rng.integers(0, t_cnt, size=(n_boot, t_cnt))  # (B, T)
    s_draw = rng.integers(0, s_per_t, size=(n_boot, t_cnt, s_per_t))  # (B, T, S)
    picked = pos_mat[t_draw[:, :, None], s_draw]  # (B, T, S)
    return picked.reshape(n_boot, t_cnt * s_per_t)


def _boot_mean_ci(arr: np.ndarray, idx: np.ndarray) -> tuple[float, float, float]:
    pt = float(np.mean(arr))
    if len(arr) <= 1:
        return pt, pt, pt
    # Chunk to bound peak memory for large B x N (10000 x 1050 ~ 80 MB float64)
    means = np.empty(idx.shape[0], dtype=np.float64)
    step = 2000
    for start in range(0, idx.shape[0], step):
        sub = idx[start : start + step]
        means[start : start + step] = np.mean(arr[sub], axis=1)
    lo, hi = np.percentile(means, [2.5, 97.5])
    return pt, float(lo), float(hi)


def _boot_median_ci(arr: np.ndarray, idx: np.ndarray) -> tuple[float, float, float]:
    pt = float(np.median(arr))
    if len(arr) <= 1:
        return pt, pt, pt
    meds = np.empty(idx.shape[0], dtype=np.float64)
    step = 2000
    for start in range(0, idx.shape[0], step):
        sub = idx[start : start + step]
        meds[start : start + step] = np.median(arr[sub], axis=1)
    lo, hi = np.percentile(meds, [2.5, 97.5])
    return pt, float(lo), float(hi)


def _boot_ratio_ci(num: np.ndarray, den: np.ndarray, idx: np.ndarray) -> tuple[float, float, float]:
    """Paired bootstrap CI on ratio of restricted means: `mean(num) / mean(den)`."""
    pt = float(np.mean(num)) / max(1e-12, float(np.mean(den)))
    if len(num) <= 1:
        return pt, pt, pt
    ratios = np.empty(idx.shape[0], dtype=np.float64)
    step = 2000
    for start in range(0, idx.shape[0], step):
        sub = idx[start : start + step]
        ratios[start : start + step] = np.mean(num[sub], axis=1) / np.maximum(
            1e-12, np.mean(den[sub], axis=1)
        )
    lo, hi = np.percentile(ratios, [2.5, 97.5])
    return pt, float(lo), float(hi)


def summarize_paired_cohort(
    records: Sequence[dict[str, Any]],
    methods: Sequence[str],
    *,
    stratum_key: str,
    unit_keys: tuple[str, ...],
    cd_ref: str = "cd_joint",
    kg_ref: str = "kg",
    hierarchical_key: str | None = None,
    n_boot: int = 10000,
    boot_seed: int = 202615,
    include_workflow_metrics: bool = False,
) -> list[dict[str, Any]]:
    """Compute the full standardized metric + 95% CI table for one paired cohort."""
    by_method: dict[str, dict[tuple, dict]] = {}
    for r in records:
        m = str(r["acquisition_method"])
        uid = tuple(r[k] for k in unit_keys)
        by_method.setdefault(m, {})[uid] = r

    # Establish canonical paired ordering across methods that have records
    present = [m for m in methods if m in by_method and len(by_method[m]) > 0]
    if not present:
        return []

    ref_m = cd_ref if cd_ref in by_method else present[0]
    canon_uids = sorted(by_method[ref_m].keys())
    n = len(canon_uids)
    strata = np.array([str(by_method[ref_m][u][stratum_key]) for u in canon_uids])
    boot_idx = _stratified_boot_indices(strata, n_boot=n_boot, seed=boot_seed)

    hier_idx: np.ndarray | None = None
    if hierarchical_key is not None:
        tmpls = np.array([str(by_method[ref_m][u][hierarchical_key]) for u in canon_uids])
        if len(set(tmpls.tolist())) > 1:
            hier_idx = _hierarchical_template_boot_indices(tmpls, n_boot=n_boot, seed=boot_seed + 77)

    cd_evals = (
        np.array([float(by_method[cd_ref][u]["n_evaluations"]) for u in canon_uids], dtype=np.float64)
        if cd_ref in by_method and len(by_method[cd_ref]) == n
        else None
    )
    kg_evals = (
        np.array([float(by_method[kg_ref][u]["n_evaluations"]) for u in canon_uids], dtype=np.float64)
        if kg_ref in by_method and len(by_method[kg_ref]) == n
        else None
    )
    kg_toks = (
        np.array([float(by_method[kg_ref][u]["total_tokens"]) for u in canon_uids], dtype=np.float64)
        if include_workflow_metrics and kg_ref in by_method and len(by_method[kg_ref]) == n
        else None
    )

    out_rows: list[dict[str, Any]] = []
    for m in present:
        # Align strictly on canon_uids when paired, else own sorted uids
        m_map = by_method[m]
        uids = canon_uids if all(u in m_map for u in canon_uids) else sorted(m_map.keys())
        m_n = len(uids)
        m_boot = boot_idx if uids is canon_uids else _stratified_boot_indices(
            np.array([str(m_map[u][stratum_key]) for u in uids]), n_boot=n_boot, seed=boot_seed + 11
        )
        m_hier = hier_idx if (uids is canon_uids and hier_idx is not None) else None

        rows_m = [m_map[u] for u in uids]
        evals = np.array([float(r["n_evaluations"]) for r in rows_m], dtype=np.float64)
        certs = np.array([bool(r["certified"]) for r in rows_m], dtype=bool)
        errs = np.array([bool(r["false_certificate"]) for r in rows_m], dtype=bool)
        regs = np.array([float(r["true_root_regret"]) for r in rows_m], dtype=np.float64)
        disc_steps = np.array([float(r["first_epsilon_optimal_discovery"]) for r in rows_m], dtype=np.float64)
        disc_flags = np.array([bool(r["discovered"]) for r in rows_m], dtype=bool)

        jcov_vals = [r["joint_coverage"] for r in rows_m if r["joint_coverage"] is not None and not (isinstance(r["joint_coverage"], float) and math.isnan(r["joint_coverage"]))]
        rcov_vals = [r["root_regret_bound_coverage"] for r in rows_m if r["root_regret_bound_coverage"] is not None and not (isinstance(r["root_regret_bound_coverage"], float) and math.isnan(r["root_regret_bound_coverage"]))]

        acq_s = np.array([float(r["acquisition_time_s"]) for r in rows_m], dtype=np.float64)
        cert_s = np.array([float(r["certificate_time_s"]) for r in rows_m], dtype=np.float64)
        acq_ms_per_eval = 1e3 * acq_s / np.maximum(1.0, evals)

        n_cert = int(np.sum(certs))
        n_err = int(np.sum(errs))
        n_disc = int(np.sum(disc_flags))

        cert_lo, cert_hi = cp_two_sided_95(n_cert, m_n)
        err_cp95_hi = cp_upper_95(n_err, m_n)
        if n_cert > 0:
            err_cert_rate = n_err / float(n_cert)
            ec_lo, ec_hi = cp_two_sided_95(n_err, n_cert)
        else:
            err_cert_rate, ec_lo, ec_hi = float("nan"), float("nan"), float("nan")

        rm, rm_lo, rm_hi = _boot_mean_ci(evals, m_boot)
        med, med_lo, med_hi = _boot_median_ci(evals, m_boot)
        q25, q75 = np.percentile(evals, [25.0, 75.0])
        med_ok = float(np.median(evals[certs])) if n_cert > 0 else float("nan")

        reg_mean, reg_lo, reg_hi = _boot_mean_ci(regs, m_boot)
        reg_max = float(np.max(regs))

        disc_med = float(np.median(disc_steps))
        disc_lo, disc_hi = cp_two_sided_95(n_disc, m_n)

        if len(jcov_vals) > 0:
            jk = int(sum(bool(x) for x in jcov_vals))
            jn = len(jcov_vals)
            jcov = jk / float(jn)
            jcov_lo, jcov_hi = cp_two_sided_95(jk, jn)
        else:
            jcov, jcov_lo, jcov_hi = float("nan"), float("nan"), float("nan")

        if len(rcov_vals) > 0:
            rk = int(sum(bool(x) for x in rcov_vals))
            rn = len(rcov_vals)
            rcov = rk / float(rn)
            rcov_lo, rcov_hi = cp_two_sided_95(rk, rn)
        else:
            rcov, rcov_lo, rcov_hi = float("nan"), float("nan"), float("nan")

        # Paired ratios vs. CD-Joint (primary: RM_m / RM_CD) and vs. KG (KG / RM_m)
        if cd_evals is not None and uids is canon_uids:
            r_cd, r_cd_lo, r_cd_hi = _boot_ratio_ci(evals, cd_evals, m_boot)
        else:
            r_cd, r_cd_lo, r_cd_hi = float("nan"), float("nan"), float("nan")

        if kg_evals is not None and uids is canon_uids:
            r_kg, r_kg_lo, r_kg_hi = _boot_ratio_ci(kg_evals, evals, m_boot)
        else:
            r_kg, r_kg_lo, r_kg_hi = float("nan"), float("nan"), float("nan")

        row: dict[str, Any] = {
            "acquisition_method": m,
            "n_campaigns": m_n,
            "n_certified": n_cert,
            "cert_rate": round(n_cert / float(m_n), 5),
            "cert_ci95_lo": round(cert_lo, 5),
            "cert_ci95_hi": round(cert_hi, 5),
            "restricted_mean": round(rm, 2),
            "rm_ci95_lo": round(rm_lo, 2),
            "rm_ci95_hi": round(rm_hi, 2),
            "capped_median": round(med, 2),
            "med_ci95_lo": round(med_lo, 2),
            "med_ci95_hi": round(med_hi, 2),
            "iqr_q25": round(float(q25), 2),
            "iqr_q75": round(float(q75), 2),
            "median_certified": round(med_ok, 2) if math.isfinite(med_ok) else None,
            "ratio_vs_cd": round(r_cd, 4) if math.isfinite(r_cd) else None,
            "ratio_vs_cd_ci95_lo": round(r_cd_lo, 4) if math.isfinite(r_cd_lo) else None,
            "ratio_vs_cd_ci95_hi": round(r_cd_hi, 4) if math.isfinite(r_cd_hi) else None,
            "kg_over_method": round(r_kg, 4) if math.isfinite(r_kg) else None,
            "kg_over_method_ci95_lo": round(r_kg_lo, 4) if math.isfinite(r_kg_lo) else None,
            "kg_over_method_ci95_hi": round(r_kg_hi, 4) if math.isfinite(r_kg_hi) else None,
            "false_certificates": n_err,
            "false_cert_cp95_upper": round(err_cp95_hi, 5),
            "err_among_certified": round(err_cert_rate, 5) if math.isfinite(err_cert_rate) else None,
            "err_among_cert_ci95_lo": round(ec_lo, 5) if math.isfinite(ec_lo) else None,
            "err_among_cert_ci95_hi": round(ec_hi, 5) if math.isfinite(ec_hi) else None,
            "mean_root_regret": round(reg_mean, 6),
            "regret_ci95_lo": round(reg_lo, 6),
            "regret_ci95_hi": round(reg_hi, 6),
            "max_root_regret": round(reg_max, 6),
            "discovery_median": round(disc_med, 2),
            "discovery_rate": round(n_disc / float(m_n), 5),
            "discovery_ci95_lo": round(disc_lo, 5),
            "discovery_ci95_hi": round(disc_hi, 5),
            "joint_coverage": round(jcov, 5) if math.isfinite(jcov) else None,
            "joint_cov_ci95_lo": round(jcov_lo, 5) if math.isfinite(jcov_lo) else None,
            "joint_cov_ci95_hi": round(jcov_hi, 5) if math.isfinite(jcov_hi) else None,
            "root_regret_bound_coverage": round(rcov, 5) if math.isfinite(rcov) else None,
            "rcov_ci95_lo": round(rcov_lo, 5) if math.isfinite(rcov_lo) else None,
            "rcov_ci95_hi": round(rcov_hi, 5) if math.isfinite(rcov_hi) else None,
            "mean_acq_ms_per_eval": round(float(np.mean(acq_ms_per_eval)), 4),
            "median_acq_ms_per_eval": round(float(np.median(acq_ms_per_eval)), 4),
            "mean_cert_time_s": round(float(np.mean(cert_s)), 4),
            "median_cert_time_s": round(float(np.median(cert_s)), 4),
            "mean_safeguard_rate": round(
                float(np.mean([float(r["safeguard_activations"]) / max(1.0, float(r["n_evaluations"])) for r in rows_m])),
                5,
            ),
            "mean_mixture_support": round(float(np.mean([float(r["mean_mixture_support"]) for r in rows_m])), 4),
            "mean_proxy_frac": round(float(np.mean([float(r["proxy_query_frac"]) for r in rows_m])), 5),
        }

        if m_hier is not None:
            _, h_rm_lo, h_rm_hi = _boot_mean_ci(evals, m_hier)
            row["hier_rm_ci95_lo"] = round(h_rm_lo, 2)
            row["hier_rm_ci95_hi"] = round(h_rm_hi, 2)
            if cd_evals is not None and uids is canon_uids:
                _, h_cd_lo, h_cd_hi = _boot_ratio_ci(evals, cd_evals, m_hier)
                row["hier_ratio_vs_cd_ci95_lo"] = round(h_cd_lo, 4)
                row["hier_ratio_vs_cd_ci95_hi"] = round(h_cd_hi, 4)
            if kg_evals is not None and uids is canon_uids:
                _, h_kg_lo, h_kg_hi = _boot_ratio_ci(kg_evals, evals, m_hier)
                row["hier_kg_over_m_ci95_lo"] = round(h_kg_lo, 4)
                row["hier_kg_over_m_ci95_hi"] = round(h_kg_hi, 4)

        if include_workflow_metrics:
            toks = np.array([float(r["total_tokens"]) for r in rows_m], dtype=np.float64)
            hf1 = np.array([float(r["heldout_f1"]) for r in rows_m], dtype=np.float64)
            hreg = np.array([float(r["heldout_regret"]) for r in rows_m], dtype=np.float64)
            tm, tm_lo, tm_hi = _boot_mean_ci(toks, m_boot)
            tmed, tmed_lo, tmed_hi = _boot_median_ci(toks, m_boot)
            tq25, tq75 = np.percentile(toks, [25.0, 75.0])
            f1_m, f1_lo, f1_hi = _boot_mean_ci(hf1, m_boot)
            hr_m, hr_lo, hr_hi = _boot_mean_ci(hreg, m_boot)
            row.update(
                {
                    "mean_tokens": round(tm, 1),
                    "mean_tokens_ci95_lo": round(tm_lo, 1),
                    "mean_tokens_ci95_hi": round(tm_hi, 1),
                    "median_tokens": round(tmed, 1),
                    "med_tokens_ci95_lo": round(tmed_lo, 1),
                    "med_tokens_ci95_hi": round(tmed_hi, 1),
                    "tokens_iqr_q25": round(float(tq25), 1),
                    "tokens_iqr_q75": round(float(tq75), 1),
                    "heldout_f1_mean": round(f1_m, 5),
                    "heldout_f1_ci95_lo": round(f1_lo, 5),
                    "heldout_f1_ci95_hi": round(f1_hi, 5),
                    "heldout_regret_mean": round(hr_m, 5),
                    "heldout_regret_ci95_lo": round(hr_lo, 5),
                    "heldout_regret_ci95_hi": round(hr_hi, 5),
                }
            )
            if kg_toks is not None and uids is canon_uids:
                tr_kg, tr_lo, tr_hi = _boot_ratio_ci(kg_toks, toks, m_boot)
                row["token_kg_over_method"] = round(tr_kg, 4)
                row["token_kg_over_method_ci95_lo"] = round(tr_lo, 4)
                row["token_kg_over_method_ci95_hi"] = round(tr_hi, 4)

        out_rows.append(row)
    return out_rows


def write_csv(path: Path, rows: Sequence[dict[str, Any]]) -> None:
    if not rows:
        return
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)


def write_campaign_records(out_dir: Path, stem: str, records: Sequence[dict[str, Any]]) -> tuple[Path, Path]:
    """Save standardized per-campaign records as both Parquet and CSV."""
    df = pd.DataFrame(records)
    for col in STANDARD_COLUMNS:
        if col not in df.columns:
            df[col] = np.nan
    ordered = list(STANDARD_COLUMNS) + [c for c in df.columns if c not in STANDARD_COLUMNS]
    df = df[ordered]
    pq_path = out_dir / f"{stem}.parquet"
    csv_path = out_dir / f"{stem}.csv"
    df.to_parquet(pq_path, index=False, compression="snappy")
    df.to_csv(csv_path, index=False)
    return pq_path, csv_path


def write_manifest(
    out_dir: Path,
    experiment_name: str,
    smoke: bool,
    elapsed_s: float,
    extra: dict[str, Any] | None = None,
) -> Path:
    files_map: dict[str, dict[str, Any]] = {}
    for fp in sorted(out_dir.iterdir()):
        if not fp.is_file() or fp.name == "manifest.json" or fp.name.endswith(".tmp"):
            continue
        files_map[fp.name] = {
            "sha256": sha256_file(fp),
            "bytes": fp.stat().st_size,
        }
    manifest: dict[str, Any] = {
        "experiment": experiment_name,
        "smoke": bool(smoke),
        "elapsed_s": round(float(elapsed_s), 2),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "files": files_map,
    }
    if extra:
        manifest.update(extra)
    mpath = out_dir / "manifest.json"
    mpath.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return mpath
