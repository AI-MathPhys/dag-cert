"""Search DAG structures, root supports, and sequential problem interfaces."""
from __future__ import annotations

from collections.abc import Mapping, Sequence

import numpy as np

from dagcert._core.graph import DAG, LeafOracle, Problem, feature_lattice, trap
from dagcert._core.v7_bayesian_ucd import SupportStructure


class SearchDAG(DAG):
    """Finite rooted all-MAX search DAG with ergonomic constructors and support analytics.

    Each root action ``a`` retains a nonempty set of reachable canonical terminals
    ``S(a) subseteq Z``. Distinct root actions may share downstream outcomes (transpositions),
    and ``SupportStructure(dag)`` precomputes the support/complement index arrays needed for
    Joint Root Certification and CD-Joint acquisition.
    """

    @classmethod
    def from_supports(
        cls,
        supports: Sequence[Sequence[int]],
        action_labels: Sequence[str] | None = None,
        leaf_labels: Sequence[str] | None = None,
    ) -> SearchDAG:
        """Build a canonical two-layer root-to-terminal DAG from root action support sets.

        Parameters
        ----------
        supports:
            Sequence of length ``K`` where ``supports[a]`` lists the canonical terminal indices
            (integers in ``0..M-1``) reachable from root action ``a``.
        action_labels:
            Optional human-readable names for the ``K`` root actions.
        leaf_labels:
            Optional human-readable names for the ``M`` canonical terminals.
        """
        if not supports:
            raise ValueError("supports must contain at least one root action")
        norm_supports = [sorted(set(int(z) for z in sup)) for sup in supports]
        if any(len(sup) == 0 for sup in norm_supports):
            raise ValueError("every root action must have a nonempty terminal support")
        all_leaves = sorted({z for sup in norm_supports for z in sup})
        if all_leaves[0] < 0 or all_leaves != list(range(len(all_leaves))):
            raise ValueError("terminal indices in supports must form a contiguous range 0..M-1")

        k = len(norm_supports)
        m = len(all_leaves)
        leaf_offset = 1 + k
        children: list[tuple[int, ...]] = [tuple(range(1, 1 + k))]
        for sup in norm_supports:
            children.append(tuple(leaf_offset + z for z in sup))
        for _ in range(m):
            children.append(())

        a_lbls = list(action_labels) if action_labels is not None else [f"action_{a}" for a in range(k)]
        z_lbls = list(leaf_labels) if leaf_labels is not None else [f"leaf_{z}" for z in range(m)]
        if len(a_lbls) != k:
            raise ValueError(f"Expected {k} action_labels, got {len(a_lbls)}")
        if len(z_lbls) != m:
            raise ValueError(f"Expected {m} leaf_labels, got {len(z_lbls)}")

        return cls(children, root=0, labels=["root", *a_lbls, *z_lbls])

    @classmethod
    def from_edges(
        cls,
        children: Sequence[Sequence[int]],
        root: int = 0,
        labels: Sequence[str] | None = None,
    ) -> SearchDAG:
        """Construct a general multi-stage rooted all-MAX DAG from adjacency lists."""
        return cls(children, root=root, labels=labels)

    def root_supports(self) -> tuple[np.ndarray, ...]:
        """Return each root action's reachable terminal indices in canonical ``0..M-1`` order."""
        return SupportStructure(self).supports

    def root_regrets(self, leaf_means: Sequence[float] | np.ndarray | Mapping[int, float]) -> np.ndarray:
        """Compute exact true root-decision regret ``r_mu(a) = mu_* - V(a)`` for every root action."""
        ss = SupportStructure(self)
        if isinstance(leaf_means, Mapping):
            mu = np.array([float(leaf_means[lf]) for lf in ss.leaves], dtype=np.float64)
        else:
            mu = np.asarray(leaf_means, dtype=np.float64)
            if len(mu) != ss.m:
                raise ValueError(f"Expected {ss.m} leaf means, got {len(mu)}")
        v_star = float(np.max(mu))
        return np.array([max(0.0, v_star - float(np.max(mu[sup]))) for sup in ss.supports], dtype=np.float64)

    def support_overlap_matrix(self) -> np.ndarray:
        """Pairwise Jaccard overlap matrix across the ``K`` root-action supports."""
        ss = SupportStructure(self)
        sets = [set(int(i) for i in sup) for sup in ss.supports]
        mat = np.zeros((ss.k, ss.k), dtype=np.float64)
        for i in range(ss.k):
            for j in range(ss.k):
                union = len(sets[i] | sets[j])
                mat[i, j] = (len(sets[i] & sets[j]) / union) if union else 0.0
        return mat


__all__ = [
    "DAG",
    "LeafOracle",
    "Problem",
    "SearchDAG",
    "SupportStructure",
    "feature_lattice",
    "trap",
]
