# Publication validation, 2026-11-14

The repository was pushed and then cloned again from GitHub into a separate directory. A new virtual environment was created in that clone and populated solely from `requirements.lock`. Project import checks confirmed that the loaded `dag_mcts` and `paper` modules were inside that clone. No editable `fuse` installation or external research directory was used.

Validated commands and outcomes:

- `python -B reproduce.py quickcheck`: 21 tests passed; all source/data hashes passed; 11 summaries and five UCT tables matched; three UCT figure PDFs and eight appendix figure PDFs regenerated; the four-method example followed one observation stream and certified after 229 rollouts.
- `python -B reproduce.py benchmark --smoke --out build/fresh-smoke`: both UCT benchmark drivers completed their reduced cohorts, including a natural SameGame case and their completion stamps.
- `python -B reproduce.py replay --study all --out build/full-replay`: all **3,826,797** recorded rollout boundaries matched. This comprises 1,627,500 primary, 436,096 gap-follow-up, and 1,763,201 stronger-compiler rollouts. Archived paths, observations, recommendations, certificate boundaries, and charged work matched.
- Historical ancestor-repair and batching reports ran successfully from the fresh clone. Regenerated JSON values matched their saved summaries. `appendix-check` provides the same check in an isolated copy to avoid rewriting the frozen records.
- The separate manuscript repository compiled from its own fresh clone, with no dependency on this repository or `fuse`.

The initial cross-platform CI run passed on both Windows and Ubuntu; the workflow in `.github/workflows/reproduce.yml` additionally checks the isolated historical summaries.

This validation did **not** collect a new full timing cohort or repeat every historical appendix proof search. The paper's frozen timing data remain the reported measurements. Deterministic replay checks the current UCT trajectories and work; hardware-dependent runtime and memory are not expected to reproduce bit for bit.
