Certifying UCT on DAGs: sharing, representation and pruning
The stronger-compiler study is in results/uct_frontier_v1.
Run python -B -m paper.uct_frontier_study --verify to check frozen sources.
Run python -B -m unittest tests.test_compiled_retirement for focused correctness tests.
The --audit and --memory flags regenerate independent replay files in a fresh copy
without coupling.jsonl or memory.jsonl, respectively. Existing files are never overwritten.
python -B -m paper.report_uct_frontier regenerates per-graph and equal-wall summaries.
Actual times include disposal; kernel-work counters exclude deallocation.

Selective backups on transposition-aware UCT rollouts
For the on-policy study run python -B -m paper.audit_uct_backup --replay and
python -B -m paper.uct_backup_gap --replay. These verify paths, root outputs, work and
stopping on every recorded case and seed. Real clock seconds are machine-specific.
python -B -m paper.report_uct_backup and its --gap option regenerate all per-case summaries.
The raw runs, protocols, and coupling digests are in results/uct_backup_v1 and paper/.

Supplementary decision-only pricing studies
Unzip into a new folder and change to that folder. In a fresh CPython 3.13
environment install the single dependency with python -m pip install -r requirements.txt.
One command replays the witness:

    python -B -m paper.replay_immediate_pricing

This checks all 32 reachability tapes and the reward intervals against the
stored certificate. The timed triples, per-graph work/time and protocol are
in results/immediate_pricing_v1 and paper/immediate_pricing_protocol.txt.
Run python -B -m paper.uniform_price_proof for the all-ranks proof.
The new entropy tapes, matched measurements and bounds are in results/uniform_price_v1.
Run python -B -m paper.report_uniform_price --replay to verify the recorded
work and rank consumption on one coupled tape per graph.
For the original fragmented proofs install Node.js (node on PATH) and run
python -B -m paper.check_fragment_sweep --seed 378001 and
python -B -m paper.fragment_shoulder. For the randomized expectation bounds
run python -B -m paper.validate_fragment_sign --replay. The six new held-out
graphs, their entropy tapes and their fixed predictions are in results/fragment_sign_v1.
For the matched layout experiment, run python -B -m paper.report_structural_price --replay.
This checks the frozen sign predictions, all matched endpoints and the simpler clipping bound,
and reruns one archived entropy tape for every layout and method. For the input family with
arbitrary complementary owner masks, run python -B -m paper.structural_price_family.
For the newer neighboring-prospect comparison, run python -B -m paper.report_neighbor_price --replay.
It replays full, immediate and deferred on one saved tape per layout and checks the extra booked
parent charges against the count-only bound. The protocol and all twelve fresh tapes are included.
For the sweep credit bound and larger graphs, run python -B -m paper.report_probe_credit --replay.
Run python -B -m paper.validate_probe_credit --replay to verify all independent rank prefixes,
their stopping scores and the simultaneous lower confidence bounds on the two means.
For the earlier policy-clock witness run python -B -m paper.replay_price_review.

To replay the paid prefix selectors, their actual baseline paths and their exact
information/access calculation, run python -B -m paper.replay_prefix_routing.
The new protocols and original raw records accompany the supplement.

python -B -m paper.report_index_repayment verifies the audited case records and
rebuilds the repair breakdown and transfer hindsight ceilings. For a fresh
counter replay, run the index_repayment_audit.main function with a new output
directory. This audit is untimed and keeps its monitoring costs off the solver.

The replay compares eager and batched histories, verifies the progress guard
and all six final work totals, then checks the reference and threshold paths
and the two exact finite-mixture calculations on every enumerated tape.
It reads the solver sources and input fixtures locally. The original witness
checker regenerates three small records inside results/repair_policy_clock_v1.
Use CPython 3.13 (the recorded run used 3.13.12). Elapsed time is machine-specific.

The five-way protocol and raw results are in paper/decision_price_protocol.txt
and results/decision_price_v1. python -m paper.report_decision_price regenerates
the primary summaries. To rerun the timed experiment from scratch, use a fresh
copy and move results/decision_price_v1 out of that copy first. The benchmark
intentionally refuses to overwrite a previous run.
