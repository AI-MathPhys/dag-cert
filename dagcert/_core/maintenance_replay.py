"""Frozen-observation comparison of root-certificate maintenance backends.

Traces are generated once, independently of the maintenance backend. Each method
recomputes the same canonical evidence; initialization, evidence, backup and the
same root queries are timed together. Trace generation, hashing and evaluation
are outside timing. Replay continues after certification to expose maintenance
cost; cost at the first certificate is also recorded separately.
"""
import argparse
import csv
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import random
import struct
import time

from .backprop_problems import problem_spec
from .certified_uct import TranspositionUCT, UCTWork
from .graph import DAG, Problem
from .retired_bounds import CanonicalIntervals, RetiredBounds
from .shared_backprop import SharedBounds


METHODS = ("full", "legacy_event", "eager", "cut", "live")


class Replay:
    def __init__(self, graph, method, scale=1, geometric=False, delta=.05):
        self.work = UCTWork()
        self.evidence = CanonicalIntervals(graph, self.work, delta, scale, geometric)
        self.method = method
        if method in ("full", "legacy_event"):
            self.bounds = SharedBounds(graph, self.work, epsilon=4/scale if scale != 1 else .05,
                                       delta=delta, mode="full" if method == "full" else "event",
                                       quantized=scale != 1)
        else:
            self.bounds = RetiredBounds(graph, self.work, method, scale)

    def step(self, leaf, reward):
        endpoints = self.evidence.observe(leaf, reward)
        if endpoints is not None:
            b = self.bounds
            if self.method in ("full", "legacy_event"):
                if b._publish(leaf, *endpoints):
                    b.leaf_changes += 1
                    if self.method == "legacy_event":
                        b._propagate(leaf)
                    else:
                        b.dp_passes += 1
                        for v in reversed(b.graph.order):
                            b._scan_node(v)
            else:
                b.publish(leaf, *endpoints)

    def query(self):
        # Exactly the same output contract and root scan for every backend.
        return RetiredBounds.query(self.bounds)


def shield(width, buried=False):
    """Distinct private witnesses, one shared nuisance stream, unresolved rival."""
    if width < 2:
        raise ValueError("width must be at least two")
    # root=0, aggregate=1, rival=2, shared x=3, private witnesses=4..4+m-1.
    witnesses = list(range(4, 4+width))
    parents = list(range(4+width, 4+2*width))
    rows = [[], parents, [], []]+[[] for _ in range(2*width)]
    means = {3:.3, **{v:(.1 if buried else .9) for v in witnesses}}
    for p, a in zip(parents, witnesses):
        rows[p] = [a, 3]
    b = len(rows); rows.append([]); means[b] = .1
    if buried:
        winner = len(rows); rows.append([]); means[winner] = .9
        rows[0] = [winner, 2, 1]; rows[2] = [b]
    else:
        rows[0] = [1, 2]; rows[2] = [3, b]
        winner = None
    p = Problem(f"{'buried' if buried else 'shield'}{width}", DAG(rows), means, tuple(means))
    return p, witnesses, 3, b, winner


def build_trace(spec, policy, seed, length=20000):
    if spec.startswith(("shield", "buried")):
        buried = spec.startswith("buried")
        width = int(spec[6:])
        p, witnesses, x, b, winner = shield(width, buried)
        # A deterministic, realizable stream; choose warm-up by the public radius,
        # not by any observed successes of a maintenance method.
        import math
        constant = math.log(math.pi**2*len(p.graph.leaves)/(.15))
        warm = 1
        while math.sqrt((constant+2*math.log(warm))/(2*warm)) > .125:
            warm += 1
        trace = []
        for a in ([winner] if winner is not None else [])+witnesses:
            trace.extend((a, p.means[a]) for _ in range(warm))
        trace.extend((x, p.means[x]) for _ in range(warm+4*width*width))
        # Certify only after the long shared-leaf phase; same stopping query.
        trace.extend((b, p.means[b]) for _ in range(warm))
        return p, trace, dict(policy="shielded", warm=warm, width=width)
    p = problem_spec(spec)
    oracle = p.oracle(seed)
    if policy == "uct":
        sampler = TranspositionUCT(p.graph)
        trace = []
        for _ in range(length):
            path, reward = sampler.step(oracle)
            trace.append((path[-1], reward))
    elif policy == "round_robin":
        leaves = list(p.graph.leaves); random.Random(seed).shuffle(leaves)
        trace = [(leaves[i % len(leaves)], oracle.sample(leaves[i % len(leaves)])) for i in range(length)]
    else:
        raise ValueError(policy)
    return p, trace, dict(policy=policy, warm=None, width=None)


def trace_digest(trace):
    h = hashlib.sha256()
    for leaf, value in trace:
        h.update(struct.pack("!qd", leaf, value))
    return h.hexdigest()


def run_replay(p, trace, method, scale, geometric, epsilon=.05, query_every=1):
    values = p.graph.optimal_values(p.means)
    def regret(query):
        return 0. if query[0] == -1 else values[p.graph.root]-values[p.graph.children[p.graph.root][query[0]]]
    start = time.perf_counter()
    replay = Replay(p.graph, method, scale, geometric)
    query = replay.query()
    init_seconds = time.perf_counter()-start
    seconds = init_seconds
    first = 0 if query[1] <= epsilon else None
    first_work = replay.work.total if first == 0 else None
    first_seconds = seconds if first == 0 else None
    digest = hashlib.sha256(); digest.update(struct.pack("!qddd", *query))
    query_count = 1
    false_certificates = int(query[1] <= epsilon and regret(query) > epsilon+1e-12)
    for step, (leaf, reward) in enumerate(trace, 1):
        start = time.perf_counter()
        replay.step(leaf, reward)
        due = step % query_every == 0 or step == len(trace)
        if due:
            query = replay.query()
        seconds += time.perf_counter()-start
        if due:
            query_count += 1
            digest.update(struct.pack("!qddd", *query))
            if first is None and not replay.evidence.conflict and query[1] <= epsilon:
                first, first_work, first_seconds = step, replay.work.total, seconds
            false_certificates += int(query[1] <= epsilon and regret(query) > epsilon+1e-12)
        if replay.evidence.conflict:
            raise AssertionError("Confidence alarm: do not treat this trace as certified")
    b = replay.bounds
    return dict(method=method, observations=len(trace), queries=query_count, scale=scale,
                geometric=int(geometric), work=replay.work.total, seconds=seconds,
                initialization_seconds=init_seconds, first_certificate=first,
                certificate_work=first_work, certificate_seconds=first_seconds,
                root_action=query[0], gap=query[1], output_sha256=digest.hexdigest(),
                messages=getattr(b,"messages",getattr(b,"parent_messages",0)),
                retired=getattr(b,"retired",0), dead_nodes=getattr(b,"dead_nodes",0),
                incoming_copies=getattr(b,"incoming_copies",0),
                interval_evaluations=replay.evidence.evaluations,
                false_certificate_queries=false_certificates, root_regret=regret(query),
                **{f"work_{k}":v for k,v in asdict(replay.work).items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problems", nargs="+", default=["merge64_8","fanout64","flat64","lattice6","lattice9"])
    parser.add_argument("--policies", nargs="+", default=["uct","round_robin"])
    parser.add_argument("--methods", nargs="+", default=list(METHODS))
    parser.add_argument("--seeds", type=int, default=10)
    parser.add_argument("--seed-offset", type=int, default=6000)
    parser.add_argument("--length", type=int, default=20000)
    parser.add_argument("--scales", nargs="+", type=int, default=[1,80])
    parser.add_argument("--geometric", action="store_true")
    parser.add_argument("--query-every", type=int, default=1)
    parser.add_argument("--repeats", type=int, default=1)
    parser.add_argument("--output", default="results/maintenance_replay")
    args = parser.parse_args()
    out = Path(args.output); out.mkdir(parents=True, exist_ok=True)
    source = Path(__file__).parent
    metadata = vars(args).copy()
    metadata.update(sources={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(source.glob("*.py"))},
                    timing="Summed initialization, observation/evidence/backup and query time; excludes trace generation, hashing and reporting.",
                    note="Every method receives identical observations and root-query times. Replay continues after certification.")
    (out/"metadata.json").write_text(json.dumps(metadata,indent=2)+"\n")
    rows = []; traces = []
    for spec in args.problems:
        policies = ["shielded"] if spec.startswith(("shield","buried")) else args.policies
        seeds = [args.seed_offset] if policies == ["shielded"] else range(args.seed_offset,args.seed_offset+args.seeds)
        for policy in policies:
            for seed in seeds:
                p, trace, extra = build_trace(spec,policy,seed,args.length)
                th = trace_digest(trace)
                traces.append(dict(spec=spec,seed=seed,trace_sha256=th,observations=len(trace),**extra))
                for scale in args.scales:
                    for repeat in range(args.repeats):
                        methods = list(args.methods)
                        random.Random(seed+scale+repeat*104729).shuffle(methods)
                        reference = None
                        for method in methods:
                            # Unmeasured warm-up runs the same code on a short prefix.
                            run_replay(p,trace[:min(64,len(trace))],method,scale,args.geometric,query_every=args.query_every)
                            row = run_replay(p,trace,method,scale,args.geometric,query_every=args.query_every)
                            signature=(row["output_sha256"],row["first_certificate"],row["interval_evaluations"])
                            if reference is None:reference=signature
                            assert signature==reference,(spec,policy,seed,scale,method,signature,reference)
                            row.update(spec=spec,policy=policy,seed=seed,repeat=repeat,trace_sha256=th,
                                       nodes=len(p.graph),edges=sum(map(len,p.graph.children)))
                            rows.append(row)
                        print(spec,policy,seed,scale,repeat,"root queries identical",flush=True)
                with (out/"runs.csv").open("w",newline="") as f:
                    writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
                (out/"traces.json").write_text(json.dumps(traces,indent=2)+"\n")
    print(f"Saved {len(rows)} replays.",flush=True)


if __name__=="__main__":
    main()
