"""Identical-observation, arbitrary-node-query compilation/maintenance study."""
import argparse
import csv
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import platform
import random
import struct
import sys
import time

from .backprop_problems import problem_spec
from .certified_uct import TranspositionUCT, UCTWork
from .demand_bounds import METHODS, make_backend
from .graph import DAG, Problem
from .retired_bounds import CanonicalIntervals


def prefix_problem(width, crossing=False):
    """O(m)-size overlapping prefix circuits; two conflicting orders if crossing."""
    chains = 2 if crossing else 1
    leaf_start = 1+chains*width
    leaves = list(range(leaf_start, leaf_start+width))
    rows = [list(range(1, leaf_start))]+[[] for _ in range(chains*width+width)]
    permutations = [list(range(width))]
    if crossing:
        # Structural permutation fixed independently of rewards/timing.
        order = list(range(width)); random.Random(1729+width).shuffle(order)
        permutations.append(order)
    for chain, order in enumerate(permutations):
        for i,j in enumerate(order):
            v = 1+chain*width+i
            rows[v] = ([v-1] if i else [])+[leaves[j]]
    means = {leaf:.2+.6*((i*37+11)%width)/max(1,width-1) for i,leaf in enumerate(leaves)}
    return Problem(('cross' if crossing else 'prefix')+str(width), DAG(rows), means)


def get_problem(spec):
    if spec.startswith('prefix'): return prefix_problem(int(spec[6:]))
    if spec.startswith('cross'): return prefix_problem(int(spec[5:]), True)
    return problem_spec(spec)


def make_trace(spec, policy, seed, length, cadence, query_mode='path'):
    p = get_problem(spec); oracle = p.oracle(seed)
    sampler = TranspositionUCT(p.graph) if policy=='uct' else None
    rng = random.Random(seed)
    leaves = list(p.graph.leaves); rng.shuffle(leaves)
    internals = [v for v,row in enumerate(p.graph.children) if row]
    events = []
    for i in range(length):
        if sampler:
            path, reward = sampler.step(oracle); leaf = path[-1]
        else:
            leaf = leaves[i % len(leaves)]; reward = oracle.sample(leaf); path = [p.graph.root]
        queries = []
        if (i+1)%cadence==0 or i+1==length:
            if query_mode=='root': queries=[p.graph.root]
            elif query_mode=='local': queries=[internals[-1] if len(internals)>1 else p.graph.root]
            elif query_mode=='path':
                queries = list(dict.fromkeys(path[:-1] if sampler else [p.graph.root, rng.choice(internals)]))
                if p.graph.root not in queries: queries.insert(0,p.graph.root)
            else: raise ValueError(query_mode)
        events.append((leaf,reward,tuple(queries)))
    return p, events


def trace_hash(events):
    h=hashlib.sha256()
    for leaf,reward,queries in events:
        h.update(struct.pack('!qdq',leaf,reward,len(queries)))
        for v in queries: h.update(struct.pack('!q',v))
    return h.hexdigest()


def retained_bytes(obj, excluded=()):
    """Python object graph size, excluding the common input DAG/work object.

    Not peak RSS, not a theoretical word count, and not included in timing.
    """
    seen={id(x) for x in excluded}; pending=[obj]; total=0
    while pending:
        x=pending.pop()
        if id(x) in seen: continue
        seen.add(id(x)); total+=sys.getsizeof(x)
        if isinstance(x,dict): pending.extend(x.keys());pending.extend(x.values())
        elif isinstance(x,(list,tuple,set,frozenset)): pending.extend(x)
        elif hasattr(x,'__dict__'): pending.append(vars(x))
    return total


def full_query(graph, lower, upper, node, scale):
    lo,hi=lower.copy(),upper.copy()
    for v in reversed(graph.order):
        if graph.children[v]:
            lo[v]=max(lo[c] for c in graph.children[v]);hi[v]=max(hi[c] for c in graph.children[v])
    row=graph.children[node]
    if not row:return (-1,0.,lo[node]/scale,hi[node]/scale)
    a=max(range(len(row)),key=lambda i:lo[row[i]])
    rival=max((hi[c] for i,c in enumerate(row) if i!=a),default=lo[node])
    return a,max(0.,(rival-lo[row[a]])/scale),lo[node]/scale,hi[node]/scale


def measure(p, events, method, scale, audit=False):
    start=time.perf_counter()
    work=UCTWork(); evidence=CanonicalIntervals(p.graph,work,scale=scale)
    backend=make_backend(p.graph,work,method,scale)
    init_seconds=time.perf_counter()-start; init_work=work.total
    elapsed=init_seconds; digest=hashlib.sha256()
    first=None; cert_work=cert_seconds=None; queries=0; false=0; changed=0
    truth=p.graph.optimal_values(p.means)
    lows,highs=[0]*len(p.graph),[scale]*len(p.graph)
    final=(-1,1.,0.,1.); root_queries=0; outputs=[]
    for step,(leaf,reward,requests) in enumerate(events,1):
        start=time.perf_counter()
        ends=evidence.observe(leaf,reward)
        if ends is not None: backend.publish(leaf,*ends)
        answers=[(node,backend.query(node)) for node in requests]
        elapsed+=time.perf_counter()-start
        if evidence.conflict:raise AssertionError('Conflicting confidence intervals')
        if ends is not None:
            changed+=int(ends!=(lows[leaf],highs[leaf]));lows[leaf],highs[leaf]=ends
        for node,q in answers:
            queries+=1;digest.update(struct.pack('!qqddd',node,*q))
            if audit:assert q==full_query(p.graph,lows,highs,node,scale),(method,step,node,q)
            row=p.graph.children[node]
            regret=0. if not row else truth[node]-truth[row[q[0]]]
            false+=int(q[1]<=.05 and regret>.05+1e-12)
            if node==p.graph.root:
                root_queries+=1;final=q
                if first is None and q[1]<=.05:first,cert_work,cert_seconds=step,work.total,elapsed
        if answers:
            outputs.append((step,work.total,elapsed,final[0],final[1]))
    return dict(method=method,scale=scale,observations=len(events),queries=queries,root_queries=root_queries,
                changed_inputs=changed,work=work.total,seconds=elapsed,initialization_work=init_work,
                initialization_seconds=init_seconds,first_certificate=first,certificate_work=cert_work,
                certificate_seconds=cert_seconds,output_sha256=digest.hexdigest(),false_certificate_queries=false,
                backend_bytes=retained_bytes(backend,(p.graph,work)),
                cover_entries=getattr(backend,'cover_entries',None),run_count=getattr(backend,'run_count',None),
                compiled_edges=getattr(backend,'compiled_edges',None),merge_inputs=getattr(backend,'merge_inputs',None),
                refreshed=getattr(backend,'refreshed',None),retired=getattr(backend,'retired',None),
                **{f'work_{k}':v for k,v in asdict(work).items()}),outputs


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--problems',nargs='+',default=['merge64_8','flat64','lattice6','lattice9','prefix64','cross64'])
    parser.add_argument('--policies',nargs='+',default=['uct','round_robin'])
    parser.add_argument('--methods',nargs='+',default=list(METHODS))
    parser.add_argument('--scales',nargs='+',type=int,default=[1,80])
    parser.add_argument('--cadences',nargs='+',type=int,default=[1,32])
    parser.add_argument('--seeds',type=int,default=3)
    parser.add_argument('--seed-offset',type=int,default=7100)
    parser.add_argument('--length',type=int,default=2048)
    parser.add_argument('--query-mode',choices=['root','path','local'],default='path')
    parser.add_argument('--repeats',type=int,default=1)
    parser.add_argument('--audit',action='store_true')
    parser.add_argument('--output',default='results/demand_primary')
    args=parser.parse_args();out=Path(args.output);out.mkdir(parents=True,exist_ok=True)
    root=Path(__file__).resolve().parents[1]
    metadata=vars(args).copy()
    metadata.update(python=sys.version,platform=platform.platform(),
       timing='Sequential per-event backend/evidence/query time plus initialization; excludes allocation, rewards, validation, hashing and memory measurement. Not end-to-end search time.',
       memory='Retained Python backend object bytes, excluding supplied graph and work counter; not peak RSS.',
       source_sha256={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((root/'dag_mcts').glob('*.py'))})
    (out/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    rows=[];traces=[]
    for spec in args.problems:
      for policy in args.policies:
       for seed in range(args.seed_offset,args.seed_offset+args.seeds):
        for cadence in args.cadences:
         p,events=make_trace(spec,policy,seed,args.length,cadence,args.query_mode)
         th=trace_hash(events); traces.append(dict(spec=spec,policy=policy,seed=seed,cadence=cadence,trace_sha256=th))
         for scale in args.scales:
          for repeat in range(args.repeats):
           methods=list(args.methods);random.Random(seed+scale+cadence+repeat*104729).shuffle(methods)
           reference=None
           for method in methods:
            measure(p,events[:min(32,len(events))],method,scale)
            row,_=measure(p,events,method,scale,args.audit)
            signature=(row['output_sha256'],row['first_certificate'])
            if reference is None:reference=signature
            assert signature==reference,(spec,policy,seed,cadence,scale,method,signature,reference)
            row.update(spec=spec,policy=policy,seed=seed,cadence=cadence,repeat=repeat,query_mode=args.query_mode,
                       trace_sha256=th,nodes=len(p.graph),edges=sum(map(len,p.graph.children)))
            rows.append(row)
           print(spec,policy,seed,cadence,scale,repeat,'identical queries',flush=True)
         with (out/'runs.csv').open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
         (out/'traces.json').write_text(json.dumps(traces,indent=2)+'\n')
    print('Saved',len(rows),'replays',flush=True)


if __name__=='__main__':main()
