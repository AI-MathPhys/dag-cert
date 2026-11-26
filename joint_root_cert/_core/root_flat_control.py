"""Strong root-only control: compile terminal incidence for every root action.

This deliberately allows O(root_degree * leaves) space, outside live-cut's
linear-memory contract. Compilation and all evidence processing are charged.
Existing frozen replay sources are not changed by this additional control.
"""
import csv
import hashlib
import json
from pathlib import Path
import random
import struct
import time

from .certified_uct import UCTWork
from .maintenance_replay import build_trace, trace_digest
from .retired_bounds import CanonicalIntervals, RetiredBounds


class FlatGraph:
    def __init__(self, children):self.children=tuple(map(tuple,children));self.root=0
    def __len__(self):return len(self.children)


class FlatReplay:
    def __init__(self, graph, scale=1, geometric=False):
        self.work=UCTWork();self.evidence=CanonicalIntervals(graph,self.work,scale=scale,geometric=geometric)
        degree=len(graph.children[graph.root]);self.mapping=[-1]*len(graph)
        self.work.initialization+=len(graph)
        if not degree:
            flat=FlatGraph([()]);self.mapping[graph.root]=0
        else:
            for i,leaf in enumerate(graph.leaves):self.mapping[leaf]=degree+1+i
            rows=[list(range(1,degree+1))]+[[] for _ in range(degree)]+[[] for _ in graph.leaves]
            self.work.initialization+=degree+len(graph.leaves)+len(rows)
            for a,start in enumerate(graph.children[graph.root]):
                seen=[False]*len(graph);pending=[start]
                self.work.initialization+=len(graph)+1
                while pending:
                    v=pending.pop();self.work.initialization+=2
                    if seen[v]:continue
                    seen[v]=True;self.work.initialization+=1
                    if graph.children[v]:
                        pending.extend(graph.children[v]);self.work.initialization+=2*len(graph.children[v])+1
                    else:
                        rows[a+1].append(self.mapping[v]);self.work.initialization+=3
            flat=FlatGraph(rows)
            self.work.initialization+=len(rows)+sum(map(len,rows))
        self.compiled_edges=sum(map(len,flat.children));self.compiled_nodes=len(flat)
        self.bounds=RetiredBounds(flat,self.work,'eager',scale)

    def step(self,leaf,reward):
        endpoints=self.evidence.observe(leaf,reward)
        if endpoints is not None:self.bounds.publish(self.mapping[leaf],*endpoints)

    def query(self):return self.bounds.query()


def measure(p,trace,scale,geometric):
    start=time.perf_counter();run=FlatReplay(p.graph,scale,geometric);query=run.query()
    seconds=time.perf_counter()-start;init=seconds
    first=0 if query[1]<=.05 else None
    fw=run.work.total if first==0 else None;fs=seconds if first==0 else None
    h=hashlib.sha256();h.update(struct.pack('!qddd',*query))
    for i,(leaf,reward) in enumerate(trace,1):
        start=time.perf_counter();run.step(leaf,reward);query=run.query();seconds+=time.perf_counter()-start
        h.update(struct.pack('!qddd',*query))
        assert not run.evidence.conflict
        if first is None and query[1]<=.05:first,fw,fs=i,run.work.total,seconds
    return dict(method='flat_eager',observations=len(trace),queries=len(trace)+1,scale=scale,geometric=int(geometric),
                work=run.work.total,seconds=seconds,initialization_seconds=init,first_certificate=first,
                certificate_work=fw,certificate_seconds=fs,root_action=query[0],gap=query[1],output_sha256=h.hexdigest(),
                messages=run.bounds.messages,retired=0,dead_nodes=0,interval_evaluations=run.evidence.evaluations,
                compiled_nodes=run.compiled_nodes,compiled_edges=run.compiled_edges)


def main():
    root=Path(__file__).resolve().parents[1];out=root/'results/maintenance_flat_control';out.mkdir(exist_ok=True)
    rows=[]
    # Post-primary stronger control, with fresh timed matching live-cut repeats.
    # Only one representative primary seed; structural timings use three repeats.
    from .maintenance_replay import run_replay
    sources={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((root/'dag_mcts').glob('*.py'))}
    for source in ('maintenance_replay','maintenance_structural'):
        old=list(csv.DictReader((root/'results'/source/'runs.csv').open(newline='')))
        selected=[r for r in old if r['method']=='live' and (source=='maintenance_structural' or r['seed']=='6000')]
        cache={}
        for ref in selected:
            key=(ref['spec'],ref['policy'],int(ref['seed']))
            if key not in cache:cache[key]=build_trace(*key,8192)
            p,trace,_=cache[key];scale=int(ref['scale']);geo=bool(int(ref['geometric']))
            methods=['flat_eager','live']
            random.Random(int(ref['seed'])+scale+sum(map(ord,ref['spec']))+104729*int(ref['repeat'])).shuffle(methods)
            for method in methods:
                if method=='flat_eager':
                    measure(p,trace[:64],scale,geo);r=measure(p,trace,scale,geo)
                else:
                    run_replay(p,trace[:64],'live',scale,geo);r=run_replay(p,trace,'live',scale,geo)
                    r.update(compiled_nodes=len(p.graph),compiled_edges=sum(map(len,p.graph.children)))
                assert r['output_sha256']==ref['output_sha256']
                assert str(r['first_certificate'] if r['first_certificate'] is not None else '')==ref['first_certificate']
                if method=='live':assert r['work']==int(ref['work'])
                r.update(spec=ref['spec'],policy=ref['policy'],seed=ref['seed'],repeat=ref['repeat'],source=source,
                         trace_sha256=trace_digest(trace))
                rows.append(r)
            print(source,ref['spec'],scale,ref['repeat'],'flat queries identical',flush=True)
    fields=sorted(set().union(*(r.keys() for r in rows)))
    with (out/'runs.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader();writer.writerows(rows)
    (out/'metadata.json').write_text(json.dumps(dict(sources=sources,note='Stronger root-flattening control added after primary results; matched live timings rerun sequentially.'),indent=2)+'\n')


if __name__=='__main__':main()
