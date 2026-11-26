"""Frozen root-stopping and finer-grid experiments; existing kernels unchanged."""
import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import platform
import random
import struct
import time
from itertools import product

from .certified_uct import TranspositionUCT, UCTWork
from .demand_benchmark import retained_bytes, get_problem
from .maintenance_regimes import make_problem
from .persistent_queries import PersistentQueries
from .retired_bounds import CanonicalIntervals

METHODS = PersistentQueries.METHODS
CAP = 131072
CHECKPOINTS = (256, 1024, 4096, 16384, 65536, CAP)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def configurations(phase):
    if phase == 'completion':
        shapes = [dict(topology=s) for s in
                  ('flat16','flat128','lattice5','lattice8','merge64_16','unfold8_16','wine')]
        shapes += [dict(topology='ladder',width=16,depth=16,groups=8)]
        cases = [dict(shape,epsilon=e,scale=40,delta=.05)
                 for shape,e in product(shapes,(.1,.2))]
    elif phase == 'accuracy':
        shapes = [dict(topology=s) for s in ('flat16','lattice6','merge48_12')]
        shapes += [dict(topology='ladder',width=12,depth=12,groups=3)]
        cases = [dict(shape,epsilon=e,scale=round(m/e),delta=d,grid_margin=m)
                 for shape,e,m,d in product(shapes,(.2,.1,.05),(4,16,64),(.05,.01))]
    else:
        raise ValueError(phase)
    return [dict(c,id=f'{phase}-{i:03d}',cadence=32,phase=phase) for i,c in enumerate(cases)]


def requests(g, nodes, step, cadence):
    return list(dict.fromkeys((g.root,nodes[(step//cadence-1)%len(nodes)])))


class DPReference:
    """Independent exact integer DP; persistent valid answers are allowed."""
    def __init__(self,g,scale,tolerance,means):
        self.g,self.scale,self.tolerance=g,scale,tolerance
        self.low,self.high=[0]*len(g),[scale]*len(g)
        self.cache={};self.truth=g.optimal_values(means);self.invalid=[]
        self.requests=0

    def block(self,publications,nodes):
        for leaf,lo,hi in publications:
            self.low[leaf],self.high[leaf]=lo,hi
        low,high=self.low.copy(),self.high.copy()
        for v in reversed(self.g.order):
            if self.g.children[v]:
                low[v]=max(low[c] for c in self.g.children[v])
                high[v]=max(high[c] for c in self.g.children[v])
        answers=[]
        for v in nodes:
            self.requests+=1
            if v not in self.cache:
                row=self.g.children[v]
                a=max(range(len(row)),key=lambda a:low[row[a]])
                ok=all(high[c]<=low[row[a]]+self.tolerance for b,c in enumerate(row) if b!=a)
                result=(a,ok)
                if ok:
                    self.cache[v]=result
                    if self.truth[v]-self.truth[row[a]]>self.tolerance/self.scale+1e-12:
                        self.invalid.append((v,a))
            else:
                result=self.cache[v]
            answers.append((v,result))
        return answers


def update_observations(digest,observations):
    for path,reward in observations:
        digest.update(struct.pack('!Id',len(path),reward))
        digest.update(struct.pack('!'+'I'*len(path),*path))


def update_answers(digest,step,answers):
    digest.update(repr((step,answers)).encode())


def common_init(p,c,seed):
    g=p.graph;w=UCTWork()
    w.initialization+=16*len(g)+10*sum(map(len,g.children))+4*len(g.leaves)
    sampler=TranspositionUCT(g);oracle=p.oracle(seed)
    evidence=CanonicalIntervals(g,w,c['delta'],c['scale'])
    nodes=[v for v,row in enumerate(g.children) if len(row)>1]
    w.initialization+=len(g)
    return w,sampler,oracle,evidence,nodes


def common_work(w,sampler,oracle):
    return w.total+sampler.work.total-sampler.work.oracle_calls+getattr(oracle,'operations',sampler.work.oracle_calls)


def trace(p,c,seed,cap=CAP):
    """Measure common live caller; DP/hashing are outside all timed blocks."""
    g=p.graph;start=time.perf_counter()
    w,sampler,oracle,ev,nodes=common_init(p,c,seed)
    elapsed=time.perf_counter()-start
    setup_seconds=elapsed;setup_work=common_work(w,sampler,oracle)
    ref=DPReference(g,c['scale'],round(c['scale']*c['epsilon']),p.means)
    obs_hash=hashlib.sha256();ans_hash=hashlib.sha256();pub_hash=hashlib.sha256()
    blocks=[]
    for base in range(0,cap,c['cadence']):
        observations=[];pubs=[];step=min(base+c['cadence'],cap)
        start=time.perf_counter()
        for _ in range(base,step):
            path,reward=sampler.step(oracle)
            pair=ev.observe(path[-1],reward)
            if ev.conflict:raise AssertionError('Confidence conflict')
            if pair is not None:pubs.append((path[-1],*pair))
            observations.append((path,reward))
        queried=requests(g,nodes,step,c['cadence'])
        w.query_reads+=4;w.statistic_writes+=len(queried)
        elapsed+=time.perf_counter()-start
        expected=ref.block(pubs,queried)
        update_observations(obs_hash,observations);update_answers(ans_hash,step,expected)
        pub_hash.update(repr((step,pubs)).encode())
        blocks.append(dict(step=step,pubs=pubs,queries=queried,expected=expected,
                           common_seconds=elapsed,common_work=common_work(w,sampler,oracle)))
        if g.root in ref.cache:break
    return dict(blocks=blocks,observations=step,completed=g.root in ref.cache,
                setup_seconds=setup_seconds,setup_work=setup_work,common_seconds=elapsed,
                common_work=common_work(w,sampler,oracle),common_fields=asdict(w),
                sampler_fields=asdict(sampler.work),
                oracle_operations=getattr(oracle,'operations',sampler.work.oracle_calls),
                observations_sha256=obs_hash.hexdigest(),answers_sha256=ans_hash.hexdigest(),
                publications_sha256=pub_hash.hexdigest(),requests=ref.requests,invalid=ref.invalid)


def service_metadata(service,g,w):
    return dict(memory_bytes=retained_bytes(service,(g,w)),
                predicate_states=getattr(service.backend,'activations',None),
                predicate_edges=getattr(service.backend,'edge_examinations',None),
                requests=service.requests,hits=service.hits)


def integrated(p,c,seed,method,ref,cap=CAP):
    g=p.graph;start=time.perf_counter()
    w,sampler,oracle,ev,nodes=common_init(p,c,seed)
    service=PersistentQueries(g,w,method,c['scale'],round(c['scale']*c['epsilon']))
    elapsed=time.perf_counter()-start
    initial_memory=retained_bytes(service,(g,w));setup_seconds=elapsed
    setup_work=common_work(w,sampler,oracle)
    obs_hash=hashlib.sha256();ans_hash=hashlib.sha256();pub_hash=hashlib.sha256();points=[]
    stop=False
    for index,base in enumerate(range(0,cap,c['cadence'])):
        observations=[];pubs=[];step=min(base+c['cadence'],cap)
        start=time.perf_counter()
        for _ in range(base,step):
            path,reward=sampler.step(oracle);pair=ev.observe(path[-1],reward)
            if ev.conflict:raise AssertionError('Confidence conflict')
            if pair is not None:
                service.publish(path[-1],*pair);pubs.append((path[-1],*pair))
            observations.append((path,reward))
        queried=requests(g,nodes,step,c['cadence'])
        w.query_reads+=4;w.statistic_writes+=len(queried)
        answers=[(v,service.query(v)) for v in queried]
        stop=g.root in service.answers;w.query_reads+=1
        elapsed+=time.perf_counter()-start
        expected=ref['blocks'][index]
        assert answers==expected['expected'] and pubs==expected['pubs'],(method,step)
        update_observations(obs_hash,observations);update_answers(ans_hash,step,answers)
        pub_hash.update(repr((step,pubs)).encode())
        if step in CHECKPOINTS or stop or step==cap:
            points.append(dict(step=step,work=common_work(w,sampler,oracle),seconds=elapsed,completed=stop))
        if stop:break
    row=dict(method=method,mode='integrated',observations=step,completed=stop,
             seconds=elapsed,work=common_work(w,sampler,oracle),setup_seconds=setup_seconds,
             setup_work=setup_work,initial_memory_bytes=initial_memory,checkpoints=points,
             observations_sha256=obs_hash.hexdigest(),answers_sha256=ans_hash.hexdigest(),
             publications_sha256=pub_hash.hexdigest(),service_common_fields=asdict(w),
             sampler_fields=asdict(sampler.work),
             oracle_operations=getattr(oracle,'operations',sampler.work.oracle_calls))
    row.update(service_metadata(service,g,w))
    return row


def replay(p,c,method,ref):
    g=p.graph;start=time.perf_counter();w=UCTWork()
    service=PersistentQueries(g,w,method,c['scale'],round(c['scale']*c['epsilon']))
    elapsed=time.perf_counter()-start;setup_seconds=elapsed;setup_work=w.total
    initial_memory=retained_bytes(service,(g,w));points=[];ans_hash=hashlib.sha256()
    for block in ref['blocks']:
        step=block['step'];start=time.perf_counter()
        for leaf,lo,hi in block['pubs']:service.publish(leaf,lo,hi)
        answers=[(v,service.query(v)) for v in block['queries']]
        stop=g.root in service.answers;w.query_reads+=1
        elapsed+=time.perf_counter()-start
        assert answers==block['expected'],(method,step,answers,block['expected'])
        update_answers(ans_hash,step,answers)
        if step in CHECKPOINTS or stop or step==ref['observations']:
            points.append(dict(step=step,work=w.total+block['common_work'],
                               seconds=elapsed+block['common_seconds'],completed=stop))
    row=dict(method=method,mode='paired_components',observations=step,completed=stop,
             seconds=elapsed+ref['common_seconds'],maintenance_seconds=elapsed,
             common_seconds=ref['common_seconds'],work=w.total+ref['common_work'],
             maintenance_work=w.total,common_work=ref['common_work'],service_fields=asdict(w),
             setup_seconds=setup_seconds+ref['setup_seconds'],setup_work=setup_work+ref['setup_work'],
             maintenance_setup_seconds=setup_seconds,maintenance_setup_work=setup_work,
             initial_memory_bytes=initial_memory,checkpoints=points,
             observations_sha256=ref['observations_sha256'],publications_sha256=ref['publications_sha256'],
             answers_sha256=ans_hash.hexdigest())
    row.update(service_metadata(service,g,w))
    return row


def freeze_sources(protocol):
    paths=sorted(Path('dag_mcts').glob('*.py'))+[Path(protocol)]
    paths+=list(Path('data/uci').glob('*.zip'))
    return {str(p).replace('\\','/'):sha(p) for p in paths}


def run(out,phase,seeds=3,repeats=2,cap=CAP,limit=None):
    folder=Path(out);folder.mkdir(parents=True,exist_ok=False)
    configs=configurations(phase)
    if limit is not None:configs=configs[:limit]
    manifest=dict(phase=phase,configurations=configs,seeds=seeds,first_seed=105000,
                  repeats=repeats,cap=cap,methods=METHODS,completed=False,
                  sources=freeze_sources('paper/completion_accuracy_protocol.txt'),
                  python=platform.python_version(),platform=platform.platform())
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))
    warm=dict(cadence=32,epsilon=.2,scale=40,delta=.05)
    p=get_problem('trap');ref=trace(p,warm,99999,128)
    for m in METHODS:integrated(p,warm,99999,m,ref,128)
    random.Random(20261031).shuffle(configs)
    start=time.perf_counter();nr=0
    with (folder/'runs.jsonl').open('w') as output, (folder/'audits.jsonl').open('w') as audits:
        for ci,c in enumerate(configs,1):
            for seed in range(105000,105000+seeds):
                p=make_problem(c,seed);reference=None
                for rep in range(repeats):
                    if reference is None or phase=='accuracy':
                        reference=trace(p,c,seed,cap)
                        audit={k:v for k,v in reference.items() if k!='blocks'}
                        assert not audit['invalid']
                        audit.update(config=c['id'],seed=seed,repeat=rep)
                        audits.write(json.dumps(audit,separators=(',',':'))+'\n');audits.flush()
                    order=list(METHODS)
                    random.Random(f'{c["id"]}:{seed}:{rep}').shuffle(order)
                    for m in order:
                        row=(integrated(p,c,seed,m,reference,cap) if phase=='completion'
                             else replay(p,c,m,reference))
                        for f in ('observations','completed','observations_sha256','publications_sha256','answers_sha256','requests'):
                            assert row[f]==reference[f],(c['id'],seed,m,f)
                        row.update(config=c['id'],seed=seed,repeat=rep,
                                   nodes=len(p.graph),edges=sum(map(len,p.graph.children)),
                                   leaves=len(p.graph.leaves))
                        output.write(json.dumps(row,separators=(',',':'))+'\n');output.flush();nr+=1
                print(phase,ci,'/',len(configs),'seed',seed,'runs',nr,
                      'observations',reference['observations'],'completed',reference['completed'],
                      'elapsed',round(time.perf_counter()-start,1),flush=True)
    manifest.update(completed=True,runs=nr,
                    output_sha256={p.name:sha(p) for p in (folder/'runs.jsonl',folder/'audits.jsonl')})
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',required=True)
    parser.add_argument('--phase',choices=('completion','accuracy'),required=True)
    parser.add_argument('--seeds',type=int,default=3);parser.add_argument('--repeats',type=int,default=2)
    parser.add_argument('--cap',type=int,default=CAP);parser.add_argument('--limit',type=int)
    args=parser.parse_args();run(args.out,args.phase,args.seeds,args.repeats,args.cap,args.limit)
