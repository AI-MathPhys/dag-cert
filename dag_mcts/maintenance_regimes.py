"""Frozen broad factorial and held-out workload definitions."""
from itertools import product
import math
import time
from .graph import DAG,Problem
from .application_search import FeatureTask
from .demand_benchmark import get_problem


def ladder(width=8,depth=8,groups=4):
    if width<2 or depth<1 or not 1<=groups<=width:raise ValueError('Invalid ladder dimensions')
    rows=[[]];means={}
    def leaf(value):
        v=len(rows);rows.append([]);means[v]=value;return v
    private=[leaf(.90+.02*(i%3)) for i in range(width)]
    sides=[leaf(.1+.02*(i%5)) for i in range(depth)]
    core=[leaf(.35+.30*i/7) for i in range(8)]
    def node(children):
        v=len(rows);rows.append(list(children));return v
    tails=[]
    for _ in range(groups):
        tail=node(core)
        for side in reversed(sides):tail=node([tail,side])
        tails.append(tail)
    rows[0]=[node([private[i],tails[i%groups]]) for i in range(width)]
    return Problem(f'ladder{width}_d{depth}_g{groups}',DAG(rows),means)


def configurations(phase):
    out=[]
    if phase=='development':
        for groups,depth,cadence,epsilon,burn in product((8,4,1),(2,8,24),(2,16,128),(.1,.2,.3),(0,32,256)):
            out.append(dict(topology='ladder',width=8,depth=depth,groups=groups,
                            cadence=cadence,epsilon=epsilon,burn=burn))
    elif phase=='holdout':
        shapes=[dict(topology=s) for s in ('lattice5','lattice7','lattice8','cross16','cross64',
                 'prefix64','flat16','flat128','merge64_16','unfold8_16','iris','wine')]
        shapes += [dict(topology='ladder',width=16,depth=4,groups=2),
                   dict(topology='ladder',width=16,depth=16,groups=8)]
        for shape in shapes:
            for cadence,epsilon,burn in ((4,.15,8),(4,.25,128),(64,.15,128),(64,.25,8)):
                out.append(dict(shape,cadence=cadence,epsilon=epsilon,burn=burn))
    else:raise ValueError(phase)
    return [dict(c,id=f'{phase}-{i:03d}',phase=phase) for i,c in enumerate(out)]


def make_problem(c,seed):
    if c['topology']=='ladder':return ladder(c['width'],c['depth'],c['groups'])
    if c['topology'] in ('iris','wine'):return FeatureTask(c['topology'],seed)
    return get_problem(c['topology'])


FEATURES=('log_nodes','log_edges','max_depth','shared_internal_fraction',
          'log_cadence','epsilon','log_burn')


def features(g,c):
    internal=shared=edges=0;max_depth=0
    for v,row in enumerate(g.children):
        edges+=len(row);max_depth=max(max_depth,g.depth[v])
        if row:
            internal+=1
            shared+=len(g.parents[v])>1
    return dict(log_nodes=math.log2(len(g)),log_edges=math.log2(max(1,edges)),
                max_depth=max_depth,shared_internal_fraction=shared/max(1,internal),
                log_cadence=math.log2(c['cadence']),epsilon=c['epsilon'],log_burn=math.log2(1+c['burn']))


class CostedOracle:
    """Actual CPU arithmetic; outcome stream and RNG calls are unchanged."""
    def __init__(self,inner,burn,seed):
        self.inner,self.burn,self.state,self.burn_operations=inner,burn,seed,0
        self.seconds=0.
    @property
    def operations(self):return self.burn_operations+getattr(self.inner,'operations',0)
    def sample(self,leaf):
        start=time.perf_counter()
        x=self.state
        for _ in range(self.burn):x=(1664525*x+1013904223)&0xffffffff
        self.state=x;self.burn_operations+=4*self.burn
        result=self.inner.sample(leaf)
        self.seconds+=time.perf_counter()-start
        return result
