"""Paid allocation and valid geometric-inspection confidence controls."""
import math

from dag_mcts.certified_uct import TranspositionUCT,UCTWork
from dag_mcts.retired_bounds import CanonicalIntervals
from dag_mcts.persistent_queries import PersistentQueries

SAMPLERS=('uct','lazy_uct','uniform','directed')
BOUNDS=('H','G')
METHODS=tuple(f'{s}_{b}' for s in SAMPLERS for b in BOUNDS)


class GeometricIntervals(CanonicalIntervals):
    """Union bound over predetermined local inspections, indexed by j not n."""
    def __init__(self,graph,work,delta=.05,scale=40):
        super().__init__(graph,work,delta,scale)
        self.inspections=[0]*len(graph);work.initialization+=len(graph)

    def observe(self,leaf,reward):
        if self.graph.children[leaf] or not math.isfinite(reward) or not 0<=reward<=1:
            raise ValueError('Need a bounded canonical terminal observation')
        self.counts[leaf]+=1;self.sums[leaf]+=reward
        w=self.work;w.oracle_calls+=1;w.statistic_writes+=2;w.confidence_work+=1
        n=self.counts[leaf]
        if n<self.next_count[leaf]:return None
        self.inspections[leaf]+=1;j=self.inspections[leaf]
        self.next_count[leaf]=n+(n+3)//4;self.evaluations+=1
        w.statistic_writes+=5;w.confidence_work+=8
        radius=math.sqrt((self.log_constant+2*math.log(j))/(2*n))
        lo=max(self.lower[leaf],self.sums[leaf]/n-radius,0.)
        hi=min(self.upper[leaf],self.sums[leaf]/n+radius,1.)
        self.lower[leaf],self.upper[leaf]=lo,hi
        if lo>hi:self.conflict=True;return None
        if self.scale!=1:
            lo=max(0,math.floor(math.nextafter(self.scale*lo,-math.inf)))
            hi=min(self.scale,math.ceil(math.nextafter(self.scale*hi,math.inf)))
            w.confidence_work+=4
        return lo,hi


class RoutedSampler:
    """Uniform or bound-directed terminal choice, with actual paid traversal."""
    def __init__(self,g,w,service,mode):
        if mode not in ('uniform','directed'):raise ValueError(mode)
        self.g,self.work,self.service,self.mode=g,w,service,mode
        self.parent=[-1]*len(g);self.calls=self.cursor=self.target_turn=0
        self.pair=(g.leaves[0],g.leaves[0]);self.forced=0
        w.initialization+=len(g)+8
        for v in g.order:
            for c in g.children[v]:
                w.edge_reads+=1;w.query_reads+=1
                if self.parent[c]==-1:self.parent[c]=v;w.statistic_writes+=1

    def _witness(self,v,lower):
        b=self.service.backend;w=self.work
        while self.g.children[v]:
            row=self.g.children[v]
            if lower:
                a=b.leader[v];w.query_reads+=2
            else:
                a=max(range(len(row)),key=lambda a:b.upper[row[a]])
                w.query_reads+=2*len(row);w.score_evaluations+=len(row)
            v=row[a];w.edge_reads+=1
        return v

    def prepare(self):
        if self.mode!='directed':return
        b=self.service.backend;w=self.work;b.flush();w.query_reads+=3
        row=self.g.children[self.g.root];a=b.leader[self.g.root]
        rivals=[i for i in range(len(row)) if i!=a]
        w.query_reads+=len(row);w.statistic_writes+=len(rivals)
        rival=max(rivals,key=lambda i:b.upper[row[i]]) if rivals else a
        w.query_reads+=2*len(rivals);w.score_evaluations+=len(rivals)
        self.pair=(self._witness(row[a],True),self._witness(row[rival],False))
        w.statistic_writes+=2

    def step(self,oracle):
        w=self.work;w.query_reads+=3
        if self.mode=='uniform' or self.calls%8==7:
            leaf=self.g.leaves[self.cursor%len(self.g.leaves)];self.cursor+=1
            if self.mode=='directed':self.forced+=1
            w.statistic_writes+=2
        else:
            leaf=self.pair[self.target_turn%2];self.target_turn+=1;w.statistic_writes+=1
        path=[leaf];v=leaf;w.statistic_writes+=1
        while v!=self.g.root:
            v=self.parent[v];path.append(v);w.edge_reads+=1;w.statistic_writes+=1
        path.reverse();w.statistic_writes+=len(path)
        self.calls+=1;w.statistic_writes+=1
        return tuple(path),oracle.sample(leaf)


class Search:
    def __init__(self,p,c,seed,method):
        self.g=p.graph;self.work=UCTWork();w=self.work;g=self.g
        w.initialization+=16*len(g)+10*sum(map(len,g.children))+4*len(g.leaves)
        self.service=PersistentQueries(g,w,'bucket',c['scale'],round(c['scale']*c['epsilon']))
        self.sampling,self.bound=method.rsplit('_',1)
        self.ev=(CanonicalIntervals if self.bound=='H' else GeometricIntervals)(g,w,c['delta'],c['scale'])
        self.sampler=(TranspositionUCT(g,lazy=self.sampling=='lazy_uct') if self.sampling in ('uct','lazy_uct')
                      else RoutedSampler(g,w,self.service,self.sampling))
        self.oracle=p.oracle(seed);self.calls=0
        self.nodes=[v for v,row in enumerate(g.children) if len(row)>1];w.initialization+=len(g)

    @property
    def total_work(self):
        # CanonicalIntervals already charges exactly one observation.
        extra=(self.sampler.work.total-self.sampler.work.oracle_calls if self.sampling in ('uct','lazy_uct') else 0)
        return self.work.total+extra

    def block(self,cadence):
        if self.sampling=='directed':self.sampler.prepare()
        pubs=[];observations=[]
        for _ in range(cadence):
            path,reward=self.sampler.step(self.oracle);self.calls+=1
            pair=self.ev.observe(path[-1],reward)
            if self.ev.conflict:raise ArithmeticError('Confidence interval conflict: stop certification')
            if pair is not None:
                self.service.publish(path[-1],*pair);pubs.append((path[-1],*pair))
            observations.append((path,reward))
        queried=list(dict.fromkeys((self.g.root,self.nodes[(self.calls//cadence-1)%len(self.nodes)])))
        self.work.query_reads+=4;self.work.statistic_writes+=len(queried)
        answers=[(v,self.service.query(v)) for v in queried]
        stopped=self.g.root in self.service.answers;self.work.query_reads+=1
        return pubs,observations,queried,answers,stopped


def configurations():
    shapes=[dict(topology=t) for t in ('flat16','flat128','lattice5','lattice8','merge48_12')]
    shapes.append(dict(topology='ladder',width=12,depth=12,groups=3))
    out=[]
    for shape in shapes:
        for eps in (.1,.05):
            out.append(dict(shape,epsilon=eps,scale=round(4/eps),delta=.05,cadence=32,
                id=f'sampling-{len(out):03d}',max_work=64000000 if shape['topology']=='lattice8' and eps==.05 else 16000000))
    return out
