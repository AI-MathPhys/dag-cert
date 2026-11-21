"""Large known DAGs; generation and reward means are excluded from learners."""
import random
from dag_mcts.graph import DAG,Problem


def interval_problem(L=8192,A=128,shape='windows',seed=0,depth=0):
    rows=[list(range(1,A+1))]+[[] for _ in range(A+L)]
    leaves=list(range(A+1,A+L+1));cache={}
    permutation=list(range(L));random.Random(8431+L+A).shuffle(permutation)
    def node(lo,hi,permuted=False):
        if hi-lo==1:return leaves[permutation[lo] if permuted else lo]
        key=(lo,hi,permuted)
        if key not in cache:
            mid=(lo+hi)//2;children=[node(lo,mid,permuted),node(mid,hi,permuted)]
            cache[key]=len(rows);rows.append(children)
        return cache[key]
    def cover(l,h,permuted=False,lo=0,hi=None):
        if hi is None:hi=L
        if l<=lo and hi<=h:return [node(lo,hi,permuted)]
        mid=(lo+hi)//2;out=[]
        if l<mid:out+=cover(l,h,permuted,lo,mid)
        if h>mid:out+=cover(l,h,permuted,mid,hi)
        return out
    for a in range(A):
        if shape=='holes':
            l=a*L//A;h=(a+1)*L//A
            children=(cover(0,l) if l else [])+(cover(h,L) if h<L else [])
        elif shape=='disjoint':
            children=cover(a*L//A,(a+1)*L//A)
        else:
            j=a//2 if shape=='crossing' else a
            count=A//2 if shape=='crossing' else A
            width=(L+1)//2;start=j*(L-width)//(count-1)
            children=cover(start,start+width,shape=='crossing' and a%2==1)
        for _ in range(depth):v=len(rows);rows.append(children);children=[v]
        rows[a+1]=children
    # A low excluded block and a broad high region. Sampling sees only the oracle.
    means={leaf:(.2 if i<L//max(2,A) else .8) for i,leaf in enumerate(leaves)}
    return Problem(f'{shape}-{L}-{A}',DAG(rows),means)


def configurations():
    out=[]
    for shape in ('windows','holes','crossing','disjoint'):
        for L,A in ((8192,128),(32768,512)):
            for eps in (.1,.05):
                out.append(dict(id=f'implicit-{len(out):03d}',shape=shape,L=L,A=A,depth=4,
                    epsilon=eps,scale=round(4/eps),delta=.05,cadence=32,interval_cap=8,max_work=16000000))
    return out


def make_problem(c,seed):
    return interval_problem(c['L'],c['A'],c['shape'],seed,c.get('depth',0))
