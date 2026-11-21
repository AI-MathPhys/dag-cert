"""All-ranks proof for two interleaved supports with one shared terminal.

A layer indexes completed public blocks. Before the first trial only the
number of picks of the shared terminal instead of each exclusive side matters.
We overapproximate incumbent choices and pilot credit; all extrema are outward.
"""
import json
import math
from collections import defaultdict
from dataclasses import dataclass

from paper.immediate_pricing import ImmediateCompact
from paper.uniform_price_benchmark import DEST, config, interleaved, specs

LIMIT = 1024  # final probe; refuse to certify unless all paths launched by here


class Leaf:
    def __init__(self, reward, scale, log_ratio):
        self.reward, self.scale, self.log_ratio = reward, scale, log_ratio
        self.total = 0.
        self.band = (0.,1.)
        self.blocks = [(0, scale, self.total, ((),()))]
        self.upper_events = [0]

    def at(self, b):
        while len(self.blocks) <= b:
            lo, hi = self.band
            low, high = self.blocks[-1][:2]
            events = ([],[])
            n0 = 16*(len(self.blocks)-1)
            for n in range(n0+1,n0+17):
                self.total += self.reward
                radius = math.sqrt((n+1)/(2*n*n)*(self.log_ratio+.5*math.log1p(n)))
                lo = max(lo,self.total/n-radius,0.)
                hi = min(hi,self.total/n+radius,1.)
                a = max(0,math.floor(math.nextafter(self.scale*lo,-math.inf)))
                bkey = min(self.scale,math.ceil(math.nextafter(self.scale*hi,math.inf)))
                if a != low: events[0].append(max(a,low))
                if bkey != high: events[1].append(max(bkey,high))
                low,high = a,bkey
            self.band = lo,hi
            self.blocks.append((low,high,self.total,events))
            self.upper_events.append(self.upper_events[-1]+len(events[1]))
        return self.blocks[b]


class Exclusive:
    def __init__(self, leaves):
        self.leaves = leaves
        self.m = len(leaves)
        self.counts = [(1,)*self.m]
        self.winners = []

    def state(self,b):
        while len(self.winners) <= b-self.m:
            counts = self.counts[-1]
            highs = [leaf.at(n)[1] for leaf,n in zip(self.leaves,counts)]
            mx = max(highs)
            assert highs.count(mx)==1, 'nonunique exclusive witness after the sweep'
            j = highs.index(mx)
            self.winners.append(j)
            next_counts = list(counts)
            next_counts[j] += 1
            self.counts.append(tuple(next_counts))
        return self.counts[b-self.m], self.winners[b-self.m]


def scan_charge(keys):
    best, ties, writes = -1,0,0
    for v in reversed(keys):
        if v>best:
            writes += ties+1
            ties, best = 1,v
        elif v==best:
            writes += 1
            ties += 1
    return 3*len(keys)+writes


def group_lower(keys, pair, updates, inc, h):
    # Sibling subtrees partition the leaves outside j. Exclude the other hot leaf.
    leaves=len(keys)
    join=(pair[0]^pair[1]).bit_length()
    total=0
    for side,j in enumerate(pair):
        peer=pair[1-side]
        events=updates[side][3][0 if inc else 1]
        n=len(events)
        if n<4: continue
        prefix=[]
        prev=-1
        for depth in range(1,h+1):
            start=((j>>(depth-1))^1)<<(depth-1)
            stop=min(leaves,start+(1<<(depth-1)))
            prev=max(prev,max((keys[k] for k in range(start,stop) if k!=peer),default=-1))
            prefix.append(prev)
        def cursor(x):
            return sum(v<=x for v in prefix)
        def pull(x,y):
            cold=min(h,cursor(x)+1)
            return min(cold,join) if y>x else cold
        old=keys[peer]
        new=updates[1-side][0 if inc else 1]
        if pull(min(events),max(old,new)) == pull(max(events),min(old,new)): continue
        boundary=h if inc else 0
        kmin=n if cursor(events[-1])!=boundary else int(cursor(events[0])!=boundary)
        # Ignore positive cursor displacement. Only ambiguous groups enter this sum.
        total += 7*n+3*kmin-(32+3*n+4*h)
    return total


@dataclass
class Bounds:
    lower: int       # cumulative scan minus retention
    cmin: int        # running scan credit, excludes one-time cover setup
    cmax: int

    def merge(self, other):
        self.lower=min(self.lower,other.lower)
        self.cmin=min(self.cmin,other.cmin)
        self.cmax=max(self.cmax,other.cmax)


def verify(spec):
    p=interleaved(spec['m'],spec['seed'])
    cfg=config(spec)
    engine=ImmediateCompact(p,cfg,1)
    m=spec['m']
    M=2*m+1
    h=(M-1).bit_length()
    scale=cfg['K']
    leaves=[Leaf(p.means[x],scale,engine.ev.log_ratio) for x in p.graph.leaves]
    sides=[Exclusive(leaves[s:2*m:2]) for s in (0,1)]
    # Check the singletons and real cover order used by the production index.
    for a in range(2):
        out,ins=engine.idx.cover(a)
        for blocks,indices in ((out,list(range(1-a,2*m,2))),
                               (ins,[*range(a,2*m,2),2*m])):
            assert [v-engine.idx.ut.size for v in blocks]==indices[::-1]
    assert all(leaf.at(1)[1]<scale for leaf in leaves)
    max_shared=0
    # Certified lower bound on each exclusive maximum throughout the checked prefix.
    hot=[max(side.leaves,key=lambda l:l.reward) for side in sides]
    floor_hot=min(l.at(LIMIT)[1] for l in hot)
    while leaves[-1].at(max_shared)[1]>=floor_hot:
        max_shared+=1
    warm=m+max_shared
    # During the unexpanded prefix every updated upper strictly decreases.
    assert all(l.at(n+1)[1]<l.at(n)[1] for l in leaves for n in range(warm))
    assert max(l.at(warm)[0] for l in leaves)+engine.tol<floor_hot, 'possible warm return'
    scan=68*M+96
    cover_extra=2*(8*M+1)
    assert (5*M+1)*(warm+1)+cover_extra<8*scan
    def first_visit_floor(leaf):
        return sum(min(0,4*len(events)-32-4*h) for events in leaf.at(1)[3] if len(events)>=4)
    warm_floor=sum(first_visit_floor(l) for l in leaves[:-1])-4*max_shared*(16+4*h)
    states={(u,v,0):Bounds(warm_floor,(3*M+1)*(warm+1),(5*M+1)*(warm+1))
            for u in range(max_shared+1) for v in range(max_shared+1-u)}
    stops=defaultdict(list)
    visited=0
    for t in range(warm,LIMIT):
        q=t+1
        later={}
        cache={}
        for (u,v,pilots),bound in states.items():
            visited+=1
            if (u,v) not in cache:
                counts0,j0=sides[0].state(t-u)
                counts1,j1=sides[1].state(t-v)
                counts=[n for pair in zip(counts0,counts1) for n in pair]+[u+v]
                curr=[leaf.at(n) for leaf,n in zip(leaves,counts)]
                low,high=([s[i] for s in curr] for i in (0,1))
                js=[2*j0,2*j1+1]
                cache[u,v]=counts,low,high,js
            counts,low,high,js=cache[u,v]
            for a in (0,1):  # deliberately allow either orientation at every query
                assert high[js[1-a]]-max(low)>engine.tol, 'possible return before launch'
                next_pilots={pilots}
                if q>=4 and (q & (q-1))==0 and max(low)>engine.tol:
                    req=8*(pilots+1)*scan
                    if bound.cmax+cover_extra>=req:
                        # All pre-seal draws accrue 28 common block units plus 8 for publish.
                        revisions=sum(l.upper_events[n] for l,n in zip(leaves,counts))
                        floor_x=36*32*t+(3*M+1)*q+12*revisions
                        assert floor_x//3>=2*(bound.cmax+cover_extra), ('unclipped',q,a,floor_x//3,2*(bound.cmax+cover_extra))
                        engine.ev.counts={x:16*n for x,n in zip(p.graph.leaves,counts)}
                        engine.ev.sums={x:l.at(n)[2] for x,l,n in zip(p.graph.leaves,leaves,counts)}
                        engine.idx.lower,engine.idx.upper=low,high
                        engine.idx.q=q
                        engine.idx.stats['misses']=q
                        engine.point=(a,False,max(low),None,None)
                        plan=engine.plan()
                        next_pilots=set()
                        if bound.cmin<req: next_pilots.add(pilots)
                        if plan is None or plan.partial_estimate>plan.earnings:
                            next_pilots.add(pilots+1)
                        else:
                            target=max(engine.setup_bound+engine.draw_bound+48,plan.partial_estimate)
                            if 2*(bound.cmax+cover_extra)>=target:
                                # At most two charged comparisons per scheduled probe; no refinement.
                                margin=bound.lower-16*(q.bit_length()-2)-60-64
                                stops[q].append(margin)
                            if 2*max(bound.cmin,req)<target:
                                next_pilots.add(pilots+1)
                if not next_pilots: continue
                inside=js[a]
                for j in ([inside] if high[inside]>high[-1] else [2*m] if high[inside]<high[-1] else [inside,2*m]):
                    pair=(j,js[1-a])
                    upd=[leaves[k].at(counts[k]+1) for k in pair]
                    newhigh=list(high)
                    for k,keys in zip(pair,upd):
                        newhigh[k]=keys[1]
                    assert newhigh!=high, 'a same-revision memo hit is possible'
                    gain=sum(group_lower(keys,pair,upd,inc,h) for keys,inc in ((low,True),(high,False)))
                    ca=[1+scan_charge(newhigh[s:2*m:2]+[newhigh[-1]])+
                        scan_charge(newhigh[1-s:2*m:2]) for s in (0,1)]
                    uv=(u+int(j==2*m and a==0),v+int(j==2*m and a==1))
                    assert sum(uv)<=max_shared
                    for b in next_pilots:
                        k=uv+(b,)
                        nb=Bounds(bound.lower+gain,bound.cmin+min(ca),bound.cmax+max(ca))
                        if k in later: later[k].merge(nb)
                        else: later[k]=nb
        states=later
        if not states: break
    if states or not stops:
        return dict(graph=spec['name'],certified=False,unfinished=len(states),visited=visited,
                    reason='horizon or no forced admission')
    margins={q:min(v) for q,v in stops.items()}
    return dict(graph=spec['name'],certified=min(margins.values())>0,lower=min(margins.values()),
                probe_margins=margins,visited=visited,warm=warm,max_shared=max_shared,warm_floor=warm_floor)


def run():
    rows=[]
    for spec in specs():
        if spec['family']=='paired':
            try: row=verify(spec)
            except AssertionError as exc: row=dict(graph=spec['name'],certified=False,reason=str(exc))
            rows.append(row)
            print(row,flush=True)
    data=DEST/'uniform_proof.json'
    if data.exists():
        assert json.loads(json.dumps(rows))==json.loads(data.read_text()), 'proof changed'
    else:
        data.write_text(json.dumps(rows,indent=2))
    assert all(r['certified'] for r in rows), 'the published positive all-ranks bounds were not established'


if __name__=='__main__':
    run()
