"""Counterfactual repair accounting on existing tapes; never schedules observations."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from paper.compact_pre_benchmark import DEST as ARCHIVE, ROOT, ProfileLane, config, factory, BUDGET, DRAWS
from paper.report_compact_pre import load

DEST = ROOT/'results/ancestor_repair_replay_v2'


class Profile:
    """Cold competitor prefixes for the two paths. Depths are one-based."""
    def __init__(self, tree, pair, increasing):
        self.pair = pair
        self.inc = increasing
        self.h = tree.size.bit_length()-1
        nodes = [tree.size+j for j in pair]
        self.join = (nodes[0]^nodes[1]).bit_length()
        paths = []
        for node in nodes:
            path = []
            while node>1:
                path.append(tree.value[node^1])
                node //= 2
            paths.append(path)
        for i in range(2):
            paths[i][self.join-1] = max(paths[1-i][:self.join-1], default=-1)
        self.levels = []
        for path in paths:
            high = -1
            prefix = []
            for key in path:
                high = max(high,key)
                prefix.append(high)
            self.levels.append(prefix)
        self.cursor = [0 if increasing else self.h]*2

    def lookup(self, side, x, pos):
        levels = self.levels[side]
        tests = 0
        if self.inc:
            while pos<self.h:
                tests+=1
                if levels[pos]>x:
                    break
                pos+=1
        else:
            while pos>0:
                tests+=1
                if levels[pos-1]<=x:
                    break
                pos-=1
        # Two fixed units and three per threshold test.
        return pos,min(self.h,pos+1),2+3*tests

    def depth(self, cold, peer, x):
        return min(cold,self.join) if peer>x else cold

    def price(self, side, events, peer_bounds, sums):
        """Price all actual updates; also price two alternative endpoint guards."""
        start = pos = self.cursor[side]
        point = 0
        pulls = 0
        for x,peer,observed in events:
            pos,cold,charge = self.lookup(side,x,pos)
            depth = self.depth(cold,peer,x)
            assert depth==observed, (depth,observed,x,peer)
            point += charge+5  # reads, peer test, minimum and accumulation
            pulls += depth
        self.cursor[side]=pos
        sums['clock_verified_pulls']+=pulls
        sums['point_price']+=point
        strong=cert=point
        if len(events)>=4:
            first,last = events[0][0],events[-1][0]
            temp,a,c0=self.lookup(side,first,start)
            temp,b,c1=self.lookup(side,last,temp)
            assert temp==pos
            check=c0+c1+8  # endpoints, cold extremes and baseline eligibility
            cold_min,cold_max=min(a,b),max(a,b)
            x_min,x_max=min(first,last),max(first,last)
            peer_min,peer_max=peer_bounds
            independent = cold_min==cold_max and cold_max<=self.join
            lo=self.depth(cold_min,peer_max,x_min)
            hi=self.depth(cold_max,peer_min,x_max)
            stationary = peer_min==peer_max
            if independent:
                assert pulls==len(events)*cold_min
                strong=cert=check+3
                sums['independent_priced_events']+=len(events)
            elif stationary:
                if lo==hi:
                    assert pulls==len(events)*lo
                    sums['stationary_priced_events']+=len(events)
                strong=cert=check+6+(3 if lo==hi else point)
            else:
                strong=check+point
                cert=check+6+(3 if lo==hi else point)
                if lo==hi:
                    assert pulls==len(events)*lo
                    sums['extra_cert_events']+=len(events)
                    sums['extra_cert_groups']+=1
        sums['strong_price']+=strong
        sums['cert_price']+=cert
        sums['oracle_strong_price']+=min(point,strong)
        sums['oracle_cert_price']+=min(point,strong,cert)


class Recorder:
    def __init__(self, tree, increasing):
        self.tree=tree
        self.original=tree.update
        self.increasing=increasing
        self.active=False
        self.profile=None
        self.sums=Counter()
        self.free_sums=Counter()
        tree.update=self.update

    def begin(self, pair, needs_clock):
        assert len(pair)==2 and pair[0]!=pair[1]
        self.active=True
        self.needs_clock=needs_clock
        self.pair=tuple(sorted(pair))
        self.events=[[],[]]
        self.old={}
        self.initial=[self.tree.value[self.tree.size+j] for j in self.pair]
        self.current=list(self.initial)

    def update(self,j,new):
        if not self.active:
            self.profile=None
            return self.original(j,new)
        side=0 if self.pair[0]==j else 1
        assert self.pair[side]==j
        t=self.tree
        old=self.current[side]
        assert old==t.value[t.size+j] and old!=new
        if not self.events[side]:
            node=t.size+j
            while node:
                if node in self.old:
                    break
                self.old[node]=t.value[node],t.count[node]
                node//=2
        before=t.w.heap_writes
        self.original(j,new)
        pulls=(t.w.heap_writes-before)//2-1
        self.events[side].append((max(old,new),self.current[1-side],pulls))
        self.current[side]=new

    def finish(self):
        self.active=False
        sides=[i for i in range(2) if self.events[i]]
        if not sides:
            return
        t=self.tree
        sums=self.sums if self.needs_clock else self.free_sums
        sums['tree_blocks']+=1
        counts=sum(len(self.events[i]) for i in sides)
        sums['events']+=counts
        sums['dirty_leaves']+=len(sides)
        if self.profile is None or self.profile.pair!=self.pair:
            self.profile=Profile(t,self.pair,self.increasing)
            sums['profiles']+=1
            sums['setup']+=16*self.profile.h+16
        touched=set()
        states={}
        dirty=set()
        for i in sides:
            node=t.size+self.pair[i]
            states[node]=self.current[i],1
            dirty.add(node//2)
            depth=max(event[2] for event in self.events[i])
            for _ in range(depth):
                node//=2
                touched.add(node)
            sums['eager']+=sum(event[2] for event in self.events[i])
            peer=1-i
            bounds=tuple(sorted((self.initial[peer],self.current[peer])))
            self.profile.price(i,self.events[i],bounds,sums)
        visited=changed=0
        while dirty:
            parents=set()
            for p in dirty:
                l,r=2*p,2*p+1
                def state(j):
                    if j in states:
                        return states[j]
                    if j in self.old:
                        return self.old[j]
                    return t.value[j],t.count[j]  # untouched throughout
                a,n=state(l); b,m=state(r)
                best=max(a,b)
                value=(best,(n if a==best else 0)+(m if b==best else 0))
                states[p]=value
                visited+=1
                if value!=self.old[p]:
                    changed+=1
                    if p>1:
                        parents.add(p//2)
            dirty=parents
        for node,old in self.old.items():
            assert states.get(node,old)==(t.value[node],t.count[node])
        sums['distinct_eager']+=len(touched)
        sums['batch_visits']+=visited
        sums['batch_changed']+=changed
        # Collect per-event metadata, coalesce at most two dirty paths, release scratch.
        sums['book']+=2*counts + 8 + 4*len(sides) + 4*visited

    def remove(self):
        del self.tree.update


def replay_case(s, row, method):
    p=factory(s)()
    c=config(s)
    lane=ProfileLane(p,c,s['seed'],method)
    eng=lane.engine
    lo,hi=Recorder(eng.idx.lt,True),Recorder(eng.idx.ut,False)
    ordinary=eng.ordinary
    blocks=0
    can_clear=(method=='core_compact' and any(len(side)>=8 for side in eng.idx.top.inside))

    def wrapped(remaining):
        nonlocal blocks
        if getattr(eng,'compact',None) is not None:
            return ordinary(remaining)
        pair=eng.pair
        for recorder in (lo,hi):
            recorder.begin(pair,can_clear and not eng.ended)
        result=ordinary(remaining)
        for recorder in (lo,hi):
            recorder.finish()
        blocks+=1
        return result

    eng.ordinary=wrapped
    build=getattr(p,'build',0)
    while not lane.point[1] and not lane.conflict and lane.draws<DRAWS and build+lane.work<BUDGET:
        lane.advance(DRAWS-lane.draws)
    cand,good,lower,_,outside=lane.point
    box=list(lane.private if outside is None else (lower,outside[0])) if good else None
    kernel=build+lane.work
    assert (lane.draws,eng.idx.q,build+eng.w.total+getattr(lane.oracle,'operations',0))==(
        row['draws'],row['queries'],row['logical'])
    assert getattr(eng,'meta',{})==row['meta']
    for recorder in (lo,hi):
        recorder.remove()
    del eng.ordinary
    disposal=lane.retire(p,c)
    assert kernel+disposal==row['work'] and disposal==row['drop']
    assert (cand if good else None,box)==(row['action'],row['box'])
    assert row['status']==('certified' if good else 'draw' if row['draws']==DRAWS else 'work')
    return dict(method=method,work=row['work'],draws=row['draws'],status=row['status'],
                ordinary_blocks=blocks,low=dict(lo.sums+lo.free_sums),high=dict(hi.sums+hi.free_sums),
                clock_free=dict(lo.free_sums+hi.free_sums))


def run(dest=DEST,limit=None):
    specs,groups=load()
    dest.mkdir(parents=True,exist_ok=False)
    digest=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
    (dest/'manifest.json').write_text(json.dumps(dict(archive=str(ARCHIVE.name),archive_sha256=digest(ARCHIVE/'runs.jsonl'),
        code_sha256=digest(__file__),protocol_sha256=digest(ROOT/'paper/ancestor_repair_protocol.txt'),
        cases=list(specs)[:limit],methods=['core_compact','core_range']),indent=2))
    n=0
    with (dest/'cases.jsonl').open('x') as out:
        for k in list(specs)[:limit]:
            s=specs[k]
            for m in ('core_compact','core_range'):
                r=replay_case(s,groups[k][0][m],m)
                r.update(case=k,seed=s['seed'],family=s['family'],epsilon=s['eps'])
                out.write(json.dumps(r)+'\n')
                out.flush()
                n+=1
            if n%20==0:
                print(n,'replays',flush=True)
    (dest/'complete.json').write_text(json.dumps(dict(records=n,sha256=digest(dest/'cases.jsonl'))))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,default=DEST)
    parser.add_argument('--limit',type=int)
    args=parser.parse_args()
    run(args.out,args.limit)

