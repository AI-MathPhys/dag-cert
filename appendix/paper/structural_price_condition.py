"""Static sufficient tests for every rank tape and every within-sibling ordering."""
import math
from bisect import bisect_right
from paper.uniform_price_proof import Leaf

from paper.immediate_pricing import ImmediateCompact


def run_fee(start, stop, size):
    """Tariff for one half-open interval in CountTree.cover."""
    a,b = start+size,stop+size
    cost = 2
    while a < b:
        cost += 4 + 2*((a & 1)+(b & 1))
        a=(a+1)//2
        b//=2
    return cost


def pair_bounds(bits,size):
    """Max fee and range count extrema under all independent sibling transpositions."""
    states={(-1,0):(0,0,0)}
    for start in range(0,len(bits),2):
        later={}
        for pair in {tuple(bits[start:start+2]),tuple(bits[start:start+2][::-1])}:
            for (old,begin),values in states.items():
                last,left=old,begin
                cost,lo,hi=values
                for j,bit in enumerate(pair,start):
                    if bit==last:continue
                    if last!=-1:cost+=run_fee(left,j,size)
                    if bit:lo+=1;hi+=1
                    last,left=bit,j
                key=last,left
                if key in later:
                    a,b,c=later[key]
                    later[key]=(max(a,cost),min(b,lo),max(c,hi))
                else:later[key]=(cost,lo,hi)
        states=later
    fee=max(v[0]+run_fee(key[1],len(bits),size) for key,v in states.items())+2
    return fee,min(v[1] for v in states.values()),max(v[2] for v in states.values())


def cold_records(side,size,cold):
    """Multiple-choice nondecreasing subsequence, at most one terminal per cover block."""
    tails=[]
    for node in side:
        first,width=node,1
        while first<size:first*=2;width*=2
        values={cold[j] for j in range(first-size,first-size+width) if j in cold}
        changes=sorted((bisect_right(tails,v),v) for v in values)
        for i,v in changes:
            if i==len(tails):tails.append(v)
            else:tails[i]=min(tails[i],v)
    return len(tails)


def check(problem,cfg,p=256):
    """The condition abstains unless one sign follows for the entire sibling orbit."""
    assert p>=8 and p & (p-1)==0
    graph=problem.graph
    leaves=graph.leaves
    M=len(leaves)
    h=(M-1).bit_length()
    H=1<<h
    eps,K=cfg['epsilon'],cfg['K']
    assert len(graph.children[0])==4 and M%2==0 and h<=8 and cfg['oracle_cost']==1
    assert graph.children[0]==tuple(range(1,5)) and len(graph.children)==M+5
    assert K*eps>2 and 0<cfg['delta']<1 and all(0<=v<=1 for v in problem.means.values())
    assert set(problem.deterministic)==set(leaves)
    owners=[sum(1<<a for a,ch in enumerate(graph.children[1:5]) if x in ch) for x in leaves]
    assert all(v.bit_count()==2 for v in owners)
    values=[problem.means[x] for x in leaves]
    W,R=sorted(range(M),key=values.__getitem__,reverse=True)[:2]
    assert owners[W]&owners[R]==0 and values[W]-values[R]>eps
    engine=ImmediateCompact(problem,cfg,1)
    covers=[engine.idx.cover(a) for a in range(4)]
    ks=[sum(map(len,c)) for c in covers]
    ranges=[pair_bounds([v>>a & 1 for v in owners],H) for a in range(4)]
    fee=sum(x[0] for x in ranges)
    candidates={a for a in range(4) if ranges[a][2]>=8}
    membership=max(16+2*hi.bit_length() for _,_,hi in ranges)
    profiles=[Leaf(v,K,engine.ev.log_ratio) for v in values]
    cold=[j for j in range(M) if j not in (W,R)]
    cold_upper={j:profiles[j].at(1)[1] for j in cold}
    assert max(cold_upper.values()) < (values[R]-1e-7)*K
    assert all(profiles[j].at(1)[0]==0 for j in cold)
    warm=[]
    for leaf in profiles:
        r=0
        while leaf.at(r)[1]==K:r+=1
        warm.append(r)
    total=sum(warm)
    min_side=min(sum(n for n,v in zip(warm,owners) if bool(v & (1<<a))==b)
                 for a in range(4) for b in (True,False))
    double=(min_side+1)//2
    sweep=total-double
    join=(W^R).bit_length()
    # Every side has at most one hot record in its ordered subsequence of sub-K records.
    lis=max(2+sum(cold_records(side,H,cold_upper) for side in cover) for cover in covers)
    kmin,kmax=min(ks),max(ks)
    def credit_upper(q):
        upper=fee
        for t in range(q):
            hi=min(kmax,max(0,total-t-min(t,double)))
            lo=max(0,kmin-2*t)
            assert lo<=hi
            writes=max(min(2*kmax-k,k+2*lis) for k in range(lo,hi+1))
            upper+=3*kmax+1+writes
        return upper

    def rad(b):
        n=16*b
        return math.sqrt((n+1)/(2*n*n)*(engine.ev.log_ratio+.5*math.log1p(n))) if n else math.inf

    def minimum_winner(t):
        rivals=sum(bool(v & owners[W]) for j,v in enumerate(owners) if j!=W)
        return max(0,t-rivals,t-sweep+warm[W] if t>=sweep else 0)

    scan=68*M+96
    out=dict(M=M,height=h,join=join,kmin=kmin,kmax=kmax,cover_fee=fee,
             max_intervals=[b[2] for b in ranges],min_intervals=[b[1] for b in ranges],
             eligible=len(candidates),sweep=sweep,lis=lis)
    if not any(owners[W]&(1<<a) for a in candidates):
        # A candidate eligible in some orbit member cannot contain the best prospect.
        checked=[]
        for logq in range(2,20):
            q=1<<logq;t=q-1;b=minimum_winner(t)
            anchor=values[W]-rad(b)-1e-7-2/K
            other=max((values[j] for j in range(M) if any(owners[j] & (1<<a) for a in candidates)),default=-1)
            if anchor>other+1e-7:
                out.update(no_launch=True,permanent=q,probe_checks=checked)
                break
            funded=fee+(5*kmax+1)*q >= 8*scan
            if funded and anchor<=max(0,other-rad(t)+1e-7+2/K):break
            checked.append(q)
    if out.get('no_launch') and h>=7:
        # If all screens close, only the bounds object's 12-unit startup is guaranteed.
        out.update(sign='immediate',bound=60 if any(b[1]>=8 for b in ranges) else 12)
        return out

    nstar=min(len(profiles[j].at(1)[3][1]) for j in cold)
    assert nstar>=4
    cold_unit=min(4*nstar-29-h,7*nstar-32-4*h)
    cold_floor=(M-6)*max(0,cold_unit)+(M-2)*min(0,cold_unit)
    hot_debt=0
    lost=[0,0]
    for j in (W,R):
        for b in range(1,2*p+1):
            _,_,_,events=profiles[j].at(b)
            for k,seq in enumerate(events):
                lost[k]+=16-len(seq)
                if len(seq)>=4:
                    hot_debt+=max(0,32+4*h-4*len(seq))
                if b>warm[j]:assert len(seq)==16, 'unpriced tail of a changing key'
    prices=[]
    for q in (p,2*p):
        t=q-1
        assert t>=sweep
        hot=16*(2*t-M+2)
        nu=max(0,hot-lost[1])+sum(len(profiles[j].at(1)[3][1]) for j in cold)
        nl=max(0,hot-lost[0])
        slack=(36*32*t+17*nu+(4+12*join)*nl+12*(join-1)*32*(t-sweep)
               +(23+4*h-5*(3*kmax+1)-10*lis)*q-5*fee-4*M)
        prices.append(slack)
    q=2*p;t=q-1
    # Allow all hot visits starting at K, including the crossing visit, as possible cache hits.
    miss=q-sum(warm[j] for j in (W,R))
    credit=(3*kmin+1)*miss
    anchor=values[W]-rad(minimum_winner(t))-1e-7-2/K
    max_anchor=values[W]-rad(t)+1e-7+2/K
    upper_gap=(values[R]+rad(t)-1e-7-2/K)-max_anchor-eps
    precision=math.ceil(2*(engine.ev.log_ratio+.5*math.log1p(1/eps**2))/eps**2)
    # No cold leaf remains a forecast target at the last probe. One of the two hot
    # lower keys equals the anchor. Parking the remaining hot target, if expensive,
    # is feasible. Thus its residual contributes at most the holding price.
    cold_clear=anchor-max(cold_upper.values())/K
    hold=2*precision/32*membership
    setup=engine.setup_bound
    estimate=max(setup+hold,setup+engine.draw_bound+48)
    useful=sum(v-1e-7>=max_anchor-eps for v in values)
    earn=useful*max(0,precision-16*t)/32*miss/q*max(0,4*kmin-6*membership)
    margin=cold_floor-hot_debt-32-60-64
    out.update(nstar=nstar,cold_unit=cold_unit,cold_floor=cold_floor,hot_debt=hot_debt,
               margin=margin,early=8*scan-credit_upper(p//2),clip=prices,
               funding=credit-16*scan,forecast=min(2*credit,earn)-estimate,
               pre_return=upper_gap,cold_clear=cold_clear)
    if (min(x[1] for x in ranges)>=8 and out['early']>0 and min(prices)>=1 and out['funding']>=0
            and out['forecast']>=0 and upper_gap>0 and cold_clear>0 and margin>0):
        out.update(sign='deferred',bound=margin)
    else:
        out.update(sign='abstain',bound=None)
    return out
