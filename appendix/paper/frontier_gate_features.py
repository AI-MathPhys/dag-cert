"""Read-only features at a single persistent verification checkpoint."""
import math

STATIC=('actions','terminals','runs_per_action','precision_load')
DYNAMIC=STATIC+('coverage','near_seen','signed_gap','top_gap','width','switches','leader_share')
def checkpoint(m):
    return 1+max(8,(m+3)//4)
def scan_cost(m,a):
    return 32*m+6*a+80
def measure(p):
    idx=p.idx; m=len(p.g.leaves);eps=p.c['epsilon']
    vals=[];peaks=[-1.,-1.];nlead=0
    for j,leaf in enumerate(p.g.leaves):
        n=p.ev.counts[leaf]
        if n:
            mean=p.ev.sums[leaf]/n
            vals.append(mean)
            side=idx.lookup[j][0]
            peaks[side]=max(peaks[side],mean)
            nlead=max(nlead,n)
    best=max(vals,default=0.)
    # Linear top-two pass. Ties count as independent terminal contenders.
    first=second=-1.
    for x in vals:
        if x>=first:second,first=first,x
        elif x>second:second=x
    signed=(peaks[1]-peaks[0])/eps if min(peaks)>=0 else 0.
    return dict(actions=len(idx.top.inside),terminals=m,
                runs_per_action=sum(map(len,idx.top.inside))/len(idx.top.inside),
                precision_load=1/(m*eps*eps),coverage=len(vals)/m,
                near_seen=sum(x>=best-eps for x in vals)/max(1,len(vals)),
                signed_gap=signed,top_gap=(first-second)/eps if second>=0 else 0.,
                width=(p.point[4][0]-p.point[2])/p.tol,switches=idx.switches,
                leader_share=nlead/max(1,p.N))
def decision(node,features):
    while 'feature' in node:
        node=node['left'] if features[node['feature']]<=node['threshold'] else node['right']
    return node['admit']

