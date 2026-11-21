"""Check a fragmentation-specific ordinary-prefix certificate; a failed sufficient test is retained."""
import json
import argparse
import math
from pathlib import Path
import subprocess
import tempfile

from paper.fragment_sign_bounds import originals, Supply
from paper.fragment_sweep_model import queues
from paper.fragment_sweep_export import export
from paper.fragment_sign_benchmark import DEST,ROOT


def verify(s,folder):
    model=Supply(s);e=model.e
    value=folder/f"fixture-{s['seed']}.json"
    end=folder/f"last-{s['seed']}.json"
    export(s,value)
    process=subprocess.run(['node',str(ROOT/'paper/fragment_sweep_check.js'),str(value),str(end)],
                           check=True,text=True,capture_output=True)
    bounds=json.loads(process.stdout)
    states=json.loads(end.read_text())
    cl,leaf=queues(s,512)
    histories=[]
    for c in cl:
        counts={i:0 for i in c['members']}
        for i in counts:
            while leaf[i].at(counts[i])[1]==model.K:counts[i]+=1
        seq=[]
        for _,j,_ in c['heads']:
            seq.append(dict(counts))
            counts[j]+=1
        histories.append(seq)
    q=512
    assert min(model.mu[i]+model.radius(q)-model.slack for i in (model.W,model.R))-(
        model.mu[model.W]-model.radius(q)+model.slack)>model.eps, 'possible early certification'
    # A memo hit requires a block in which neither upper key changes; only the
    # initial clipped prospect visits can do that. All later block endpoints differ.
    for l in leaf:
        for b in range(q):
            if l.at(b)[1]<model.K:assert l.at(b+1)[1]<l.at(b)[1]
    clipped=sum(model.quota(i,1.,q) for i in (model.W,model.R))
    credit=(3*min(model.ks)+1)*(q-clipped)
    margin=float('inf')
    for counts,_,_ in states:
        n={}
        for g,x in enumerate(counts):n.update(histories[g][x])
        lower=[leaf[i].at(n[i])[0] for i in range(model.M)]
        upper=[leaf[i].at(n[i])[1] for i in range(model.M)]
        theta=max(lower)
        e.ev.counts={x:16*n[i] for i,x in enumerate(e.g.leaves)}
        e.ev.sums={x:leaf[i].at(n[i])[2] for i,x in enumerate(e.g.leaves)}
        e.idx.lower,e.idx.upper=lower,upper
        e.idx.q=q;e.idx.stats['misses']=q-clipped
        actions=set().union(*(model.owners[i] for i,k in enumerate(lower) if k==theta))
        for a in actions:
            assert len(e.idx.top.inside[a])>=8
            e.point=(a,False,theta,None,None)
            # Miss fraction affects parking; evaluate the residual at *maximum*
            # holding price, and the earnings with minimum possible misses and
            # maximum 4 retained additional members.
            e.idx.stats['misses']=q
            plan=e.plan()
            if plan is None:margin=-1;continue
            pcm=math.ceil(2*(model.log+.5*math.log1p(1/model.eps**2))/model.eps**2)
            future=sum(max(0,pcm-16*n[i]) for i,x in enumerate(e.g.leaves)
                       if e.ev.sums[x]/(16*n[i])>=theta/model.K-model.eps)
            earn=future/32*(q-clipped)/q*max(0,4*model.ks[a]-
                (16+2*len(e.idx.top.inside[a]).bit_length())*min(e.idx.cap,plan.high_count+4))
            margin=min(margin,2*credit-max(e.setup_bound+e.draw_bound+48,plan.partial_estimate),
                       earn-plan.partial_estimate)
    out=dict(seed=s['seed'],**bounds,gate_funding=credit-16*(68*model.M+96),plan_margin=margin)
    final_query=23+4*model.h-5*(3*max(model.ks)+1)-10*json.loads(value.read_text())['lis']
    out['clip256']=out['baselines']['256'][2]+final_query
    out['conditional_gain']=min(out['baselines']['256'][1]-16,out['baselines']['512'][1]-32)-60-64
    out['certified']=(out['conditional_gain']>0 and min(out['clip256'],out['clipLower'])>=1 and
                      out['earlyCredit']<out['gate'] and out['gate_funding']>=0 and margin>=0)
    return out


def run(refresh=False,seed=None):
    with tempfile.TemporaryDirectory() as tmp:
        result=[verify(s,Path(tmp)) for s in originals() if s['profile']=='sharp' and (seed is None or seed==s['seed'])]
    target=DEST/'sweep.json'
    if seed is not None:
        assert not refresh and result
        assert [r for r in json.loads(target.read_text()) if r['seed']==seed]==result
    elif target.exists() and not refresh:assert json.loads(target.read_text())==result
    else:target.write_text(json.dumps(result,indent=2))
    print([(r['seed'],r['certified'],r['conditional_gain'],r['clipLower'],round(r['plan_margin'])) for r in result])


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true',help='refresh the derived certificate')
    parser.add_argument('--seed',type=int,help='verify a single archived sharp input')
    args=parser.parse_args()
    run(args.write,args.seed)
