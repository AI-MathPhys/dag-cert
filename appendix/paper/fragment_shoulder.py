"""All-rank reversal test: exclude early forecasts then exhaust unresolved public histories."""
import heapq
import json
import math
from pathlib import Path
import subprocess
import tempfile
from paper.fragment_sign_bounds import originals,Supply
from paper.fragment_sign_benchmark import DEST,ROOT
from paper.uniform_price_proof import Leaf


def reject(m,q):
    # Outward bins; any affordable anchor must survive at least one bin.
    high=m.mu[m.W]-m.radius(q-1)+m.slack
    for i in range(max(0,math.ceil(high*10000))+1):
        a,z=i/10000,(i+1)/10000
        if sum(mu-1e-7>=z-m.eps for mu in m.mu)>12:continue
        # At count 16 the mixture's 17/16 factor covers log(33); at counts
        # >=32 the log term already covers it. Counts here are multiples of 16.
        assert 17/16*(m.log+.5*math.log(17))>=m.log+.5*math.log(33)
        cells=[(m.log+.5*math.log(33))/(2*max(abs(mu-a)+m.slack,abs(mu-z)+m.slack,m.eps/4)**2) for mu in m.mu]
        residual=max(0,sum(sorted(cells)[:-4])-32*(q-1))
        if m.e.setup_bound+78*residual<=2*m.max_credit(q)+1:return False
    return True


def run():
    spec=list(originals())[-1]
    m=Supply(spec)
    gates={2**k:reject(m,2**k) for k in range(2,13)}
    assert all(gates.values())
    groups=[]
    for mask in sorted(set(m.owners),key=lambda a:tuple(sorted(a))):
        members=[i for i,owners in enumerate(m.owners) if owners==mask]
        leaves=[Leaf(m.mu[i],m.K,m.log) for i in members]
        counts=[0]*len(leaves)
        for j,l in enumerate(leaves):
            while l.at(counts[j])[1]==m.K:counts[j]+=1
        r=sum(counts)
        heap=[(-l.at(n)[1],j) for j,(l,n) in enumerate(zip(leaves,counts))]
        heapq.heapify(heap)
        # Only local block counts up to 8192 can enter the recursion. For equal
        # head-key runs all canonical orders have identical start/end multisets.
        rows=[]
        lower=max(l.at(n)[0] for l,n in zip(leaves,counts))
        while len(rows)<=8192:
            start=lower
            value=-heap[0][0]
            n=0
            while -heap[0][0]==value:
                _,j=heapq.heappop(heap);counts[j]+=1
                l,u,_,_=leaves[j].at(counts[j])
                lower=max(lower,l);heapq.heappush(heap,(-u,j))
                n+=1
            rows.append([value,start,start])
            rows.extend([[value,start,lower] for _ in range(n-1)])
        groups.append(dict(mask=sum(1<<i for i in mask),warm=r,rows=rows))
    with tempfile.TemporaryDirectory() as d:
        inp=Path(d)/'model.json'
        inp.write_text(json.dumps(dict(Q=8192,K=m.K,classes=groups)))
        proc=subprocess.run(['node',str(ROOT/'paper/fragment_shoulder_boxes.js'),str(inp)],
                            capture_output=True,check=True,text=True)
    result=dict(seed=spec['seed'],gates=gates,**json.loads(proc.stdout))
    assert result['remaining']==0 and result['last']<8192
    path=DEST/'shoulder.json'
    if path.exists():assert json.loads(json.dumps(result))==json.loads(path.read_text())
    else:path.write_text(json.dumps(result,indent=2))
    print(result)


if __name__=='__main__':run()
