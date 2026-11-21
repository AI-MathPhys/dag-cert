"""Secondary sensitivity: grant a materialized batch a child-delta parent updater."""
import json
from collections import Counter,defaultdict
from unittest.mock import patch

from paper import ancestor_repair_replay as ref
from paper.report_ancestor_repair import bill
from paper.report_compact_pre import load

OUT=ref.DEST/'child_delta'
Original=ref.Recorder


class DeltaRecorder(Original):
    total=None

    def finish(self):
        super().finish()
        dirty={self.tree.size+self.pair[i] for i in range(2) if self.events[i]}
        t=self.tree
        while dirty:
            next_dirty=set()
            for p in {node//2 for node in dirty}:
                old,oldcount=self.old[p]
                left,right=2*p,2*p+1
                if left in dirty and right in dirty:
                    a,b=t.value[left],t.value[right]
                    v=max(a,b)
                    count=(t.count[left] if a==v else 0)+(t.count[right] if b==v else 0)
                    price=9  # both child proposals in hand, old-state check and writes
                    reason='two'
                else:
                    c=left if left in dirty else right
                    a,i=self.old[c]
                    b,j=t.value[c],t.count[c]
                    if b>old:
                        v,count=b,j
                        price=4
                        reason='new_high'
                    elif b==old:
                        v,count=old,oldcount-(i if a==old else 0)+j
                        price=8+int(a==old)
                        reason='new_tie'
                    elif a<old:
                        v,count=old,oldcount
                        price=4
                        reason='unchanged'
                    elif oldcount>i:
                        v,count=old,oldcount-i
                        price=9
                        reason='other_winner'
                    else:
                        sibling=c^1
                        v=max(b,t.value[sibling])
                        count=(j if v==b else 0)+(t.count[sibling] if v==t.value[sibling] else 0)
                        price=13  # conservatively charge the fallback's tie case
                        reason='sibling'
                assert (v,count)==(t.value[p],t.count[p])
                self.total['price']+=price
                self.total['visits']+=1
                self.total[reason]+=1
                if (v,count)!=(old,oldcount):
                    self.total['changed']+=1
                    if p>1:
                        next_dirty.add(p)
            dirty=next_dirty


def run():
    specs,groups=load()
    original=[json.loads(x) for x in (ref.DEST/'cases.jsonl').read_text().splitlines()]
    OUT.mkdir(exist_ok=False)
    import hashlib
    digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    (OUT/'manifest.json').write_text(json.dumps(dict(source=digest(ref.ROOT/'paper/ancestor_repair_delta.py'),
        primary=digest(ref.DEST/'cases.jsonl')),indent=2))
    aggregates=defaultdict(Counter)
    with patch.object(ref,'Recorder',DeltaRecorder), (OUT/'cases.jsonl').open('x') as out:
        for index,r in enumerate(original):
            s=specs[r['case']];m=r['method']
            DeltaRecorder.total=Counter()
            rec=ref.replay_case(s,groups[r['case']][0][m],m)
            assert all(rec[k]==r[k] for k in rec)
            b=bill(r); t=DeltaRecorder.total
            assert t['visits']==b.get('batch_visits',0) and t['changed']==b.get('batch_changed',0)
            # The old and proposed states of each dirty child are assumed carried
            # by the batch. Give a sensitivity charging four additional field
            # reads per dirty child edge if those arguments must be fetched.
            edges=t['visits']+t['two']
            base=b['strong_bill']-12*t['visits']+t['price']
            cert=base-(b['strong_bill']-b['cert_bill'])
            rec=dict(case=r['case'],method=m,delta=dict(t),edges=edges,strong=base,cert=cert)
            out.write(json.dumps(rec)+'\n')
            part='overlap' if s['family']=='overlap' else 'broad'
            z=aggregates[m,part]
            z.update(t)
            z.update(dict(strong=base,cert=cert,edges=edges,work=b['work']))
            if (index+1)%40==0:print(index+1,'delta replays',flush=True)
    summary={}
    for (m,part),z in aggregates.items():
        saving=z['strong']-z['cert']
        ceiling=z['price']-2*z['changed']
        summary[m,part]=dict(totals=dict(z),batch_gain=1-z['strong']/z['work'],
             marginal=saving/z['strong'],marginal_paid_args=saving/(z['strong']+4*z['edges']),
             residual_above_writes=ceiling/z['strong'],
             price_plus_parent_ceiling=(ceiling+saving)/z['strong'],
             price_parent_plus_dispatch_ceiling=(ceiling+saving+4*z['visits'])/z['strong'])
    (OUT/'summary.json').write_text(json.dumps({m+'_'+p:v for (m,p),v in summary.items()},indent=2))
    (OUT/'complete.json').write_text(json.dumps(dict(records=len(original),sha256=digest(OUT/'cases.jsonl'))))


if __name__=='__main__':
    run()

