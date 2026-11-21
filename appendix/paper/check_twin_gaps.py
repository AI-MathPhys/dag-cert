"""Check the clean-law comparison using the very same twin oracle representation."""
import json
from statistics import mean
from unittest.mock import patch
from paper.prefix_routing_benchmark import DEST,base,EXTENSIONS
from paper.overlap_prefix_benchmark import TwinProblem,problem
from paper.decision_price_family import execute


def check():
    pair=json.loads((base.DEST/'same_graph.json').read_text())['selected']
    totals={}
    for k,j in (('a','b'),('b','a')):
        p,c=problem(pair[k]['spec']);other=problem(pair[j]['spec'])[0].means
        p=TwinProblem(p.name,p.graph,dict(p.means),(),values=p.means,other=other,alpha=0.)
        with patch.dict(base.ENGINES,EXTENSIONS):
            rs=[{m:execute(p,c,t,m) for m in ('credit','credit-all')} for t in pair[k]['ties']]
        assert all(r['status']=='certified' and r['regret']==0 for v in rs for r in v.values())
        totals[k]=dict(gap=mean(v['credit']['work']-v['credit-all']['work'] for v in rs),
                       max_total_draws=max(sum(r['draws'] for r in v.values()) for v in rs),runs=rs)
    assert totals['a']['gap']==194101.375 and totals['b']['gap']==-3047397.625
    assert max(v['max_total_draws'] for v in totals.values())<180000
    (DEST/'clean_twin_gaps.json').write_text(json.dumps(totals,indent=2))
    print([(k,v['gap'],v['max_total_draws']) for k,v in totals.items()])


if __name__=='__main__':
    check()
