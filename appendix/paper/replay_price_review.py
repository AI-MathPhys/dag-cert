"""One-command witness reproduction. No wall timer and no downloads."""
import json
from paper.check_clock_witness import check as original_check
from paper.audit_decision_price import check as path_check
from paper.decision_price_benchmark import DEST, ENGINES, population, factory, config
from paper.decision_price_family import execute
from paper.credit_admission import CreditAtAdmission, setup
from paper.decision_price_stress import problem
from paper.decision_price_same_graph import mixture
from unittest.mock import patch


def main():
    original_check()
    obj=next(x for x in population() if x['tag']=='selected')
    p=factory(obj['s'])()
    cfg=config(obj['s'])
    archived={}
    with (DEST/'runs.jsonl').open() as f:
        for line in f:
            r=json.loads(line)
            if r['tag']=='selected': archived[r['method']]=r
    assert set(archived)==set(ENGINES)
    print('selected graph | method | work | draws | sealed | root regret')
    for m in ENGINES:
        r=execute(p,cfg,obj['tie'],m)
        for k in ('status','work','draws','regret'):
            assert r[k]==archived[m][k],(m,k,r[k],archived[m][k])
        assert r['status']=='certified'
        print(m,r['work'],r['draws'],r['seal'],r['regret'])
    print('reference / threshold path:',dict(path_check(obj)))
    with patch.dict(ENGINES,{'credit-all':CreditAtAdmission}):
        all_credit=execute(p,cfg,obj['tie'],'credit-all')
        assert all_credit['work']==3743617 and all_credit['regret']==0
        print('credit-all',all_credit)
    family=json.loads((DEST/'family.json').read_text())['selected']
    extras=json.loads((DEST/'credit_complete.json').read_text())['family']
    if family:
        p,cfg=setup(family['seed'],family['size'],family['shift'],family['inverse'])
        with patch.dict(ENGINES,{'credit-all':CreditAtAdmission}):
            for tie,runs,extra in zip(family['ties'],family['runs'],extras,strict=True):
                for m,old in dict(runs,**{'credit-all':extra}).items():
                    assert execute(p,cfg,tie,m)==old
        print('232-terminal expectation checked over all',len(family['ties']),'ties.')
        left=[dict(r,**{'credit-all':v}) for r,v in zip(family['runs'],extras,strict=True)]
        selected=json.loads((DEST/'stress.json').read_text())['selected']
        right=selected['right']
        p,cfg=problem(right['spec'])
        with patch.dict(ENGINES,{'credit-all':CreditAtAdmission}):
            for tie,old in zip(right['ties'],right['runs'],strict=True):
                for m,r in old.items():
                    assert execute(p,cfg,tie,m)==r
        k=selected['left_weight']
        sums={m:k*sum(r[m]['work'] for r in left)+(16-k)*sum(r[m]['work'] for r in right['runs'])
              for m in left[0]}
        assert sums==selected['sums'] and sums['reference']<min(v for m,v in sums.items() if m!='reference')
        print('mixture interval and sums /128:',mixture(left,right['runs']),sums)
        same=json.loads((DEST/'same_graph.json').read_text())['selected']
        p_a,_=problem(same['a']['spec'])
        p_b,cfg=problem(same['b']['spec'])
        assert p_a.graph.children==p_b.graph.children and same['a']['ties']==same['b']['ties']
        with patch.dict(ENGINES,{'credit-all':CreditAtAdmission}):
            for tie,old in zip(same['b']['ties'],same['b']['runs'],strict=True):
                for m,r in old.items():
                    assert execute(p_b,cfg,tie,m)==r and r['regret']==0
        a,b=same['a']['runs'],same['b']['runs']
        assert a==left and mixture(a,b)==same['interval']
        nums={m:7*sum(r[m]['work'] for r in a)+sum(r[m]['work'] for r in b) for m in a[0]}
        assert nums==dict(reference=261292327,bare=262244817,credit=262245009,
                          threshold=262444488,**{'credit-all':275754513})
        print('same graph, two laws, interval and sums /64:',same['interval'],nums)


if __name__=='__main__':
    main()
