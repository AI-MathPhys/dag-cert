"""Fresh timing check at the precision showing inconsistent inert-control timings."""
import json
import platform
import random
from collections import defaultdict

from paper import compact_side_structural as structural
from paper.compact_side_benchmark import ROOT, digest, config, caseid, run_one

DEST=ROOT/'results/compact_side_repeat_v1'
METHODS=('compact','compact_sham','range','side_compact','pre_only','side_range')


def run():
    specs=[dict(family='overlap_repeat',seed=i,eps=.0125,law='constant') for i in range(312101,312109)]
    DEST.mkdir(parents=True,exist_ok=True)
    if any(DEST.iterdir()):
        raise ValueError('use an empty results directory')
    sources=dict(json.loads((structural.DEST/'manifest.json').read_text())['source'])
    for f in ('paper/compact_side_repeat.py','paper/compact_side_repeat_protocol.txt'):
        sources[f]=digest(ROOT/f)
    assert all(digest(ROOT/f)==h for f,h in sources.items())
    (DEST/'manifest.json').write_text(json.dumps(dict(cases=specs,methods=METHODS,source=sources,
                              python=platform.python_version(),platform=platform.platform()),indent=2))
    blocks=[]
    for s in specs:
        for pair in range(3):
            order=list(METHODS)
            random.Random(s['seed']+313101*(pair+1)).shuffle(order)
            blocks.extend(((s,2*pair,order),(s,2*pair+1,order[::-1])))
    random.Random(313909).shuffle(blocks)
    with (DEST/'runs.jsonl').open('x') as out:
        for i,(s,rep,order) in enumerate(blocks,1):
            p,_=structural.problem(s)
            for pos,method in enumerate(order):
                r=run_one(lambda:p,config(s),s['seed'],'compact' if method=='compact_sham' else method)
                r.update(method=method,case=caseid(s),repeat=rep,position=pos)
                out.write(json.dumps(r)+'\n')
                out.flush()
            if i%12==0:
                print(i,'/',len(blocks),'blocks',flush=True)
    (DEST/'complete.json').write_text(json.dumps(dict(records=len(blocks)*len(METHODS),
                                          sha256=digest(DEST/'runs.jsonl'))))


def report():
    import math
    import statistics
    import numpy as np
    manifest=json.loads((DEST/'manifest.json').read_text())
    assert all(digest(ROOT/f)==h for f,h in manifest['source'].items())
    specs={caseid(s):s for s in manifest['cases']}
    stamp=json.loads((DEST/'complete.json').read_text())
    lines=(DEST/'runs.jsonl').read_text().splitlines()
    assert digest(DEST/'runs.jsonl')==stamp['sha256'] and len(lines)==stamp['records']==288
    groups=defaultdict(lambda:defaultdict(dict))
    for line in lines:
        r=json.loads(line)
        group=groups[r['case']][r['repeat']]
        assert r['method'] not in group
        group[r['method']]=r
    done={m:0 for m in METHODS}
    certificates=sham_paths=0
    for k,s in specs.items():
        p,_=structural.problem(s)
        v=p.graph.optimal_values(p.means)
        vals=[v[j] for j in p.graph.children[0]]
        assert set(groups[k])==set(range(6))
        for rs in groups[k].values():
            assert set(rs)==set(METHODS)
            for m,r in rs.items():
                if r['status']=='certified':
                    assert max(vals)-vals[r['action']]<=s['eps']+1e-12
                    assert r['work']<=102400000 and r['draws']<=262144 and r['seconds']<=12
                    assert r['box'][1]-r['box'][0]<=round(config(s)['K']*s['eps'])
                    certificates+=1
            for x,y in [('compact','compact_sham'),('pre_only','side_compact')]:
                if rs[x]['status']==rs[y]['status']=='certified':
                    assert all(rs[x][f]==rs[y][f] for f in ('action','box','work','draws','queries','logical'))
                    sham_paths+=1
        for m in METHODS:
            done[m]+=all(rs[m]['status']=='certified' for rs in groups[k].values())
    ratios={}
    for m,ref in [('side_compact','compact'),('side_compact','range'),('side_compact','pre_only'),
                  ('compact_sham','compact'),('pre_only','compact'),('side_range','range')]:
        for key in ('work','seconds'):
            logs=[]
            for g in groups.values():
                if all(rs[m]['status']==rs[ref]['status']=='certified' for rs in g.values()):
                    logs.append(math.log(statistics.median(rs[m][key]/rs[ref][key] for rs in g.values())))
            if logs:
                vals=np.asarray(logs)
                sample=np.random.default_rng(265901).integers(len(vals),size=(10000,len(vals)))
                ci=np.exp(np.quantile(vals[sample].mean(axis=1),[.025,.975])).tolist()
                ratios[m+'/'+ref+':'+key]=dict(joint=len(vals),ratio=math.exp(statistics.mean(logs)),
                                               ci=ci,wins=sum(t<0 for t in logs))
    output=dict(done=done,certificates=certificates,inert_identities=sham_paths,ratios=ratios)
    (DEST/'summary.json').write_text(json.dumps(output,indent=2))
    return output


if __name__=='__main__':
    import sys
    if '--report' not in sys.argv:
        run()
    print(report())

