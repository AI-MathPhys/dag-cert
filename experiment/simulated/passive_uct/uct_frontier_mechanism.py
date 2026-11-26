"""Common-prefix work and relevance diagnostics, excluded from timed runs."""
import json
from experiment.simulated.passive_uct.uct_frontier_study import DEST,CASES,SEEDS,METHODS,verify
from experiment.simulated.passive_uct.uct_frontier_families import make
from dagcert._core.compiled_retirement import Search

def run():
    verify()
    rows=[json.loads(s) for s in (DEST/'runs.jsonl').read_text().splitlines()]
    with (DEST/'mechanism.jsonl').open('x') as out:
        for f,n in CASES:
            for seed in SEEDS:
                steps=max(r['steps'] for r in rows if (r['family'],r['size'],r['seed'])==(f,n,seed))
                p,e=make(f,n,seed)
                for method in METHODS:
                    lane=Search(p,seed,method,e)
                    initial=lane.work
                    post=0;first_work=None
                    for t in range(steps):
                        lane.step()
                        if lane.first_cut is not None:
                            if first_work is None:first_work=lane.work
                            else:post+=1
                    m=lane.monitor;ev=m.evidence;b=getattr(m,'bounds',None)
                    threshold=lane.query[2]
                    row=dict(family=f,size=n,seed=seed,method=method,steps=steps,
                        certified=lane.certified,work=lane.work,setup_work=initial,
                        monitor_work=m.work.total,first_cut=lane.first_cut,first_cut_work=first_work,
                        post_cut_rollouts=post,frontier_terminals=sum(ev.upper[j]>=threshold for j in p.graph.leaves),
                        terminals=len(p.graph.leaves),unobserved=sum(ev.counts[j]==0 for j in p.graph.leaves),
                        messages=getattr(b,'messages',None),retired=getattr(b,'retired',None),
                        circuit_edges=getattr(m,'info',{}).get('edges'),
                        dead=getattr(b,'dead_nodes',None),final_gap=lane.query[1])
                    if b is not None:
                        row['live_edges']=sum(b.active)
                        row['samples_on_released_terminals']=b.skipped_dead
                    out.write(json.dumps(row)+'\n');out.flush()
                print(f,n,seed,steps,flush=True)

if __name__=='__main__':run()

