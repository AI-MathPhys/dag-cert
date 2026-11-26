import math
import random
import unittest

from joint_root_cert._core.certified_uct import UCTWork
from joint_root_cert.graph import DAG, feature_lattice, trap
from joint_root_cert._core.maintenance_replay import Replay, build_trace, run_replay, shield
from joint_root_cert.certificates import CanonicalIntervals, RetiredBounds


def full_dp(graph, lower, upper):
    lo, hi = lower.copy(), upper.copy()
    for v in reversed(graph.order):
        if graph.children[v]:
            lo[v] = max(lo[c] for c in graph.children[v])
            hi[v] = max(hi[c] for c in graph.children[v])
    return lo, hi


def exact_live_edges(graph, lo, hi):
    reached={graph.root};edges=set()
    for p in graph.order:
        if p not in reached:continue
        for a,c in enumerate(graph.children[p]):
            if hi[c]>=lo[p]:
                edges.add((p,a));reached.add(c)
    return reached,edges


class RetiredBoundsTests(unittest.TestCase):
    def test_random_monotone_updates_exactness_structure_and_volume(self):
        for graph in (trap().graph,feature_lattice(4).graph,shield(7)[0].graph,shield(7,True)[0].graph):
            for seed in range(4):
                rng=random.Random(seed)
                centers={v:rng.randint(2,18) for v in graph.leaves}
                terminal_l,terminal_u=[0]*len(graph),[20]*len(graph)
                methods=[RetiredBounds(graph,UCTWork(),m,20) for m in ('eager','cut','live')]
                old_l,old_u=full_dp(graph,terminal_l,terminal_u)
                structural_volume=0
                for _ in range(500):
                    leaf=rng.choice(graph.leaves)
                    terminal_l[leaf]=rng.randint(terminal_l[leaf],centers[leaf])
                    terminal_u[leaf]=rng.randint(centers[leaf],terminal_u[leaf])
                    _,before=exact_live_edges(graph,old_l,old_u)
                    indegree=[0]*len(graph)
                    for p,a in before:indegree[graph.children[p][a]]+=1
                    lo,hi=full_dp(graph,terminal_l,terminal_u)
                    structural_volume+=sum((int(lo[v]!=old_l[v])+int(hi[v]!=old_u[v]))*indegree[v] for v in range(len(graph)))
                    for b in methods:
                        b.publish(leaf,terminal_l[leaf],terminal_u[leaf])
                        for v in range(len(graph)):
                            if b.live[v]:self.assertEqual((b.lower[v],b.upper[v]),(lo[v],hi[v]))
                    self.assertEqual(methods[0].query(),methods[1].query())
                    self.assertEqual(methods[0].query(),methods[2].query())
                    b=methods[2]
                    reached,edges=exact_live_edges(graph,lo,hi)
                    self.assertEqual({v for v in range(len(graph)) if b.live[v]},reached)
                    self.assertEqual({(b.parent[e],b.action[e]) for e in range(len(b.active)) if b.active[e]},edges)
                    self.assertLessEqual(b.incoming_copies,structural_volume)
                    self.assertLessEqual(b.retired,len(b.active))
                    self.assertTrue(all(n<=40 for n in b.endpoint_changes))
                    old_l,old_u=lo,hi

    def test_strict_cut_ties_and_shared_child_reference_counts(self):
        g=DAG(((1,2),(3,4),(4,5),(),(),()))
        b=RetiredBounds(g,UCTWork())
        b.publish(3,.8,.9)
        b.publish(4,.2,.8)
        self.assertTrue(b.active[b.outgoing[1][1]]) # equality does not cut
        b.publish(4,.2,.7)
        self.assertFalse(b.active[b.outgoing[1][1]])
        self.assertTrue(b.live[4]) # rival still subscribes
        self.assertEqual(b.indegree[4],1)
        b.publish(5,.85,.95)
        self.assertFalse(b.live[4])
        b.publish(4,.3,.6)
        self.assertEqual(b.skipped_dead,1)

    def test_recursive_release_avoids_dead_region_updates(self):
        g=DAG(((1,2,3),(),(),(4,5),(6,),(6,),()))
        a=RetiredBounds(g,UCTWork(),'cut');b=RetiredBounds(g,UCTWork(),'live')
        for s in (a,b):s.publish(1,.8,.9);s.publish(6,.1,.7)
        self.assertTrue(a.live[6]);self.assertFalse(b.live[6])
        ca,cb=a.messages,b.messages
        for s in (a,b):s.publish(6,.2,.6)
        self.assertGreater(a.messages,ca);self.assertEqual(b.messages,cb)
        self.assertEqual(a.query(),b.query())

    def test_identical_real_observations_checkpoints_and_certificates(self):
        for p in (trap(),feature_lattice(4)):
            for scale,geo in ((1,False),(80,False),(80,True)):
                runs=[Replay(p.graph,m,scale,geo) for m in ('full','legacy_event','eager','cut','live')]
                oracle=p.oracle(6234);leaves=p.graph.leaves
                for i in range(3000):
                    leaf=leaves[i%len(leaves)];reward=oracle.sample(leaf)
                    for run in runs:run.step(leaf,reward)
                    self.assertEqual(len({r.query() for r in runs}),1)
                    self.assertEqual(len({r.evidence.evaluations for r in runs}),1)
                self.assertTrue(all(r.evidence.counts==runs[0].evidence.counts for r in runs))

    def test_realizable_separation_traces_remain_uncertified_during_nuisance_phase(self):
        for spec in ('shield8','buried8'):
            p,trace,extra=build_trace(spec,'shielded',6000)
            rows=[run_replay(p,trace,m,1,False) for m in ('eager','cut','live')]
            self.assertEqual(len({r['output_sha256'] for r in rows}),1)
            self.assertGreater(rows[0]['first_certificate'],len(trace)-extra['warm'])
            self.assertLess(rows[2]['messages'],rows[0]['messages'])
            if spec.startswith('buried'):
                self.assertLess(rows[2]['messages'],rows[1]['messages'])

    def test_alarm_and_invalid_inputs(self):
        g=trap().graph;ev=CanonicalIntervals(g,UCTWork())
        ev.lower[3]=.99
        for _ in range(500):ev.observe(3,0.)
        self.assertTrue(ev.conflict)
        for reward in (-1,math.nan,2):
            with self.assertRaises(ValueError):ev.observe(3,reward)
        with self.assertRaises(ValueError):ev.observe(0,.5)
        with self.assertRaises(ValueError):RetiredBounds(g,UCTWork(),'unknown')
        b=RetiredBounds(g,UCTWork())
        with self.assertRaises(ValueError):b.publish(0,0,1)

    def test_terminal_root_and_query_frequency(self):
        g=DAG(((),));b=RetiredBounds(g,UCTWork())
        b.publish(0,.2,.8)
        self.assertEqual(b.query(),(-1,0.,.2,.8))
        p,trace,_=build_trace('shield8','shielded',1)
        for q in (1,7,32):
            rows=[run_replay(p,trace,m,80,True,query_every=q) for m in ('eager','cut','live')]
            self.assertEqual(len({r['output_sha256'] for r in rows}),1)
            self.assertEqual(len({r['first_certificate'] for r in rows}),1)


if __name__=='__main__':unittest.main()
