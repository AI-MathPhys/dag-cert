"""Matched input and cold search loop for wall-time measurements."""
import hashlib
import random
from paper.partial_benchmark import config, prior, Problem
from paper.escrow_clearing import GuardedSearch
from paper.partial_clearing import PartialSearch
from paper.frontier_sampling import Search


def make_input(family,level,price,seed):
    c=config(family,level,price)
    offset={'fragmented_sparse':21000,'fragmented_dense':31000,'fragmented_shoulder':41000}.get(family,0)
    p=prior.problem(c,seed+offset)
    if c.get('shoulder'):
        rng=random.Random(seed+offset+303)
        means=dict(p.means)
        for leaf in rng.sample([x for x,v in means.items() if v<.7],8):
            means[leaf]=rng.uniform(.49,.64)
        p=Problem(c['id'],p.graph,means)
    return c,p


def fingerprint(p,seed):
    return hashlib.sha256(repr((p.graph.children,sorted(p.means.items()),seed)).encode()).hexdigest()


def original(p,c,seed,method):
    if method=='range':
        return Search(p,c,seed,'range_lucb32')
    if method=='partial':
        return PartialSearch(p,c,seed,'partial')
    raise ValueError(method)


def execute(p,c,seed,method,factory=original):
    """One uninterrupted cold solve; exclude only input generation and external audit."""
    search=factory(p,c,seed,method)
    point=search.query()
    while not point[1] and search.w.total<c['max_work'] and search.w.oracle_calls<c['max_observations']:
        _,point=search.step(c['max_observations']-search.w.oracle_calls)
    if isinstance(search,GuardedSearch) and search.trial is not None:
        search.close('abort_cap')
    return search,point
