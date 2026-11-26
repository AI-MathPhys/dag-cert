"""Cold DAGs for the on-policy selective-backup comparison."""
import random
from joint_root_cert.graph import DAG, Problem, feature_lattice
from joint_root_cert._core.backprop_problems import reconvergent


def binary_root(rows, nodes):
    """Join a power of two equally deep children without changing action order."""
    while len(nodes)>1:
        parents = []
        for j in range(0,len(nodes),2):
            parents.append(len(rows))
            rows.append((nodes[j],nodes[j+1]))
        nodes = parents
    return nodes[0]


def funnel(width, seed, noisy=False, placement='low', exits=1, gap=None):
    if width<2 or width & (width-1):
        raise ValueError('power-of-two funnel width required')
    gap = .25*width**(-1/16) if gap is None else gap
    rows = [(),(),(),()]
    means = {1:.75,2:.75-gap,3:.25}
    if exits==2:
        rows.append(())
        means.update({3:.125,4:.375})
    bottom = []
    for i in range(width):
        target = 1 if placement=='best' else 3+int(exits==2 and i>=width//2)
        bottom.append(len(rows))
        rows.append((target,))
    top = binary_root(rows,bottom)
    actions = [top,2,3] if placement=='best' else [1,2,top]
    random.Random(seed).shuffle(actions)
    rows[0] = actions
    graph = DAG(rows)
    problem = Problem('funnel',graph,means,() if noisy else graph.leaves)
    return problem,gap/2


def wide_core(r,seed):
    if r<2 or r & (r-1):
        raise ValueError('power-of-two core factor required')
    rows = [(),()]
    leaves = list(range(2,r*r+2))
    rows.extend([()]*(r*r))
    hub = binary_root(rows,leaves)
    actions = [1]
    for _ in range(r):
        own = len(rows)
        rows.append(())
        actions.append(len(rows))
        rows.append((hub,own))
    random.Random(seed).shuffle(actions)
    rows[0] = actions
    graph = DAG(rows)
    means = {leaf:float(leaf==1) for leaf in graph.leaves}
    return Problem('wide core',graph,means,graph.leaves),.20


def fixture(family, size, seed):
    if family in ('funnel','noisy'):
        return funnel(size,seed,noisy=(family=='noisy'))
    if family=='two-exit':
        return funnel(size,seed,exits=2)
    if family=='live-best':
        return funnel(size,seed,placement='best')
    if family=='fixed-gap':
        return funnel(size,seed,gap=.10)
    if family=='core':
        return wide_core(size,seed)
    if family=='lattice':
        return feature_lattice(size,True),.08
    if family=='merge':
        return reconvergent(size,6),.08
    raise ValueError(family)

