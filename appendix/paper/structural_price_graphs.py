"""Controlled index layouts of the same four-action fragmented decision problem."""
from dag_mcts.graph import DAG, Problem
from paper.decision_price_benchmark import factory


def logical_fixture(s):
    """Return a spread layout; subsequent layouts only permute this labeled problem."""
    graph = factory(s)()
    leaves = graph.graph.leaves
    ranks = list(range(len(leaves)))
    winner, rival = sorted(ranks, key=lambda j: graph.means[leaves[j]], reverse=True)[:2]
    # Put the two distinguished *pairs* at opposite ends, keeping every pair intact.
    pairs = [ranks[i:i+2] for i in range(0,len(ranks),2)]
    if winner//2 == rival//2:
        # The cyclic distinguished neighboring owner sets intersect, whereas the
        # prospects have complementary owners in this four-action generator.
        raise ValueError('expected distinct logical prospect pairs')
    arranged = [pairs[winner//2]] + [pair for i,pair in enumerate(pairs)
                                      if i not in (winner//2,rival//2)] + [pairs[rival//2]]
    order = [j for pair in arranged for j in pair]
    base = permute(graph, order, 'spread')
    means = dict(base.means)
    for j,leaf in enumerate(leaves):
        if means[leaf] < .3:
            means[leaf] = .01 + .02*j/(len(leaves)-1)
    return Problem('spread',base.graph,means,leaves)


def permute(p, order, name):
    leaves=p.graph.leaves
    assert sorted(order)==list(range(len(leaves)))
    mapping={leaves[j]:leaves[k] for k,j in enumerate(order)}
    graph=DAG([p.graph.children[0],
               *(tuple(sorted(mapping[j] for j in children)) for children in p.graph.children[1:5]),
               *([()]*len(leaves))])
    return Problem(name,graph,{mapping[j]:value for j,value in p.means.items()},graph.leaves)


def layout(p, kind, chunk=8):
    leaves=p.graph.leaves
    masks=[sum(1<<a for a,ch in enumerate(p.graph.children[1:5]) if j in ch) for j in leaves]
    w,r=sorted(range(len(leaves)),key=lambda j:p.means[leaves[j]],reverse=True)[:2]
    order=list(range(len(leaves)))
    if kind=='spread':
        return p
    if kind=='neighbors':
        # Change only the rival and the winner's sibling. This controls join depth
        # while keeping the unlabeled supports, observations and gap fixed.
        k=w^1
        order[k],order[r]=order[r],order[k]
    elif kind=='short-runs':
        order=[]
        for subset in sorted(set(mask&masks[w] for mask in masks)):
            groups={}
            for j,mask in enumerate(masks):
                if mask&masks[w]==subset:
                    groups.setdefault(mask,[]).append(j)
            for start in range(0,max(map(len,groups.values())),chunk):
                for mask in sorted(groups):
                    order.extend(groups[mask][start:start+chunk])
    else:
        raise ValueError(kind)
    return permute(p,order,kind)


def switched(p,bits):
    """Apply independent within-pair transpositions, preserving dyadic geometry."""
    order=list(range(len(p.graph.leaves)))
    assert len(bits)==len(order)//2
    for k,flip in enumerate(bits):
        if flip:
            order[2*k],order[2*k+1]=order[2*k+1],order[2*k]
    return permute(p,order,'sibling permutation')
