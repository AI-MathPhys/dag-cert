"""Frozen-family candidates: overlapping routing catalogs and natural SameGame."""
from collections import Counter
from functools import lru_cache
import random
from dagcert.graph import DAG, Problem, feature_lattice
from dagcert._core._samegame_engine import Game, Moves, finish
from experiment.simulated.passive_uct.uct_backup_families import funnel


def catalog(k,seed,profile):
    """Select a row/column class, then an admissible endpoint; all root sets distinct."""
    rng=random.Random(seed)
    rows=[()]
    grid=[]
    for i in range(k):
        grid.append(list(range(len(rows),len(rows)+k)))
        rows.extend([()] * k)
    groups=[]
    for items in grid+list(map(list,zip(*grid))):
        groups.append(len(rows));rows.append(tuple(items))
    # Both coordinate systems survive unary/equal-child simplification.
    actions=[]
    masks=[]
    for axis in range(2):
        available=list(range(axis*k,(axis+1)*k))
        seen=set()
        for j in range(k):
            while True:
                chosen=axis*k+j
                mask=tuple(sorted([chosen]+rng.sample([x for x in available if x!=chosen],max(1,k//2)-1)))
                if mask not in seen:
                    seen.add(mask);break
            masks.append(mask)
            actions.append(len(rows));rows.append(tuple(groups[i] for i in mask))
    # Direct near-rival and winner lengthen the public root decision independently.
    winner=len(rows);rows.append(())
    rival=len(rows);rows.append(())
    actions.extend((winner,rival));rng.shuffle(actions)
    rows[0]=tuple(actions)
    graph=DAG(rows)
    low=.12 if profile=='sparse' else .65
    means={v:low+.04*rng.random() for row in grid for v in row}
    means.update({winner:.82,rival:.75})
    return Problem('row-column catalog',graph,means),.05


def samegame(side,seed):
    rng=random.Random(seed)
    # Only legal root branching is screened. No score, support size or outcome screen.
    while True:
        board=tuple(tuple(rng.randrange(3) for _ in range(side)) for _ in range(side))
        if len(Moves()(board))>=2:break
    game=Game(board,2)
    moves=Moves()
    @lru_cache(None)
    def expected(b):
        options=moves(b)
        if not options:return float(finish(b))
        return sum(g+expected(nxt) for nxt,g in options)/len(options)
    game.means={j:(score+expected(b)+game.B)/game.scale
                for j in game.graph.leaves for b,score,_ in (game.states[j],)}
    # Exact (up to binary64 summation) finite uniform-playout expectation, audit only.
    game.audit_states=len(moves.cache)
    return game,.10


def make(family,size,seed):
    if family=='coded':
        return coded(size,seed)
    if family in ('sparse','dense'):
        return catalog(size,seed,family)
    if family=='samegame':
        return samegame(size,seed)
    if family=='lattice':
        return feature_lattice(size,True),.10
    if family=='funnel':
        return funnel(size,seed,noisy=True,gap=.10)
    raise ValueError(family)


class BoundedProblem(Problem):
    def oracle(self,seed):
        p=self
        class Oracle:
            def __init__(self):
                self.rng={v:random.Random((seed+1)*1000003+v*9176) for v in p.graph.leaves}
            def sample(self,j):
                return p.means[j]+.01*(2*self.rng[j].random()-1)
        return Oracle()


def coded(k,seed):
    """Hadamard coordinate catalogs: fragmented in every linear leaf layout."""
    if k<4 or k&(k-1):raise ValueError('power of two >=4')
    rows=[()];grid=[]
    for i in range(k):
        grid.append(list(range(len(rows),len(rows)+k)));rows.extend([()]*k)
    groups=[]
    for cells in grid+list(map(list,zip(*grid))):
        groups.append(len(rows));rows.append(tuple(cells))
    actions=[]
    for axis in range(2):
        for a in range(1,k):
            for parity in (0,1):
                actions.append(len(rows))
                rows.append(tuple(groups[axis*k+i] for i in range(k) if (a&i).bit_count()%2==parity))
    winner=len(rows);rows.append(());actions.append(winner)
    random.Random(seed).shuffle(actions);rows[0]=tuple(actions)
    means={j:.02 for row in grid for j in row};means[winner]=.99
    return BoundedProblem('coded coordinate catalog',DAG(rows),means),.20


def describe(problem):
    graph=problem.graph
    supports={}
    for v in reversed(graph.order):
        supports[v]=(frozenset((v,)) if not graph.children[v] else
                     frozenset().union(*(supports[c] for c in graph.children[v])))
    sets=[supports[a] for a in graph.children[graph.root]]
    memberships=sum(map(len,sets))
    return dict(nodes=len(graph),edges=sum(map(len,graph.children)),leaves=len(graph.leaves),
                root_actions=len(sets),unique_supports=len(set(sets)),
                memberships=memberships,mean_membership=memberships/len(graph.leaves),
                audit_states=getattr(problem,'audit_states',None))

