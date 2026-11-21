"""Cold finite peg-solitaire planning problems and hidden-good fragmented inputs."""
import itertools
import random
from fractions import Fraction
from functools import lru_cache
from dag_mcts.graph import DAG, Problem

CELLS=tuple((r,c) for r in range(5) for c in range(r+1))
JUMPS=[]
for start,(r,c) in enumerate(CELLS):
    for dr,dc in ((1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1)):
        mid,end=(r+dr,c+dc),(r+2*dr,c+2*dc)
        if mid in CELLS and end in CELLS:
            JUMPS.append(((1<<start)|(1<<CELLS.index(mid)),1<<CELLS.index(end)))
assert len(JUMPS)==36

class Rules:
    def __init__(self):
        self.cache={};self.operations=0
    def children(self,state):
        self.operations+=1
        if state not in self.cache:
            self.cache[state]=tuple(state^pair^end for pair,end in JUMPS
                                    if state&pair==pair and not state&end)
            self.operations+=3*len(JUMPS)+len(self.cache[state])
        return self.cache[state]

def orbit(board):
    def transform(perm):
        val=0
        for k,(r,c) in enumerate(CELLS):
            if board>>k&1:
                bary=(c,r-c,4-r)
                a,b=(bary[perm[i]] for i in (0,1))
                val|=1<<CELLS.index((a+b,a))
        return val
    return min(transform(p) for p in itertools.permutations(range(3)))

def positions():
    rules=Rules();start=[32767^(1<<i) for i in range(15)]
    openings=sorted({orbit(b) for b in start});level=set(start)
    for _ in range(3):level={child for b in level for child in rules.children(b)}
    eligible=sorted({orbit(b) for b in level if len(rules.children(b))>=2})
    midgames=sorted(random.Random(211503).sample(eligible,8))
    return [('opening',b,h) for b in openings for h in (3,6)]+[('midgame',b,h) for b in midgames for h in (3,5)]

class PegProblem:
    def __init__(self,board,h):
        self.rules=Rules();self.boards=[board];rank={board:0};rows=[]
        for b in self.boards:
            children=self.rules.children(b) if board.bit_count()-b.bit_count()<h else ()
            row=[]
            for z in children:
                if z not in rank:
                    rank[z]=len(rank);self.boards.append(z)
                row.append(rank[z])
            rows.append(tuple(row))
        self.graph=DAG(rows)
        self.build_work=self.rules.operations+4*len(rows)+5*sum(map(len,rows))
    def oracle(self,seed):
        return Rollout(self,seed)

class Rollout:
    def __init__(self,p,seed):
        self.p=p;self.calls=0;self.jumps=0
        self.tapes={j:random.Random((seed+1)*1000003+p.boards[j]*9176) for j in p.graph.leaves}
        self.base_work=p.rules.operations
    @property
    def operations(self):
        return self.p.rules.operations-self.base_work+4*self.jumps+self.calls
    def sample(self,j):
        self.calls+=1
        b=self.p.boards[j];rng=self.tapes[j]
        while (children:=self.p.rules.children(b)):
            b=children[rng.randrange(len(children))];self.jumps+=1
        return float(b.bit_count()==1)

def exact_peg(board,h):
    rules=Rules()
    @lru_cache(None)
    def value(b):
        cs=rules.children(b)
        if not cs:return Fraction(int(b.bit_count()==1))
        vals=[value(z) for z in cs]
        if board.bit_count()-b.bit_count()<h:return max(vals)
        return sum(vals,Fraction())/len(cs)
    actions=[value(z) for z in rules.children(board)]
    return actions,len(rules.cache)

def fragmented(seed,good,gap_mult,noise,M=256,A=32):
    if M%2 or A%2 or not 1<=good<=A//2:raise ValueError('invalid sizes')
    rng=random.Random(seed)
    action_order=list(range(A));rng.shuffle(action_order)
    owners=[{action_order[(k+j)%A] for j in range(good)} for k in range(A)]
    for j in range((M-A)//2):
        half=set(rng.sample(range(A),A//2))
        owners.extend((half,set(range(A))-half))
    winner=rng.randrange(A)
    rival=rng.choice([k for k in range(A) if not(owners[k]&owners[winner])])
    vals=[rng.uniform(.05,.25) for _ in range(M)]
    vals[winner]=.70;vals[rival]=.70-.05*gap_mult
    pairs=list(range(M//2));rng.shuffle(pairs)
    ranks=[2*k+j for k in pairs for j in (0,1)]
    offset=A+1
    children=[tuple(range(1,A+1))]
    children.extend(tuple(offset+j for j,i in enumerate(ranks) if a in owners[i]) for a in range(A))
    children.extend([()]*M);g=DAG(children)
    p=Problem('fragment',g,{offset+j:vals[i] for j,i in enumerate(ranks)},
              () if noise=='bernoulli' else g.leaves)
    return p

