"""Single-checkpoint gate. Persistent runs unchanged; a cold Compact lane spends earned credit."""
from collections import deque
import json
import random
import time
from paper.cold_decision_solvers import create
from paper.compact_partial import FastPartial
from paper.peg_fragment_benchmark import ROOT
from paper.frontier_gate_features import checkpoint,decision

MODEL=json.loads((ROOT/'paper/frontier_gate_model.json').read_text())
BUDGET=102_400_000
DRAWS=262144
SECONDS=12.
def dispose_cells(root,shared):
    """Explicit reference-slot tariff for releasing private Python containers."""
    seen={id(x) for x in shared};stack=[root];cost=0
    while stack:
        obj=stack.pop()
        if id(obj) in seen:continue
        seen.add(id(obj))
        if isinstance(obj,dict):
            cost+=1+2*len(obj);stack.extend(obj.keys());stack.extend(obj.values())
        elif isinstance(obj,(list,tuple,deque,set,frozenset)):
            cost+=1+len(obj);stack.extend(obj)
        elif isinstance(obj,random.Random):
            cost+=1  # one fixed-size native handle
        elif type(obj).__module__.startswith(('paper.','dag_mcts.')):
            stack.append(vars(obj));cost+=1
    return cost

class AuditedCompact(FastPartial):
    def close(self,reason):
        if reason=='decision':
            self.private_box=self.trial.inside_lower,self.trial.outside.value[1]
        return super().close(reason)

class Lane:
    def __init__(self,p,c,seed,method):
        self.engine=AuditedCompact(p,c,seed) if method=='compact' else create(p,c,seed,method)
        self.oracle=self.engine.oracle
        self.point=self.engine.query()
        self.peak=0;self.seal_at=None;self.conflict=False
    @property
    def work(self):
        return self.engine.w.total+getattr(self.oracle,'operations',0)
    @property
    def draws(self):return self.engine.w.oracle_calls
    def advance(self,left):
        before=self.work
        try:_,self.point=self.engine.step(left)
        except ArithmeticError:
            if not (self.engine.ev.conflict or (getattr(self.engine,'trial',None) and self.engine.trial.evidence.conflict)):raise
            self.conflict=True
        # Keep only the two integer witnesses of a discarded private decision.
        if getattr(self.engine,'meta',{}).get('decision'):
            self.private=self.engine.private_box
        if self.seal_at is None and getattr(self.engine,'meta',{}).get('seal'):
            self.seal_at=self.work
        self.peak=max(self.peak,self.work-before)
    def box(self):
        s=self.engine;a=self.point[0]
        if getattr(s,'meta',{}).get('decision'):return self.private
        ins={j for lo,hi in s.idx.top.inside[a] for j in range(lo,hi)}
        return (max(s.idx.lower[j] for j in ins),
                max((u for j,u in enumerate(s.idx.upper) if j not in ins),default=-1))
    def retire(self,p,c):
        s=self.engine
        charge=dispose_cells(s,(p,p.graph,c))
        before=self.work
        if getattr(s,'trial',None) is not None:s.close('abort_cap')
        charge+=self.work-before
        # Buffered ordinary dispatch can hold a bound method of the engine.
        s.__dict__.pop('observe',None)
        self.engine=None;self.oracle=None
        return charge

def policy_value(p,mode,M,eps):
    if mode=='blind':return True,{}
    if mode=='early':
        features={'width':(p.point[4][0]-p.point[2])/p.engine.tol}
    else:
        features={'precision_load':1/(M*eps*eps)}
    return decision(MODEL[mode],features),features

def solve(make_problem,c,seed,method,*,controller=None):
    start=time.perf_counter();p=make_problem();build=getattr(p,'build',0)
    race=controller is not None or method in ('early','static','blind')
    base=Lane(p,c,seed,'persistent' if race else method);alt=None
    pfee=12 if race else 0;cfee=0;monitor=0;quantum=0;max_debt=0
    decision_log=None;admit=False;qgate=checkpoint(len(p.graph.leaves))
    while True:
        pw=build+base.work;cw=alt.work+cfee if alt else 0
        total=pw+cw+pfee+monitor
        calls=base.draws+(alt.draws if alt else 0)
        if (base.point[1] or base.conflict or (alt and (alt.point[1] or alt.conflict))
            or total>=BUDGET or calls>=DRAWS or time.perf_counter()-start>=SECONDS):break
        if race and qgate is not None and base.engine.idx.q>=qgate:
            allowed=32<=pw//16
            next_query=None
            if controller is not None and allowed:
                if hasattr(controller,'funded_review'):
                    # Spend only the part of the existing dispatch allowance
                    # that earlier full persistent blocks have already earned.
                    credit=max(0,pw//100-(pfee-12))
                    admit,features,next_query,spent=controller.funded_review(base,decision_log is not None,credit)
                    if not 0<=spent<=credit:raise ValueError('unfunded review')
                    pfee+=spent
                else:admit,features,next_query=controller(base,decision_log is not None)
                if next_query is not None and (admit or next_query<=base.engine.idx.q or decision_log is not None):
                    raise ValueError('Expected at most one later review after a rejection')
            else:
                admit,features=policy_value(base,method,len(p.graph.leaves),c['epsilon']) if allowed else (False,{})
            if allowed:monitor=32
            previous=decision_log
            decision_log=dict(admit=admit,eligible=allowed,features=features,prefix_work=pw,
                              prefix_draws=base.draws,q=base.engine.idx.q,time=time.perf_counter()-start)
            if previous is not None:decision_log['initial']=previous
            qgate=next_query
        if admit and cw<=pw:
            before=cw
            if alt is None:alt=Lane(p,c,seed,'compact')
            else:alt.advance(DRAWS-calls)
            cfee+=8
            new=alt.work+cfee
            quantum=max(quantum,new-before)
            max_debt=max(max_debt,new-pw)
        else:
            base.advance(DRAWS-calls)
            if race:pfee+=8
    # Save stopping witness and counters. An independent verifier rechecks
    # evidence outside the timed runs; this constant-size query witness is free to read.
    winner=alt if alt and alt.point[1] else base if base.point[1] else None
    box=None
    if winner is not None:
        a,good,lo,_,y=winner.point
        box=getattr(winner,'private',None) if y is None else (lo,y[0])
        if box is None or box[1]-box[0]>winner.engine.tol:raise AssertionError('invalid returned witness')
    pw=build+base.work;cw=alt.work+cfee if alt is not None else 0
    # Includes cancellation of a speculative trial and the container disposal
    # tariff for both lanes. Their Python engine state is dropped inside timing.
    pdraw=base.draws;cdraw=alt.draws if alt else 0
    pseal=base.seal_at;cseal=alt.seal_at if alt else None
    conflict=base.conflict or bool(alt and alt.conflict)
    action=winner.point[0] if winner else None
    lane='compact' if winner is alt and alt is not None else 'base' if winner else None
    pdrop=base.retire(p,c);cdrop=alt.retire(p,c) if alt else 0
    elapsed=time.perf_counter()-start
    work=pw+cw+pfee+monitor+pdrop+cdrop
    status=('conflict' if conflict else 'wall' if elapsed>SECONDS else 'work' if work>BUDGET
            else 'certified' if winner else 'draw' if pdraw+cdraw>=DRAWS else 'work')
    if race and cw>pw+quantum:raise AssertionError('credit overrun')
    if race and monitor>pw/16:raise AssertionError('monitor credit')
    if race and pfee>20+.01*pw:raise AssertionError('protected dispatch bound')
    return dict(status=status,seconds=elapsed,work=work,action=action if status=='certified' else None,
                box=box if status=='certified' else None,prefix_or_full_P=pw,C=cw,pdrop=pdrop,cdrop=cdrop,
                pfee=pfee,fee=monitor,quantum=quantum,debt=max_debt,base_draws=pdraw,alt_draws=cdraw,
                base_seal=pseal,alt_seal=cseal,lane=lane,gate=decision_log,build=build)

