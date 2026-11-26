"""Demanded, shared monotone upper-threshold certificates on a known MAX DAG.

The API answers U(node) >= integer level, NOT an exact numerical maximum.
Watch mode subscribes only to a current true child predicate. Truth changes
once (true to false); a child changing its witness without changing its truth
does not invalidate ancestors. Direct mode is a strong lazy control: canonical
terminal witnesses, shared memoization, permanent false caches and cursors.
Both use an iterative evaluator and support deep DAGs without recursion.
"""
from collections import deque
from dataclasses import dataclass, field


@dataclass
class _Predicate:
    node: int
    level: int
    cursor: int = 0
    value: object = None
    witness: int = -1
    terminal: int = -1
    listeners: list = field(default_factory=list)


class DemandThreshold:
    def __init__(self, graph, work, scale=40, mode='watch'):
        if not isinstance(scale,int) or scale < 1 or mode not in ('watch','direct'):
            raise ValueError('Need integer resolution and watch/direct mode')
        self.graph,self.work,self.scale,self.mode=graph,work,scale,mode
        self.bounds={}; self.index={}; self.states=[]
        self.terminal_levels={}; self.queue=deque()
        self.edge_examinations=self.activations=self.notifications=self.crossings=0
        self.work.initialization+=12

    def publish(self,leaf,lo,hi):
        self.work.query_reads+=4
        oldlo,oldhi=self.bounds.get(leaf,(0,self.scale))
        if (self.graph.children[leaf] or not isinstance(lo,int) or not isinstance(hi,int)
                or not oldlo<=lo<=hi<=oldhi):
            raise ValueError('Need nested integer terminal endpoints')
        self.bounds[leaf]=(lo,hi);self.work.statistic_writes+=1
        if self.mode=='watch' and leaf in self.terminal_levels:
            # Across the whole run a terminal crosses each integer level once.
            levels=self.terminal_levels[leaf]
            for k in range(hi+1,oldhi+1):
                self.crossings+=1;self.work.query_reads+=1
                sid=levels.get(k)
                if sid is not None:self._false(sid)

    def _new(self,node,level):
        sid=len(self.states);self.index[node,level]=sid
        self.states.append(_Predicate(node,level));self.activations+=1
        self.work.initialization+=9
        if not self.graph.children[node]:
            if self.mode=='watch':self.terminal_levels.setdefault(node,{})[level]=sid
            self.work.statistic_writes+=1
        return sid

    def _valid(self,sid):
        state=self.states[sid];self.work.query_reads+=2
        if state.value is None:return False
        if self.mode=='watch' or not state.value:return True
        self.work.query_reads+=2
        return self.bounds.get(state.terminal,(0,self.scale))[1]>=state.level

    def _ensure(self,node,level):
        sid=self.index.get((node,level));self.work.query_reads+=1
        if sid is None:sid=self._new(node,level)
        stack=[sid];self.work.statistic_writes+=1
        while stack:
            i=stack[-1];s=self.states[i]
            if self._valid(i):stack.pop();self.work.statistic_writes+=1;continue
            row=self.graph.children[s.node];self.work.query_reads+=1
            if not row:
                s.value=self.bounds.get(s.node,(0,self.scale))[1]>=s.level
                s.terminal=s.node;s.witness=-1;stack.pop()
                self.work.query_reads+=1;self.work.statistic_writes+=4
                continue
            if s.cursor==len(row):
                s.value=False;s.terminal=-1;stack.pop();self.work.statistic_writes+=3
                continue
            child=row[s.cursor];key=(child,s.level)
            j=self.index.get(key);self.work.query_reads+=2
            if j is None:j=self._new(*key)
            if not self._valid(j):stack.append(j);self.work.statistic_writes+=1;continue
            self.edge_examinations+=1;self.work.edge_reads+=1
            if self.states[j].value:
                s.value=True;s.witness=j;s.terminal=self.states[j].terminal
                if self.mode=='watch':self.states[j].listeners.append(i)
                stack.pop();self.work.statistic_writes+=5
            else:
                s.cursor+=1;self.work.statistic_writes+=1
        return sid

    def _false(self,sid):
        s=self.states[sid];self.work.query_reads+=1
        if s.value:
            s.value=False;self.queue.append(sid);self.work.statistic_writes+=2

    def flush(self):
        while self.queue:
            child=self.queue.popleft();self.work.statistic_writes+=1
            for parent in self.states[child].listeners:
                self.notifications+=1;self.work.query_reads+=3
                s=self.states[parent]
                if not s.value or s.witness!=child:continue
                # The old child is permanently false; never examine it again.
                s.cursor+=1;self.work.statistic_writes+=1
                row=self.graph.children[s.node]
                found=False
                while s.cursor<len(row):
                    nxt=self._ensure(row[s.cursor],s.level)
                    self.edge_examinations+=1;self.work.edge_reads+=1
                    if self.states[nxt].value:
                        s.witness=nxt;self.states[nxt].listeners.append(parent)
                        self.work.statistic_writes+=2;found=True;break
                    s.cursor+=1;self.work.statistic_writes+=1
                if not found:self._false(parent)
            self.states[child].listeners.clear()
            self.work.statistic_writes+=1

    def has_high(self,node,level):
        if not isinstance(level,int):raise ValueError('Threshold level must be an integer')
        self.work.query_reads+=2
        if level<=0:return True
        if level>self.scale:return False
        if self.mode=='watch':self.flush()
        sid=self._ensure(node,level)
        if self.mode=='watch':self.flush()
        return bool(self.states[sid].value)

    def certify(self,node,action,lower,tolerance):
        """Verify a supplied valid lower bound for the proposed action.

        The caller must substantiate `lower` (e.g. a sampled terminal reached
        by a validated path from that action). This method does not validate
        a path or select a candidate. Both lower and tolerance are grid units.
        """
        row=self.graph.children[node]
        if (not 0<=action<len(row) or not isinstance(lower,int)
                or not isinstance(tolerance,int) or not 0<=lower<=self.scale
                or tolerance<0):raise ValueError('Invalid candidate certificate request')
        self.work.query_reads+=4
        for a,child in enumerate(row):
            self.work.edge_reads+=1
            if a!=action and self.has_high(child,lower+tolerance+1):return False
        return True
