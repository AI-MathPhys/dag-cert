"""Stronger control: the same algebraic quotient with frozen Range-batch.

No witness machinery is constructed. Original action multiplicity and tie
ordering are retained in a small decision adapter, including unary nodes.
"""
from .graph import DAG
from .demand_bounds import make_backend


class QuotientRange:
    def __init__(self,graph,work,scale=1):
        self.graph,self.work,self.scale=graph,work,scale
        self.ids=[-1]*len(graph);self.groups=[None]*len(graph)
        self.query_epoch=[-1]*len(graph);self.query_cache=[None]*len(graph)
        rows=[];pool={};work.initialization+=4*len(graph)+6
        for v in reversed(graph.order):
            row=graph.children[v]
            if not row:
                self.ids[v]=len(rows);rows.append(());self.groups[v]=()
                work.initialization+=3;continue
            positions={}
            for a,c in enumerate(row):
                q=self.ids[c]
                if q in positions:positions[q]=(positions[q][0],True)
                else:positions[q]=(a,False)
                work.query_reads+=3;work.statistic_writes+=2
            distinct=tuple(positions);key=frozenset(distinct)
            work.query_reads+=4*len(distinct)+2
            if len(distinct)==1:i=distinct[0]
            elif key in pool:i=pool[key]
            else:
                i=len(rows);rows.append(distinct);pool[key]=i
                work.initialization+=2+len(distinct)
            self.ids[v]=i
            self.groups[v]=tuple((q,a,m) for q,(a,m) in positions.items())
            work.initialization+=3*len(positions)+1
        self.quotient=DAG(rows,root=self.ids[graph.root])
        # Validation, topological order, parents, and graph metadata are paid.
        work.initialization+=16*len(rows)+10*sum(map(len,rows))
        self.core=make_backend(self.quotient,work,'range_batch',scale)

    def publish(self,leaf,lo,hi):
        self.work.query_reads+=2
        self.core.publish(self.ids[leaf],lo,hi)

    def query(self,node=None):
        node=self.graph.root if node is None else node;epoch=self.core.epoch
        self.work.query_reads+=3
        if self.query_epoch[node]==epoch:return self.query_cache[node]
        groups=self.groups[node]
        if not groups:
            lo,hi=self.core.interval(self.ids[node]);answer=(-1,0.,lo/self.scale,hi/self.scale)
            self.work.query_reads+=2
        else:
            pairs=[self.core.interval(q) for q,_,_ in groups]
            leader=max(range(len(groups)),key=lambda i:pairs[i][0])
            lo=pairs[leader][0];hi=max(u for _,u in pairs)
            rival=max((u for i,(_,u) in enumerate(pairs) if i!=leader or groups[i][2]),default=lo)
            answer=(groups[leader][1],max(0.,(rival-lo)/self.scale),lo/self.scale,hi/self.scale)
            self.work.query_reads+=4*len(groups)+4
        self.query_cache[node]=answer;self.query_epoch[node]=epoch;self.work.statistic_writes+=2
        return answer
