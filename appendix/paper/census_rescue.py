"""Budgeted empirical contender count added after the static and geometry decisions."""
from paper.static_rescue import controller,feature

class Census:
    def __init__(self,model):
        self.base=controller(model,'union')
    def funded_review(self,lane,later,credit):
        admit,details,next_query=self.base(lane,later)
        if not later or admit:return admit,details,next_query,0
        load=details.get('load')
        if load is None:load=feature(lane,'load')
        actions=feature(lane,'actions')
        if actions<4 or not 19.53125<load<=40.625:return False,details,None,0
        s=lane.engine;cost=10*len(s.g.leaves)+2*actions+32
        if cost>credit:return False,dict(details,census='unfunded'),None,0
        threshold=s.idx.best/s.c['K']-s.c['epsilon']
        if threshold<=0 or max(map(len,s.idx.top.inside))<8:
            return False,dict(details,census='ineligible',charge=cost),None,cost
        contenders=0
        for leaf in s.g.leaves:
            count=s.ev.counts[leaf]
            if not count or s.ev.sums[leaf]/count>=threshold:
                contenders+=1
                if contenders>s.c['cap']:break
        return contenders<=s.c['cap'],dict(details,census=contenders,charge=cost,threshold=threshold),None,cost

