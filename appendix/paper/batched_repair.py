"""Coalesced public index maintenance for the existing paired samplers."""
from paper.ancestor_repair_replay import Profile
from paper.compact_pre import FusedTree, FastPreCompact, FastPreRange


class BatchTree(FusedTree):
    @classmethod
    def from_index(cls, tree, increasing, account):
        result=cls.from_tree(tree)
        result.increasing=increasing
        result.account=account
        result.active=False
        result.profile=None
        result.events=([],[])
        return result

    def begin(self, pair, priced):
        self.active=True
        self.pair=pair
        self.priced=priced
        self.n0=self.n1=0
        self.v0=self.value[self.size+pair[0]]
        self.v1=self.value[self.size+pair[1]]

    def update(self, i, value):
        if not self.active:
            # Private commits and any publication outside an ordinary pair.
            self.profile=None
            return super().update(i,value)
        if i==self.pair[0]:
            if value==self.v0:
                return
            if self.priced:
                self.events[0].append((max(value,self.v0),self.v1))
            self.v0=value
            self.n0+=1
        elif i==self.pair[1]:
            if value==self.v1:
                return
            if self.priced:
                self.events[1].append((max(value,self.v1),self.v0))
            self.v1=value
            self.n1+=1
        else:
            raise ValueError('ordinary publication outside fixed pair')

    def price_group(self, side, events, peer_old, peer_new):
        """Reconstruct the eager visits. No eager parents are actually repaired."""
        profile=self.profile
        pos=profile.cursor[side]
        price=pulls=0
        if len(events)>=4:
            first,last=events[0][0],events[-1][0]
            probe,a,c0=profile.lookup(side,first,pos)
            probe,b,c1=profile.lookup(side,last,probe)
            price=c0+c1+8
            independent = a==b and a<=profile.join
            if independent:
                profile.cursor[side]=probe
                return a*len(events),price+3
            if peer_old==peer_new:
                price+=6
                start=profile.depth(a,peer_old,first)
                end=profile.depth(b,peer_old,last)
                if start==end:
                    profile.cursor[side]=probe
                    return start*len(events),price+3
        for x,peer in events:
            pos,depth,cost=profile.lookup(side,x,pos)
            pulls+=min(depth,profile.join) if peer>x else depth
            price+=cost+5
        profile.cursor[side]=pos
        return pulls,price

    def climb(self, node, stop):
        """Repair until the shared ancestor or the first unchanged state."""
        values,counts=self.value,self.count
        visits=0
        while node!=stop:
            left=2*node
            right=left+1
            a,b=values[left],values[right]
            if a>b:
                high,ties=a,counts[left]
            elif b>a:
                high,ties=b,counts[right]
            else:
                high,ties=a,counts[left]+counts[right]
            visits+=1
            if high==values[node] and ties==counts[node]:
                return visits,False
            values[node],counts[node]=high,ties
            node//=2
        return visits,True

    def flush(self):
        self.active=False
        n=self.n0+self.n1
        if not n:
            return
        pair=self.pair
        a,b=self.size+pair[0],self.size+pair[1]
        priced=self.priced
        price=pulls=0
        if priced:
            if self.profile is None or self.profile.pair!=pair:
                self.profile=Profile(self,pair,self.increasing)
                price+=16*self.profile.h+16
            if self.n0:
                k,cost=self.price_group(0,self.events[0],self.value[b],self.v1)
                pulls+=k
                price+=cost
                self.events[0].clear()
            if self.n1:
                k,cost=self.price_group(1,self.events[1],self.value[a],self.v0)
                pulls+=k
                price+=cost
                self.events[1].clear()
        dirty=int(self.n0>0)+int(self.n1>0)
        if self.n0:
            self.value[a],self.count[a]=self.v0,1
        if self.n1:
            self.value[b],self.count[b]=self.v1,1
        if dirty==1:
            visits,_=self.climb((a if self.n0 else b)//2,0)
        else:
            join=a>>(a^b).bit_length()
            va,ra=self.climb(a//2,join)
            vb,rb=self.climb(b//2,join)
            visits=va+vb
            if ra or rb:
                vc,_=self.climb(join,0)
                visits+=vc
        w=self.w
        # Keep the reference clock only where it can affect sampling.
        billed_pulls=pulls if priced else visits
        billed_leaves=n if priced else dirty
        w.query_reads+=n+6*billed_pulls
        w.heap_comparisons+=4*billed_pulls
        w.heap_writes+=2*billed_leaves+2*billed_pulls
        self.account.extra+=8+4*dirty+4*visits
        if priced:
            self.account.extra+=2*n+price+2*dirty+12*visits
            self.account.saved+=2*n+12*pulls


class BatchBlocks:
    def prepare_batch(self, compact):
        idx=self.idx
        idx.lt=BatchTree.from_index(idx.lt,True,self.account)
        idx.ut=BatchTree.from_index(idx.ut,False,self.account)
        self.can_clear=compact and any(len(side)>=8 for side in idx.top.inside)
        self.batch_open=False
        self.account.extra+=32+(2*len(idx.top.inside)+4 if compact else 0)
        self.account.batch_blocks=0
        self.account.priced_blocks=0

    def ordinary(self, remaining):
        if getattr(self,'compact',None) is not None:
            return super().ordinary(remaining)
        priced=self.can_clear and not self.ended
        pair=self.pair if self.pair[0]<self.pair[1] else (self.pair[1],self.pair[0])
        self.idx.lt.begin(pair,priced)
        self.idx.ut.begin(pair,priced)
        self.batch_open=True
        self.account.extra+=8
        self.account.batch_blocks+=1
        self.account.priced_blocks+=int(priced)
        try:
            return super().ordinary(remaining)
        finally:
            # The normal query flushes first. A conflict or bad observation
            # can also leave a legal prefix that must be charged and repaired.
            if self.batch_open:
                self.finish_batch()

    def finish_batch(self):
        self.idx.lt.flush()
        self.idx.ut.flush()
        self.batch_open=False

    def query(self):
        if self.batch_open:
            self.finish_batch()
        return super().query()


class BatchedCompact(BatchBlocks,FastPreCompact):
    def __init__(self,p,c,seed):
        super().__init__(p,c,seed,receipts=False,fused=True)
        self.prepare_batch(True)


class BatchedRange(BatchBlocks,FastPreRange):
    def __init__(self,p,c,seed):
        super().__init__(p,c,seed,receipts=False,fused=True)
        self.prepare_batch(False)

