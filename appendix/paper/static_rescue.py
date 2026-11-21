"""Keep static admissions. Optionally rescue a declined case at one later persistent query."""
import json
from pathlib import Path
from paper.frontier_gate_features import decision
from paper.frontier_gate_race import MODEL

ROOT=Path(__file__).resolve().parents[1]
MODEL_PATH=ROOT/'paper/static_rescue_model.json'
STATIC=('actions','load','first_spans','terminals')
SIGNALS=('deficit','anchor_fraction','outside_fraction','inside_fraction','anchor_mean',
         'lag','switches','inside_fraction_of_leaves')
def review_query(m):
    return 1+m

def feature(lane,name):
    s=lane.engine;i=s.idx;m=len(s.g.leaves)
    if name=='actions':return len(i.top.inside)
    if name=='load':
        eps=s.c['epsilon']
        return 1/(m*eps*eps)  # Use exactly the frozen static comparator's operation order.
    if name=='terminals':return m
    if name=='first_spans':return len(i.top.inside[0])
    if name=='deficit':return (s.point[4][0]-s.point[2])/s.tol
    if name=='lag':return (i.best-s.point[2])/s.tol
    if name=='switches':return i.switches
    if name=='inside_fraction_of_leaves':return len(i.groups[1])/m
    if name in ('anchor_fraction','anchor_mean'):j=i.anchor
    elif name=='inside_fraction':j=s.point[3][1]
    elif name=='outside_fraction':j=s.point[4][1]
    else:raise KeyError(name)
    leaf=s.g.leaves[j]
    if name=='anchor_mean':return s.ev.sums[leaf]/max(1,s.ev.counts[leaf])
    return s.ev.counts[leaf]/s.N

def static_choice(lane):
    load=feature(lane,'load')
    return decision(MODEL['static'],{'precision_load':load}),load

def apply_tree(tree,lane):
    seen={}
    node=tree
    while 'feature' in node:
        key=node['feature']
        if key not in seen:seen[key]=feature(lane,key)
        node=node['left'] if seen[key]<=node['threshold'] else node['right']
    return node['admit'],seen

def controller(model,mode='rescue'):
    if mode not in ('rescue','geometry','union','trim','retry_all','static_only'):
        raise ValueError(mode)
    def gate(lane,later):
        if not later:
            allow,load=static_choice(lane)
            if allow and mode=='trim':
                veto,details=apply_tree(model['veto'],lane)
                return not veto,dict(details,load=load,stage='veto'),None
            next_q=None if allow or mode=='static_only' else review_query(len(lane.engine.g.leaves))
            return allow,{'load':load,'stage':'static'},next_q
        if mode=='retry_all':return True,{'stage':'retry_all'},None
        if mode in ('union','trim'):
            allow,features=apply_tree(model['geometry'],lane)
            if not allow:
                allow,signal=apply_tree(model['rescue'],lane)
                features.update(signal)
        else:allow,features=apply_tree(model[mode],lane)
        return allow,dict(features,stage='rescue'),None
    return gate

