"""Reconverging internal-state problems plus the unchanged UCT benchmark cases."""
from .graph import DAG, Problem
from .uct_problems import problem_spec as old_spec


def reconvergent(width=64, depth=8, shared=True, gap=.25):
    if width<2 or depth<1 or not 0<gap<.6:
        raise ValueError("Invalid reconvergence parameters")
    rows=[[],[],[]]
    means={}
    def add(children=()):
        node=len(rows);rows.append(list(children));return node
    if shared:
        leaf=add();means[leaf]=.15
        tail=leaf
        for _ in range(depth-1):tail=add((tail,))
        routers=[add((tail,)) for _ in range(width)]
        left,right=routers,routers
    else:
        branches=[]
        for _ in range(2):
            routers=[]
            for _ in range(width):
                leaf=add();means[leaf]=.15
                tail=leaf
                for _ in range(depth):tail=add((tail,))
                routers.append(tail)
            branches.append(routers)
        left,right=branches
    a,b=add(),add();means[a]=.85;means[b]=.85-gap
    rows[0]=[1,2];rows[1]=left+[a];rows[2]=right+[b]
    label="merge" if shared else "unfold"
    return Problem(f"{label}_{width}_depth{depth}_gap{gap:g}",DAG(rows),means)


def problem_spec(spec):
    if spec.startswith(("merge","unfold")):
        parts=spec.split("_");shared=parts[0].startswith("merge")
        width=int(parts[0][5:] if shared else parts[0][6:])
        depth=int(parts[1]) if len(parts)>1 else 8
        return reconvergent(width,depth,shared)
    return old_spec(spec)
