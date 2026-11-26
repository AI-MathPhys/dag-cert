"""Best-root-action benchmarks: trajectories only, no direct leaf queries."""

from .graph import DAG, Problem
from .benchmark import make_problem


def shared_fanout(width=256, gap=.2, deterministic=False):
    if width < 2 or not 0 < gap < .7:
        raise ValueError("Invalid width/gap")
    # Both root actions share all distractors; their private terminal distinguishes them.
    shared = tuple(range(3, 3+width))
    a, b = 3+width, 4+width
    graph = DAG([(1, 2), shared+(a,), shared+(b,)] + [()]*(width+2))
    means = {v:.08+.32*i/(width-1) for i,v in enumerate(shared)}
    means.update({a:.9, b:.9-gap})
    name = f"fanout_{width}_gap{gap:g}" + ("_det" if deterministic else "")
    return Problem(name, graph, means, graph.leaves if deterministic else ())


def flat_arms(width=256, equal=False):
    graph = DAG([tuple(range(1,width+1))]+[()]*width)
    means = {v:(.5 if equal else .1+.3*(v-1)/max(1,width-1)) for v in graph.leaves}
    if not equal:
        means[width] = .85
    return Problem(f"{'equal' if equal else 'flat'}_{width}", graph, means,
                   graph.leaves if equal else ())


def problem_spec(name):
    if name.startswith("fanout"):
        bits = name.split("_")
        return shared_fanout(int(bits[0][6:]), .04 if "hard" in bits else .2, "det" in bits)
    if name.startswith("flat"):
        return flat_arms(int(name[4:]))
    if name.startswith("equal"):
        return flat_arms(int(name[5:]), True)
    return make_problem(name)
