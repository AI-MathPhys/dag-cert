"""Audited SameGame engine and reachable-endgame DAG generator over the 20 standard boards."""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from functools import lru_cache
import hashlib
from pathlib import Path
import random

from joint_root_cert._core.graph import DAG

HASH = "d20270c2d3ddff9add5d77fa85593574f85de7fbf8b0db0729e6d8c85b2a4d35"
STANDARD_PATH = Path(__file__).resolve().parents[1] / "benchmarks" / "data" / "samegame" / "StandardTestset.txt"


def standard():
    if hashlib.sha256(STANDARD_PATH.read_bytes()).hexdigest() != HASH:
        raise ValueError("wrong benchmark revision")
    rows = [list(map(int, l.split())) for l in STANDARD_PATH.read_text().splitlines() if l.strip()]
    if len(rows) != 300 or any(len(r) != 15 for r in rows):
        raise ValueError("board format")
    return [tuple(tuple(col) for col in zip(*rows[i : i + 15][::-1])) for i in range(0, 300, 15)]


def tiles(board):
    return sum(map(len, board))


def finish(board):
    if not board:
        return 1000
    counts = Counter(c for col in board for c in col)
    return -sum(max(n - 2, 0) ** 2 for n in counts.values())


class Moves:
    def __init__(self):
        self.cache = {}
        self.cost = 0
        self.entries = 0

    def __call__(self, board):
        self.cost += 1
        if board in self.cache:
            return self.cache[board]
        seen = set()
        actions = []
        cells = tiles(board)
        self.cost += 12 * cells + len(board) + 4
        for x, col in enumerate(board):
            for y, color in enumerate(col):
                if (x, y) in seen:
                    continue
                group = {(x, y)}
                seen.add((x, y))
                todo = [(x, y)]
                while todo:
                    i, j = todo.pop()
                    for a, b in ((i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1)):
                        if 0 <= a < len(board) and 0 <= b < len(board[a]) and (a, b) not in seen and board[a][b] == color:
                            seen.add((a, b))
                            group.add((a, b))
                            todo.append((a, b))
                if len(group) < 2:
                    continue
                child = tuple(
                    tuple(c for j, c in enumerate(column) if (i, j) not in group)
                    for i, column in enumerate(board)
                )
                child = tuple(column for column in child if column)
                actions.append((child, (len(group) - 2) ** 2))
                self.cost += 4 * cells + 3 * len(board)
        self.cache[board] = tuple(actions)
        self.entries += 1 + sum(2 + len(b) + tiles(b) for b, _ in actions)
        return self.cache[board]


def game_cases():
    cases = []
    for k, initial in enumerate(standard(), 1):
        rng = random.Random(226000 + k)
        moves = Moves()
        board = initial
        path = []
        choices = []
        while actions := moves(board):
            if len(actions) >= 2:
                choices.append((board, list(path)))
            index = rng.randrange(len(actions))
            path.append(index)
            board = actions[index][0]
        eligible = [item for item in choices if len(moves(item[0])) >= 4]
        if not eligible:
            raise ValueError("standard board has no four-way decision")
        board, path = next((item for item in eligible if tiles(item[0]) <= 54), eligible[-1])
        cases.append(dict(family="standard_end", seed=226000 + k, board=board, path=path, source=k, h=3, eps=0.02))
    for seed in range(227101, 227113):
        rng = random.Random(seed)
        while True:
            board = tuple(tuple(rng.randrange(3) for _ in range(5)) for _ in range(5))
            if len(Moves()(board)) >= 2:
                break
        cases.append(dict(family="small", seed=seed, board=board, h=3, eps=0.05))
    return cases


class Game:
    def __init__(self, board, h):
        self.start = board
        self.h = h
        counts = Counter(c for col in board for c in col).values()
        self.B = sum(max(k - 2, 0) ** 2 for k in counts)
        self.scale = max(1, (0 if 1 in counts else 1000) + 2 * self.B)
        self.moves = Moves()
        self.states = [(board, 0, h)]
        rank = {self.states[0]: 0}
        rows = []
        for b, points, left in self.states:
            actions = self.moves(b) if left else ()
            children = []
            for nxt, gain in actions:
                state = nxt, points + gain, left - 1
                if state not in rank:
                    rank[state] = len(rank)
                    self.states.append(state)
                children.append(rank[state])
            rows.append(tuple(dict.fromkeys(children)))
        root_moves = self.moves(board)
        aliases = []
        for nxt, gain in root_moves:
            child = rank[nxt, gain, h - 1]
            aliases.append(len(rows))
            rows.append((child,))
        rows[0] = tuple(aliases)
        self.graph = DAG(rows)
        self.build = self.moves.cost + 5 * sum(map(len, rows)) + 5 * len(rows) + self.moves.entries

    def oracle(self, seed):
        return GameOracle(self, seed)


class GameOracle:
    def __init__(self, p, seed):
        self.p = p
        self.moves = Moves()
        self.calls = 0
        self.extra = 0
        self.tapes = {j: random.Random(1000003 * (seed + 1) + 9176 * j) for j in p.graph.leaves}

    @property
    def operations(self):
        return self.moves.cost + self.extra + self.moves.entries

    def sample(self, j):
        self.calls += 1
        b, score, _ = self.p.states[j]
        rng = self.tapes[j]
        while actions := self.moves(b):
            b, points = actions[rng.randrange(len(actions))]
            score += points
            self.extra += 4
        self.extra += 6 + tiles(b)
        return (score + finish(b) + self.p.B) / self.p.scale


def exact(board, h):
    moves = Moves()

    @lru_cache(None)
    def value(b, left):
        actions = moves(b)
        if not actions:
            return Fraction(finish(b))
        vals = [g + value(nxt, max(0, left - 1)) for nxt, g in actions]
        return max(vals) if left else sum(vals, Fraction()) / len(vals)

    vals = [g + value(nxt, h - 1) for nxt, g in moves(board)]
    return max(vals), vals
