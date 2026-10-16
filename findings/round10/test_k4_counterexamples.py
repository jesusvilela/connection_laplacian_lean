#!/usr/bin/env python3
"""Exact finite checks for the two distinct K4 counterexamples; not a Lean proof."""
from fractions import Fraction
from itertools import combinations

EDGES = tuple(combinations(range(4), 2))


def signed_matrix(wrap):
    return [[3 if u == v else (1 if tuple(sorted((u, v))) in wrap else -1)
             for v in range(4)] for u in range(4)]


def rank_and_determinant(matrix):
    rows = [[Fraction(x) for x in row] for row in matrix]
    rank, determinant = 0, Fraction(1)
    for col in range(4):
        pivot = next((i for i in range(rank, 4) if rows[i][col]), None)
        if pivot is None:
            continue
        if pivot != rank:
            rows[pivot], rows[rank] = rows[rank], rows[pivot]
            determinant = -determinant
        value = rows[rank][col]
        determinant *= value
        rows[rank] = [x / value for x in rows[rank]]
        for i in range(rank + 1, 4):
            factor = rows[i][col]
            rows[i] = [x - factor * y for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return rank, determinant if rank == 4 else Fraction(0)


def balanced(wrap):
    # K4 is connected: propagate epsilon(v) = sign(uv) * epsilon(u).
    signs = {0: 1}
    todo = [0]
    while todo:
        u = todo.pop()
        for v in range(4):
            if u == v:
                continue
            required = signs[u] * (-1 if tuple(sorted((u, v))) in wrap else 1)
            if v in signs and signs[v] != required:
                return False
            if v not in signs:
                signs[v] = required
                todo.append(v)
    return True


def main():
    cases = (
        ("manuscript matching {12,34}", {(0, 1), (2, 3)}, 48),
        ("Lean comment adjacent {a-b,a-c}", {(0, 1), (0, 2)}, 32),
    )
    for label, wrap, expected_det in cases:
        rank, det = rank_and_determinant(signed_matrix(wrap))
        assert (rank, det) == (4, expected_det), (label, rank, det)
        assert len(wrap) == 2 and not balanced(wrap)
        prediction = 1 - (len(wrap) % 2)
        assert prediction == 1 and 4 - rank == 0
        print(f"{label}: even wrap count 2, predicted nullity 1, actual 0, determinant {det}")
    # Include singular controls and every other signing, using exact rational arithmetic.
    nullities = set()
    for mask in range(1 << len(EDGES)):
        wrap = {edge for i, edge in enumerate(EDGES) if mask & (1 << i)}
        rank, _ = rank_and_determinant(signed_matrix(wrap))
        nullity = 4 - rank
        assert nullity == int(balanced(wrap)), (wrap, nullity)
        nullities.add(nullity)
    assert nullities == {0, 1}
    print("PASS: all 64 K4 signings; balanced/nullity equality and singular controls")


if __name__ == "__main__":
    main()
