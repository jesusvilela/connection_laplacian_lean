#!/usr/bin/env python3
"""Exact finite verification of signed graph Laplacian identities.

Finite tests are independent numerical evidence, not Lean proofs.
No external packages and no floating-point arithmetic are used.

Run: python3 scripts/verify_signed_laplacian_small.py [max_n]
Default: max_n = 4 (all 760 signed graphs on 1..4 labelled vertices).
"""

from fractions import Fraction
from itertools import combinations, product
import sys


def exact_rank(matrix):
    """Gaussian rank over Q, which equals real rank for integer matrices."""
    a = [[Fraction(c) for c in row] for row in matrix]
    n = len(a)
    rank = 0
    for col in range(n):
        pivot = next((row for row in range(rank, n) if a[row][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        for row in range(rank + 1, n):
            if a[row][col]:
                multiple = a[row][col] / a[rank][col]
                for k in range(col, n):
                    a[row][k] -= multiple * a[rank][k]
        rank += 1
    return rank


def signed_matrix(n, edges):
    """L = D-A_sigma. Edges are (u,v,sign) with sign in {-1,+1}."""
    lap = [[0] * n for _ in range(n)]
    for u, v, sign in edges:
        lap[u][u] += 1
        lap[v][v] += 1
        lap[u][v] = -sign
        lap[v][u] = -sign
    return lap


def balanced_component_count(n, edges):
    """Return balanced components, all component gauges, and total components."""
    adjacency = [[] for _ in range(n)]
    for u, v, sign in edges:
        adjacency[u].append((v, sign))
        adjacency[v].append((u, sign))
    gauge = [None] * n
    balanced = 0
    components = 0
    all_balanced = True
    for start in range(n):
        if gauge[start] is not None:
            continue
        components += 1
        gauge[start] = 1
        todo = [start]
        valid = True
        for u in todo:
            for v, sign in adjacency[u]:
                candidate = gauge[u] * sign
                if gauge[v] is None:
                    gauge[v] = candidate
                    todo.append(v)
                elif gauge[v] != candidate:
                    valid = False
        if valid:
            balanced += 1
        else:
            all_balanced = False
    return balanced, gauge, components, all_balanced


def quadratic(matrix, vector):
    return sum(vector[i] * matrix[i][j] * vector[j]
               for i in range(len(vector)) for j in range(len(vector)))


def energy(edges, vector):
    return sum((vector[u] - sign * vector[v]) ** 2 for u, v, sign in edges)


def verify(max_n=4):
    case_count = 0
    energy_checks = 0
    gauge_checks = 0
    for n in range(1, max_n + 1):
        possible = list(combinations(range(n), 2))
        for statuses in product((0, 1, -1), repeat=len(possible)):
            edges = [(u, v, sign) for (u, v), sign in zip(possible, statuses) if sign]
            lap = signed_matrix(n, edges)
            balanced, tau, components, all_balanced = balanced_component_count(n, edges)
            nullity = n - exact_rank(lap)
            assert nullity == balanced, (n, statuses, nullity, balanced)
            if all_balanced:
                ordinary = signed_matrix(n, [(u, v, 1) for u, v, _ in edges])
                for i in range(n):
                    for j in range(n):
                        assert lap[i][j] == tau[i] * ordinary[i][j] * tau[j], (n, statuses)
                gauge_checks += 1
            for vec in product((-1, 0, 1), repeat=n):
                q = quadratic(lap, vec)
                assert q == energy(edges, vec) and q >= 0, (n, statuses, vec, q)
                energy_checks += 1
            case_count += 1
    # For K4, parity of the total number of negative edges is insufficient.
    pairs = list(combinations(range(4), 2))
    balanced_k4 = 0
    even_but_unbalanced_k4 = 0
    for statuses in product((1, -1), repeat=len(pairs)):
        edges = [(u, v, sign) for (u, v), sign in zip(pairs, statuses)]
        count, _, _, _ = balanced_component_count(4, edges)
        balanced_k4 += int(count == 1)
        even_but_unbalanced_k4 += int(sum(sign == -1 for sign in statuses) % 2 == 0 and count != 1)
    assert balanced_k4 == 8, balanced_k4
    assert even_but_unbalanced_k4 == 28, even_but_unbalanced_k4
    print('PASS: {} exact signed graphs, n=1..{}'.format(case_count, max_n))
    print('PASS: {} exact quadratic energy checks'.format(energy_checks))
    print('PASS: {} full-graph gauge conjugation checks'.format(gauge_checks))
    print('PASS: K4 balanced signings = {}; even-negative unbalanced signings = {}'.format(
        balanced_k4, even_but_unbalanced_k4))


if __name__ == '__main__':
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    if not 1 <= max_n <= 5:
        raise SystemExit('max_n must be between 1 and 5; n=5 is substantially slower')
    verify(max_n)
