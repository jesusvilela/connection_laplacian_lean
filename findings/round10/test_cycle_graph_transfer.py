#!/usr/bin/env python3
"""Exact-integer independent falsification of graph-to-cycle matrix transport.

Reconstruct the ConnGraph signed/scalar Laplacians from an explicit finite
simple graph and a wrap EDGE SET, not from any CycleSpectrum Lean matrix.
Check the two exact matrix-identification hypotheses underlying
CycleGraphTransfer.lean for n=3..64, then for relabelled cycle graphs.
This is computational triangulation, NOT a Lean-checked graph equivalence.
"""
from __future__ import annotations

import random


def edges_cycle(n: int) -> set[frozenset[int]]:
    assert n >= 3
    return {frozenset((j, (j + 1) % n)) for j in range(n)}


def lap_from_graph(n: int, edges: set[frozenset[int]],
                   wraps: set[frozenset[int]]) -> list[list[int]]:
    assert wraps <= edges
    degrees = [sum(i in edge for edge in edges) for i in range(n)]
    return [[degrees[i] if i == j else
             (1 if frozenset((i, j)) in wraps else -1)
             if frozenset((i, j)) in edges else 0
             for j in range(n)] for i in range(n)]


def scalar_special(n: int) -> list[list[int]]:
    return [[2 if i == j else
             -1 if (i + 1) % n == j or (j + 1) % n == i else 0
             for j in range(n)] for i in range(n)]


def signed_special(n: int) -> list[list[int]]:
    return [[2 if i == j else
             -1 if i + 1 == j or j + 1 == i else
             1 if (i == n - 1 and j == 0) or (j == n - 1 and i == 0)
             else 0
             for j in range(n)] for i in range(n)]


def reindex(m: list[list[int]], canonical_to_label: list[int]) -> list[list[int]]:
    return [[m[canonical_to_label[i]][canonical_to_label[j]]
             for j in range(len(m))] for i in range(len(m))]


def run() -> dict:
    cases = 0
    wrong_seam_rejected = 0
    permutation_cases = 0
    rng = random.Random(20261016)
    for n in range(3, 65):
        canonical_edges = edges_cycle(n)
        canonical_wrap = {frozenset((n - 1, 0))}
        scalar = lap_from_graph(n, canonical_edges, set())
        signed = lap_from_graph(n, canonical_edges, canonical_wrap)
        assert scalar == scalar_special(n), ("scalar", n)
        assert signed == signed_special(n), ("signed", n)
        cases += 2

        # Negative: the wrap edge must be the antiperiodic closing edge.
        wrong = lap_from_graph(n, canonical_edges, {frozenset((0, 1))})
        assert wrong != signed_special(n), ("wrong seam unexpectedly accepted", n)
        wrong_seam_rejected += 1

        for _ in range(3):
            p = list(range(n))
            rng.shuffle(p)
            relabelled_edges = {frozenset(p[i] for i in edge)
                                for edge in canonical_edges}
            relabelled_wrap = {frozenset((p[n - 1], p[0]))}
            graph_scalar = lap_from_graph(n, relabelled_edges, set())
            graph_signed = lap_from_graph(n, relabelled_edges, relabelled_wrap)
            assert reindex(graph_scalar, p) == scalar_special(n)
            assert reindex(graph_signed, p) == signed_special(n)
            permutation_cases += 2

    return {
        "n": "3..64",
        "canonical_exact_matrix_cases": cases,
        "reindexed_exact_matrix_cases": permutation_cases,
        "incorrect_closing_edge_rejected": wrong_seam_rejected,
        "status": "PASS (exact integer arithmetic; not a Lean theorem)",
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run(), indent=2))
