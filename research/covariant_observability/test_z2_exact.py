"""Independent small-graph oracle for the manuscript's two-sheet connection.

Exhaust all simple signed graphs on <= 4 vertices, including disconnected
and edgeless cases. Separately probe held-out n=5,6 graphs, gauge flips,
vertex relabelings, and an intentionally corrupted off-diagonal block.
"""
from __future__ import annotations

import itertools
import json

import numpy as np

from experiment import z2_bundle

IDENTITY = np.eye(2, dtype=complex)
SWAP = np.array([[0., 1.], [1., 0.]], dtype=complex)


def reference_laplacian(n, edges, wrapped):
    """Direct block D-A definition, independent of incidence assembly."""
    L = np.zeros((2 * n, 2 * n), dtype=complex)
    for u, v in edges:
        U = SWAP if (u, v) in wrapped else IDENTITY
        L[2*u:2*u+2, 2*u:2*u+2] += IDENTITY
        L[2*v:2*v+2, 2*v:2*v+2] += IDENTITY
        L[2*u:2*u+2, 2*v:2*v+2] -= U
        L[2*v:2*v+2, 2*u:2*u+2] -= U.conj().T
    return L


def parity_dimension(n, edges, wrapped):
    """BFS Z/2 cocycle consistency: #components + #balanced components."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        w = int((u, v) in wrapped)
        adj[u].append((v, w))
        adj[v].append((u, w))
    colors = [None] * n
    components = balanced = 0
    for root in range(n):
        if colors[root] is not None:
            continue
        components += 1
        okay = True
        colors[root] = 0
        todo = [root]
        for u in todo:
            for v, w in adj[u]:
                implied = colors[u] ^ w
                if colors[v] is None:
                    colors[v] = implied
                    todo.append(v)
                elif colors[v] != implied:
                    okay = False
        balanced += int(okay)
    return components + balanced


def all_signed_graphs(n):
    pairs = list(itertools.combinations(range(n), 2))
    for statuses in itertools.product(range(3), repeat=len(pairs)):
        edges = [e for e, state in zip(pairs, statuses) if state]
        wrapped = {e for e, state in zip(pairs, statuses) if state == 2}
        yield edges, wrapped


def matrices_and_nullity(n, edges, wrapped):
    Lref = reference_laplacian(n, edges, wrapped)
    B = z2_bundle(n, edges, wrapped).incidence()
    assert B.shape == (2 * len(edges), 2 * n), B.shape
    err = float(np.max(np.abs(B.conj().T @ B - Lref)))
    vals = np.linalg.eigvalsh(Lref)
    nullity = int(np.count_nonzero(np.abs(vals) < 1e-8))
    return err, nullity, parity_dimension(n, edges, wrapped)


def run():
    total, max_error = 0, 0.0
    for n in (2, 3, 4):
        for edges, wrapped in all_signed_graphs(n):
            err, nullity, expected = matrices_and_nullity(n, edges, wrapped)
            assert err < 1e-12, (n, edges, wrapped, err)
            assert nullity == expected, (n, edges, wrapped, nullity, expected)
            max_error = max(max_error, err)
            total += 1
    rng = np.random.default_rng(77128)
    heldout = 0
    for n in (5, 6):
        pairs = list(itertools.combinations(range(n), 2))
        for _ in range(100):
            statuses = rng.integers(0, 3, size=len(pairs))
            edges = [e for e, state in zip(pairs, statuses) if state]
            wrapped = {e for e, state in zip(pairs, statuses) if state == 2}
            err, nullity, expected = matrices_and_nullity(n, edges, wrapped)
            assert err < 1e-12 and nullity == expected, (n, edges, wrapped)
            heldout += 1
    representations = 0
    for n in (4, 5, 6):
        pairs = list(itertools.combinations(range(n), 2))
        for _ in range(20):
            statuses = rng.integers(0, 3, size=len(pairs))
            edges = [e for e, state in zip(pairs, statuses) if state]
            wrapped = {e for e, state in zip(pairs, statuses) if state == 2}
            L = reference_laplacian(n, edges, wrapped)
            # Reindex vertices: block conjugacy is the expected invariance.
            perm = rng.permutation(n)
            re_edges = {
                tuple(sorted((int(perm[u]), int(perm[v])))): state
                for (u, v), state in zip(pairs, statuses) if state
            }
            e2 = sorted(re_edges)
            w2 = {e for e, state in re_edges.items() if state == 2}
            L2 = reference_laplacian(n, e2, w2)
            P = np.zeros_like(L)
            for u in range(n):
                P[2*perm[u]:2*perm[u]+2, 2*u:2*u+2] = IDENTITY
            assert np.max(np.abs(L2 - P @ L @ P.conj().T)) < 1e-12

            # Vertex-wise Z/2 gauge: wrap'_uv = wrap_uv XOR g_u XOR g_v.
            flips = rng.integers(0, 2, size=n)
            g_wrap = {
                e for e in edges
                if (int(e in wrapped) ^ int(flips[e[0]]) ^ int(flips[e[1]])) == 1
            }
            gauged = reference_laplacian(n, edges, g_wrap)
            G = np.zeros_like(L)
            for u in range(n):
                G[2*u:2*u+2, 2*u:2*u+2] = SWAP if flips[u] else IDENTITY
            assert np.max(np.abs(gauged - G @ L @ G.conj().T)) < 1e-12
            representations += 1

    # Failure injection ensures that the factorization oracle is not inert.
    edges = [(0, 1), (1, 2), (0, 2)]
    L = reference_laplacian(3, edges, {(0, 2)})
    B = z2_bundle(3, edges, {(0, 2)}).incidence()
    bad = L.copy()
    bad[0:2, 4:6] *= -1
    assert np.max(np.abs(B.conj().T @ B - bad)) > 0.5

    # Historical counterexample: two wrap edges in a connected graph
    # can create a negative triangle and only one parallel section.
    K4 = list(itertools.combinations(range(4), 2))
    assert parity_dimension(4, K4, {(0, 1), (0, 2)}) == 1

    # Reject duplicate (multi-)edges and improperly specified fibers.
    from experiment import Connection
    try:
        Connection(2, [(0, 1), (0, 1)], [IDENTITY, IDENTITY], rank=2).incidence()
        raise AssertionError("duplicate edges incorrectly accepted")
    except ValueError:
        pass
    try:
        Connection(2, [], []).incidence()
        raise AssertionError("unspecified edgeless fiber incorrectly accepted")
    except ValueError:
        pass

    return {
        "status": "pass", "exhaustive_graphs": total,
        "heldout_graphs": heldout, "representation_checks": representations,
        "max_factorization_error": max_error,
        "independent_oracles": [
            "direct 2x2 block Laplacian", "signed-BFS balanced component count"
        ],
        "scope": "finite simple Z/2 graph connections; numerical cross-check only",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
