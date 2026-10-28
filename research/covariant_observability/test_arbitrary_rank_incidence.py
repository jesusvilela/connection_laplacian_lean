"""Arbitrary-rank U(r) directed half-edge incidence, independent block oracle.

For each undirected edge we include both orientations with 1/sqrt(2) rows.
The direct degree-minus-transport block Laplacian is built separately.
Controls: isolates, disconnected graphs, noncommuting transports,
vertex-gauge covariance, orientation cancellation and injected failures.
"""
from __future__ import annotations

import itertools
import json
import numpy as np


def unitary(rng, r):
    z = rng.standard_normal((r, r)) + 1j * rng.standard_normal((r, r))
    q, rr = np.linalg.qr(z)
    d = np.diag(rr)
    return q * (d / np.abs(d))[None, :]


def direct_laplacian(n, r, edges):
    L = np.zeros((n*r, n*r), dtype=complex)
    I = np.eye(r)
    for u, v, U in edges:
        assert 0 <= u < v < n
        assert np.max(np.abs(U.conj().T @ U - I)) < 1e-11
        us, vs = slice(u*r, (u+1)*r), slice(v*r, (v+1)*r)
        L[us, us] += I
        L[vs, vs] += I
        L[us, vs] -= U
        L[vs, us] -= U.conj().T
    return L


def half_edge_incidence(n, r, edges):
    B = np.zeros((2*len(edges)*r, n*r), dtype=complex)
    source = []
    I = np.eye(r)
    for k, (u, v, U) in enumerate(edges):
        for direction, (src, dst, T) in enumerate(
            ((u, v, U), (v, u, U.conj().T))
        ):
            row = slice((2*k+direction)*r, (2*k+direction+1)*r)
            B[row, src*r:(src+1)*r] += I / np.sqrt(2)
            B[row, dst*r:(dst+1)*r] -= T / np.sqrt(2)
            source.append(src)
    return B, source


def diagonal_blocks(blocks):
    r = blocks[0].shape[0]
    out = np.zeros((len(blocks)*r, len(blocks)*r), dtype=complex)
    for k, b in enumerate(blocks):
        out[k*r:(k+1)*r, k*r:(k+1)*r] = b
    return out


def patterns(n, rng):
    pairs = list(itertools.combinations(range(n), 2))
    yield []
    yield [(i, i+1) for i in range(n-1)]  # tree; all sections trivializable
    yield [(i, (i+1) % n) if i < n-1 else (0, n-1)
           for i in range(n)]
    yield [e for e in pairs if rng.uniform() < 0.35]
    yield [e for e in pairs if rng.uniform() < 0.65]


def run():
    rng = np.random.default_rng(20261028)
    cases, gauge_cases, max_error, max_gauge_error, max_intertwine = 0, 0, 0., 0., 0.
    min_eigenvalue = 0.
    for r in [2, 3, 4]:
        for n in [3, 5, 8]:
            for pattern in patterns(n, rng):
                E = sorted(set(tuple(sorted(e)) for e in pattern))
                transports = [(u, v, unitary(rng, r)) for u, v in E]
                B, sources = half_edge_incidence(n, r, transports)
                L = direct_laplacian(n, r, transports)
                err = float(np.max(np.abs(B.conj().T @ B - L)))
                assert err < 1e-11, (n, r, E, err)
                eig_min = float(np.linalg.eigvalsh(L)[0])
                assert eig_min > -1e-10
                min_eigenvalue = min(min_eigenvalue, eig_min)
                max_error = max(max_error, err)
                gauges = [unitary(rng, r) for _ in range(n)]
                G = diagonal_blocks(gauges)
                E2 = [(u, v, gauges[u] @ U @ gauges[v].conj().T)
                      for u, v, U in transports]
                Bg, _ = half_edge_incidence(n, r, E2)
                Lg = direct_laplacian(n, r, E2)
                H = diagonal_blocks([gauges[src] for src in sources]) if sources else np.zeros((0, 0))
                gerr = float(np.max(np.abs(Lg - G @ L @ G.conj().T)))
                ierr = float(np.max(np.abs(Bg @ G - H @ B))) if sources else 0.0
                assert gerr < 1e-11 and ierr < 1e-11
                max_gauge_error = max(max_gauge_error, gerr)
                max_intertwine = max(max_intertwine, ierr)
                cases += 1
                gauge_cases += 1

    r, n = 3, 4
    E = [(0, 1), (0, 2), (1, 2), (2, 3)]
    edges = [(u, v, unitary(rng, r)) for u, v in E]
    D, _ = half_edge_incidence(n, r, edges)
    L = direct_laplacian(n, r, edges)
    # Kill the theorem if a half of the oriented rows is silently missing.
    missing_reverse = D.reshape(len(E), 2*r, n*r)[:, :r, :].reshape(len(E)*r, n*r)
    missing_error = float(np.max(np.abs(missing_reverse.conj().T @ missing_reverse - L)))
    assert missing_error > 0.25
    # Kill it if a reverse edge reuses U instead of U^*.
    broken = D.copy()
    u, v, U = edges[0]
    row = slice(r, 2*r)
    broken[row, u*r:(u+1)*r] = -U / np.sqrt(2)
    bad_error = float(np.max(np.abs(broken.conj().T @ broken - L)))
    assert bad_error > 0.1
    comm = float(np.linalg.norm(edges[0][2] @ edges[1][2] -
                                edges[1][2] @ edges[0][2], ord="fro"))
    assert comm > 0.05
    return {
        "status": "pass", "rank_choices": [2, 3, 4],
        "cases": cases, "gauge_checks": gauge_cases,
        "max_gram_error": max_error,
        "max_block_gauge_error": max_gauge_error,
        "max_incidence_intertwining_error": max_intertwine,
        "minimum_laplacian_eigenvalue": min_eigenvalue,
        "noncommuting_transport_commutator": comm,
        "missing_reverse_orientation_kill": missing_error,
        "incorrect_reverse_transport_kill": bad_error,
        "scope": "finite graph, arbitrary complex U(r) fiber, oriented double rows; not Lean proof or hypercomplex hardness bound",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
