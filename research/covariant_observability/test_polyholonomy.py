"""Matched nonabelian SU(2) two-cycle controls, with analytic oracles.

Run: python research/covariant_observability/test_polyholonomy.py

This instrument deliberately uses a direct degree-minus-transport-adjacency
construction, independent of the repository's incidence implementation.
"""
from __future__ import annotations

import json

import numpy as np

IDENTITY = np.eye(2, dtype=complex)
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SZ = np.diag([1, -1]).astype(complex)
THETA = [(0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4)]
WEDGE = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]
A_ANGLE, B_ANGLE = 0.8, 1.0


def matrices(angle: float) -> tuple[np.ndarray, np.ndarray]:
    a = np.cos(A_ANGLE) * IDENTITY + 1j * np.sin(A_ANGLE) * SZ
    b = np.cos(B_ANGLE) * IDENTITY + 1j * np.sin(B_ANGLE) * (
        np.cos(angle) * SZ + np.sin(angle) * SX
    )
    return a, b


def base_edges(topology: str, a: np.ndarray, b: np.ndarray) -> list[tuple[int, int, np.ndarray]]:
    assert topology in ("theta", "wedge")
    edges = THETA if topology == "theta" else WEDGE
    special = {(1, 3): a, (1, 4): b} if topology == "theta" else {(1, 2): a, (3, 4): b}
    return [(u, v, special.get((u, v), IDENTITY)) for u, v in edges]


def subdivide(base: list[tuple[int, int, np.ndarray]], subdivision: int):
    """Replace every edge by a chain of equal length with the same net transport."""
    assert subdivision >= 1
    if subdivision == 1:
        return 5, list(base)
    vertices = 5
    edges = []
    for u, v, transport in base:
        chain = [u] + list(range(vertices, vertices + subdivision - 1)) + [v]
        vertices += subdivision - 1
        for k, (src, dest) in enumerate(zip(chain, chain[1:])):
            along_path = transport if k == 0 else IDENTITY
            edges.append((src, dest, along_path) if src < dest else
                         (dest, src, along_path.conj().T))
    return vertices, edges


def block_laplacian(n: int, edges: list[tuple[int, int, np.ndarray]]) -> np.ndarray:
    """Direct block degree-minus-adjacency, NOT incidence^* incidence."""
    out = np.zeros((2 * n, 2 * n), dtype=complex)
    assert len({(u, v) for u, v, _ in edges}) == len(edges)
    for u, v, transport in edges:
        assert 0 <= u < v < n
        assert np.max(np.abs(transport.conj().T @ transport - IDENTITY)) < 1e-12
        ui = slice(2 * u, 2 * u + 2)
        vi = slice(2 * v, 2 * v + 2)
        out[ui, ui] += IDENTITY
        out[vi, vi] += IDENTITY
        out[ui, vi] -= transport
        out[vi, ui] -= transport.conj().T
    assert np.max(np.abs(out - out.conj().T)) < 1e-13
    return out


def block_diagonal(blocks: list[np.ndarray]) -> np.ndarray:
    out = np.zeros((2 * len(blocks), 2 * len(blocks)), dtype=complex)
    for i, block in enumerate(blocks):
        out[2 * i:2 * i + 2, 2 * i:2 * i + 2] = block
    return out


def random_u2(rng: np.random.Generator) -> np.ndarray:
    z = rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))
    q, r = np.linalg.qr(z)
    d = np.diag(r)
    return q * (d / np.abs(d))[None, :]


def conjugated_gauge(edges, gauges):
    return [(u, v, gauges[u] @ transport @ gauges[v].conj().T)
            for u, v, transport in edges]


def relabel(n, edges, permutation):
    out = []
    for u, v, transport in edges:
        pu, pv = int(permutation[u]), int(permutation[v])
        out.append((pu, pv, transport) if pu < pv else (pv, pu, transport.conj().T))
    return out


def test():
    rng = np.random.default_rng(20261028)
    angles = [0., np.pi / 6, np.pi / 3, np.pi / 2]
    data = []
    negative_controls = []
    max_gauge_error = max_relabel_error = 0.0
    for subdivision in [1, 2, 3]:
        for topology in ["theta", "wedge"]:
            baseline = None
            for angle in angles:
                a, b = matrices(angle)
                n, edges = subdivide(base_edges(topology, a, b), subdivision)
                L = block_laplacian(n, edges)

                # Independent incidence factorization cross-check.
                D = np.zeros((2 * len(edges), 2 * n), dtype=complex)
                for k, (u, v, U) in enumerate(edges):
                    D[2 * k:2 * k + 2, 2 * u:2 * u + 2] = IDENTITY
                    D[2 * k:2 * k + 2, 2 * v:2 * v + 2] = -U
                assert np.max(np.abs(D.conj().T @ D - L)) < 1e-12

                eig = np.linalg.eigvalsh(L)
                assert eig[0] > 1e-12
                comm = float(np.linalg.norm(a @ b - b @ a, ord="fro"))
                tr_mixed = float(np.trace(a @ b.conj().T).real)
                c = IDENTITY + a + b
                c_expected = 3 + float(np.trace(a).real) + float(np.trace(b).real) + tr_mixed
                assert np.max(np.abs(c.conj().T @ c - c_expected * IDENTITY)) < 1e-12

                if baseline is None:
                    baseline = (eig, L, tr_mixed)
                spectral_effect = float(np.max(np.abs(eig - baseline[0])))
                assert abs(float(np.trace(a).real) - 2 * np.cos(A_ANGLE)) < 1e-12
                assert abs(float(np.trace(b).real) - 2 * np.cos(B_ANGLE)) < 1e-12
                if angle == 0:
                    assert comm < 1e-12
                else:
                    assert comm > 0.5

                if topology == "wedge":
                    # Negative control: noncommuting holonomies are spectrally invisible.
                    assert spectral_effect < 1e-10, (subdivision, angle, spectral_effect)
                    negative_controls.append(spectral_effect)
                elif angle == np.pi / 2:
                    assert spectral_effect > 0.01, (subdivision, spectral_effect)

                if topology == "theta" and subdivision == 1:
                    moment_diff = float(np.trace(np.linalg.matrix_power(L, 4)).real
                                        - np.trace(np.linalg.matrix_power(baseline[1], 4)).real)
                    # The mixed 4-cycle contributes eight oriented based walks.
                    predicted = 8 * (tr_mixed - baseline[2])
                    assert abs(moment_diff - predicted) < 1e-8, (moment_diff, predicted)
                    for k in [1, 2, 3]:
                        actual_k = float(np.trace(np.linalg.matrix_power(L, k)).real)
                        base_k = float(np.trace(np.linalg.matrix_power(baseline[1], k)).real)
                        assert abs(actual_k - base_k) < 1e-8, (k, actual_k, base_k)

                # Metamorphic controls: random U(2) gauges and relabelings.
                for _ in range(2):
                    gs = [random_u2(rng) for _ in range(n)]
                    G = block_diagonal(gs)
                    lg = block_laplacian(n, conjugated_gauge(edges, gs))
                    ge = float(np.max(np.abs(lg - G @ L @ G.conj().T)))
                    assert ge < 1e-10
                    max_gauge_error = max(max_gauge_error, ge)
                    perm = rng.permutation(n)
                    p = np.zeros_like(L)
                    for u in range(n):
                        p[2 * perm[u]:2 * perm[u] + 2, 2 * u:2 * u + 2] = IDENTITY
                    lr = block_laplacian(n, relabel(n, edges, perm))
                    re = float(np.max(np.abs(lr - p @ L @ p.conj().T)))
                    assert re < 1e-10
                    max_relabel_error = max(max_relabel_error, re)

                data.append({"topology": topology, "subdivision": subdivision,
                             "vertices": n, "edges": len(edges), "axis_angle": float(angle),
                             "commutator_frobenius": comm, "trace_A": float(np.trace(a).real),
                             "trace_B": float(np.trace(b).real),
                             "mixed_wilson_trace": tr_mixed,
                             "spectral_gap": float(eig[0]),
                             "rescaled_gap_s_squared": float(eig[0] * subdivision * subdivision),
                             "max_spectral_shift_vs_commuting": spectral_effect})
    assert len(data) == 24
    assert max(negative_controls) < 1e-10
    return {"status": "pass", "cases": len(data),
            "theta_vs_wedge_confound": "same vertex/edge counts, cycle rank, fiber rank; DIFFERENT degree sequences; cross-graph topology-only causality NOT supported",
            "max_wedge_spectral_shift": max(negative_controls),
            "max_gauge_block_error": max_gauge_error,
            "max_relabel_block_error": max_relabel_error,
            "observables": data,
            "claims": {"P": "exact finite moment and Schur-complement arguments in POLYHOLONOMY.md",
                       "M": "these bounded finite-matrix comparisons, not a Lean proof",
                       "H": "uniform graph-family or hyperbolic limit behavior is not established"}}


if __name__ == "__main__":
    print(json.dumps(test(), indent=2))
