"""Exact characteristic-polynomial oracle for ALL uniformly subdivided SU(2)
theta graphs, and a separately testable metric-graph low spectrum.

No claim of Lean proof. See METRIC_GRAPH_LIMIT.md for the derivation.
"""
from __future__ import annotations

import json
import math
import numpy as np

from test_polyholonomy import matrices, base_edges, subdivide, block_laplacian


def chebyshev_second(m: int, epsilon: float) -> float:
    """U_m(1-epsilon/2); U_{-1}=0, U_0=1."""
    if m == -1:
        return 0.0
    a, b = 0.0, 1.0
    for _ in range(m):
        a, b = b, (2.0 - epsilon) * b - a
    return float(b)


def theta_charpoly(s: int, epsilon: float, a: np.ndarray, b: np.ndarray) -> float:
    """Exact det(L_s-epsilon I), represented over complex rank-two fibers."""
    assert s >= 1
    m = 2 * s
    p = chebyshev_second(m - 1, epsilon)
    prev = chebyshev_second(m - 2, epsilon)
    h = (3.0 - epsilon) * p - 3.0 * prev
    chi = 3.0 + float(np.trace(a).real) + float(np.trace(b).real) + (
        float(np.trace(a @ b.conj().T).real)
    )
    return float(p * p * (h * h - chi) ** 2)


def continuum_roots(a: np.ndarray, b: np.ndarray, repetitions: int = 6) -> list[float]:
    """First metric-graph eigenvalues from the limiting secular equation."""
    chi = 3.0 + float(np.trace(a).real) + float(np.trace(b).real) + (
        float(np.trace(a @ b.conj().T).real)
    )
    assert 0 < chi < 9, chi
    alpha = math.acos(math.sqrt(chi) / 3.0)
    q = [alpha / 2]
    for m in range(1, repetitions + 2):
        q += [(m * math.pi - alpha) / 2,
              m * math.pi / 2, (m * math.pi + alpha) / 2]
    eigenvalues = sorted(v * v for v in q)
    # Each root has complex multiplicity two.
    return [ev for ev in eigenvalues for _ in range(2)]


def test():
    cases = []
    max_logdet_error = 0.0
    for s in [1, 2, 3, 4, 6]:
        for angle in [0., 0.3, 0.9, math.pi / 2]:
            a, b = matrices(angle)
            n, edges = subdivide(base_edges("theta", a, b), s)
            L = block_laplacian(n, edges)
            for eps in [-0.7, -0.15, 0.12, 0.65, 1.55, 3.1]:
                analytic = theta_charpoly(s, eps, a, b)
                sign, logdet = np.linalg.slogdet(L - eps * np.eye(2 * n))
                assert sign.real > 0.999999, (s, angle, eps, sign)
                assert analytic > 0, (s, angle, eps, analytic)
                error = abs(float(logdet) - math.log(analytic))
                assert error < 1e-7, (s, angle, eps, error)
                max_logdet_error = max(error, max_logdet_error)
            cases.append({"subdivision": s, "angle": float(angle), "vertices": n})
    # Freeze the continuum oracle from the analytic secular equation and compare
    # against dense H_s=s^2 L_s spectra. This is an asymptotic *test*, not proof.
    convergence = []
    for s in [4, 8, 16, 24]:
        a, b = matrices(math.pi / 2)
        n, edges = subdivide(base_edges("theta", a, b), s)
        observed = s * s * np.linalg.eigvalsh(block_laplacian(n, edges))
        expected = np.array(continuum_roots(a, b)[:10])
        err = float(np.max(np.abs(observed[:10] - expected)))
        convergence.append({"subdivision": s, "vertices": n, "first_10_max_abs_error": err,
                            "first_10_scaled_eigenvalues": observed[:10].tolist(),
                            "candidate_continuum_eigenvalues": expected.tolist()})
    # Open-ended report of convergence; intentionally no posthoc threshold used.
    return {"status": "pass", "characteristic_polynomial_cases": len(cases),
            "determinant_evaluations": len(cases) * 6,
            "max_logdet_error": max_logdet_error,
            "continuum_spectral_comparison": convergence,
            "claim": "finite exact polynomial proven on paper; metric-graph spectrum is a candidate supported by secular-limit algebra",
            "scope": "theta graph, complex fundamental SU(2), edge lengths 1, Kirchhoff coupling"}


if __name__ == "__main__":
    print(json.dumps(test(), indent=2))
