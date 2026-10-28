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


def continuum_heat_trace(a: np.ndarray, b: np.ndarray, t: float) -> float:
    """Analytic Kirchhoff metric-theta heat trace, chi strictly between 0 and 9."""
    chi = 3.0 + float(np.trace(a).real) + float(np.trace(b).real) + (
        float(np.trace(a @ b.conj().T).real)
    )
    assert 0 < chi < 9
    alpha = math.acos(math.sqrt(chi) / 3.0)
    # m>=20 terms are beyond machine precision for t=3.
    mixed = 2 * sum(math.exp(-t * ((m * math.pi + alpha) / 2) ** 2)
                    for m in range(-20, 21))
    dirichlet = 2 * sum(math.exp(-t * (m * math.pi / 2) ** 2)
                        for m in range(1, 21))
    return float(mixed + dirichlet)


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
    # A uniform spectral-tail bound from interlacing. Delete the four
    # pole-fiber coordinates: six identical Dirichlet path blocks remain.
    # For the i-th ascending eigenvalue, i>=5, the comparison gives
    # lambda_i(H_s) >= ceil((i-4)/6)^2, independently of A and B.
    interlacing_max_violation = 0.0
    for s in [1, 2, 4, 8, 16]:
        a, b = matrices(math.pi / 2)
        n, edges = subdivide(base_edges("theta", a, b), s)
        eig = s * s * np.linalg.eigvalsh(block_laplacian(n, edges))
        lower_bounds = np.array([0.0 if i < 4 else
                                 float(math.ceil((i - 3) / 6) ** 2)
                                 for i in range(len(eig))])
        violation = float(np.max(lower_bounds - eig))
        assert violation < 1e-8, (s, violation)
        interlacing_max_violation = max(violation, interlacing_max_violation)

    # Continuum heat trace is an analytic series computed separately
    # from the matrix eigenvalue method (not a numerical fit).
    a, b0 = matrices(0.)
    _, b1 = matrices(math.pi / 2)
    t = 3.0
    continuum_contrast = (continuum_heat_trace(a, b1, t)
                          - continuum_heat_trace(a, b0, t))
    heat_comparison = []
    for s in [4, 8, 16, 24]:
        n, e0 = subdivide(base_edges("theta", a, b0), s)
        _, e1 = subdivide(base_edges("theta", a, b1), s)
        lam0 = s * s * np.linalg.eigvalsh(block_laplacian(n, e0))
        lam1 = s * s * np.linalg.eigvalsh(block_laplacian(n, e1))
        measured = float(np.exp(-t * lam1).sum()-np.exp(-t * lam0).sum())
        heat_comparison.append({"s": s, "observed": measured,
                                "analytic_limit": continuum_contrast,
                                "absolute_error": abs(measured-continuum_contrast)})
    assert all(b["absolute_error"] < a["absolute_error"]
               for a, b in zip(heat_comparison, heat_comparison[1:]))
    assert heat_comparison[-1]["absolute_error"] < 0.005
    # Open-ended report of convergence; no claim of Lean verification.
    return {"status": "pass", "characteristic_polynomial_cases": len(cases),
            "determinant_evaluations": len(cases) * 6,
            "max_logdet_error": max_logdet_error,
            "continuum_spectral_comparison": convergence,
            "uniform_interlacing_max_violation": interlacing_max_violation,
            "heat_trace_limit_contrast_t3": continuum_contrast,
            "heat_trace_continuum_comparison": heat_comparison,
            "claim": "finite polynomial and metric-graph heat trace convergence derived via compact spectral determinant and uniform interlacing tail bound, not Lean-proved",
            "scope": "theta graph, complex fundamental SU(2), edge lengths 1, Kirchhoff coupling"}


if __name__ == "__main__":
    print(json.dumps(test(), indent=2))
