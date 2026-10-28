"""Signature-(2,2) transport controls: noncommuting pseudo-isometries.

The Q-inner product is indefinite; it must NOT be substituted into
positive-semidefinite Riesz, heat-trace or energy estimates without
a new operator theory. This tests exact algebraic contracts numerically.
"""
from __future__ import annotations

import json
import numpy as np

Q = np.diag([1., 1., -1., -1.])
I = np.eye(4)


def boost(i: int, j: int, rapidity: float) -> np.ndarray:
    """Lorentz-type boost in one positive/one negative signature plane."""
    assert i in (0, 1) and j in (2, 3)
    c, s = np.cosh(rapidity), np.sinh(rapidity)
    b = I.copy()
    b[i, i] = b[j, j] = c
    b[i, j] = b[j, i] = s
    return b


def defect(B):
    return float(np.max(np.abs(B.T @ Q @ B - Q)))


def run():
    A = boost(0, 2, 0.45)
    B = boost(1, 2, 0.70)
    C = A @ B
    assert defect(A) < 1e-12 and defect(B) < 1e-12
    assert defect(C) < 1e-12
    noncommuting = float(np.linalg.norm(A @ B - B @ A, ord="fro"))
    assert noncommuting > 0.1
    euclidean_defect = float(np.linalg.norm(C.T @ C - I, ord="fro"))
    assert euclidean_defect > 0.5

    # The inverse of a Q-isometry is Q^{-1} U^T Q, not U^T.
    q_inverse = Q @ C.T @ Q
    assert np.max(np.abs(q_inverse @ C - I)) < 1e-12
    assert np.max(np.abs(C @ q_inverse - I)) < 1e-12
    assert np.linalg.norm(C.T @ C - I) > 0.5

    # Paired commuting-only null uses two boosts in the same plane.
    commA = boost(0, 2, 0.45)
    commB = boost(0, 2, 0.70)
    commuting = float(np.linalg.norm(commA @ commB - commB @ commA, ord="fro"))
    assert commuting < 1e-12
    assert defect(commA @ commB) < 1e-12

    # Vertex-frame covariance, using inverse rather than transpose.
    rng = np.random.default_rng(20261028)
    gsrc, gdst, U = A, C, B
    assert defect(gsrc) < 1e-12 and defect(gdst) < 1e-12
    U_gauged = gsrc @ U @ np.linalg.inv(gdst)
    assert defect(U_gauged) < 1e-12
    worst_covariance = 0.0
    worst_energy = 0.0
    for _ in range(64):
        x, y = rng.standard_normal(4), rng.standard_normal(4)
        delta = x - U @ y
        lhs = gsrc @ x - U_gauged @ (gdst @ y)
        rhs = gsrc @ delta
        worst_covariance = max(worst_covariance, float(np.max(np.abs(lhs-rhs))))
        worst_energy = max(worst_energy,
                           float(abs(lhs @ Q @ lhs - delta @ Q @ delta)))
    assert worst_covariance < 1e-12 and worst_energy < 1e-12

    positive, negative = np.array([1., 0., 0., 0.]), np.array([0., 0., 1., 0.])
    assert positive @ Q @ positive == 1.
    assert negative @ Q @ negative == -1.

    corrupted = A.copy()
    corrupted[0, 0] += 0.05
    failure_injection = defect(corrupted)
    assert failure_injection > 0.05

    return {
        "status": "pass", "signature": [2, 2],
        "rank": 4, "pair_noncommutator_frobenius": noncommuting,
        "commuting_null_commutator": commuting,
        "composition_form_defect": defect(C),
        "euclidean_orthogonality_defect": euclidean_defect,
        "max_gauge_covariance_error": worst_covariance,
        "max_indefinite_form_error": worst_energy,
        "failure_injection_form_defect": failure_injection,
        "scope": "algebraic pseudo-orthogonal transports; no positive energy, hyperbolic curvature or hardness bound",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
