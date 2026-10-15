"""Numerical, not formal, validation of the Fourier-multiset assembly design.

Verifies scalar and one-wrap signed cycle eigenvector matrices and spectra,
including multiplicities, for n=3..64. Designed to falsify common mistakes:
using cosine-only vectors (not a full basis), forgetting the anti-periodic
boundary condition, or comparing eigenvalue sets instead of multisets.

Run from the repository root:
  python findings/round10/test_cycle_fourier_multisets.py
"""
import numpy as np


def cycle_laplacians(n):
    assert n >= 3
    scalar = 2.0 * np.eye(n)
    signed = 2.0 * np.eye(n)
    for i in range(n):
        j = (i + 1) % n
        scalar[i, j] = scalar[j, i] = -1.0
        signed[i, j] = signed[j, i] = (
            1.0 if {i, j} == {0, n - 1} else -1.0
        )
    return scalar, signed


def candidate_basis(n, twisted):
    j, k = np.meshgrid(np.arange(n), np.arange(n), indexing="ij")
    phi = (2 * k + (1 if twisted else 0)) * np.pi / n
    return np.exp(1j * j * phi), 2.0 - 2.0 * np.cos(phi[0])


def check_all(start=3, stop=64, tol=1e-9):
    max_residual = 0.0
    max_unitarity = 0.0
    max_multiset_diff = 0.0
    bad_twist_rejected = 0

    for n in range(start, stop + 1):
        scalar, signed = cycle_laplacians(n)
        for laplacian, twisted in ((scalar, False), (signed, True)):
            basis, values = candidate_basis(n, twisted)
            residual = np.linalg.norm(
                laplacian @ basis - basis * values[None, :],
                ord="fro",
            ) / n
            unit = np.linalg.norm(
                (basis.conj().T @ basis) / n - np.eye(n), ord="fro"
            ) / n
            actual = np.sort(np.linalg.eigvalsh(laplacian))
            diff = np.max(np.abs(actual - np.sort(values)))

            max_residual = max(max_residual, residual)
            max_unitarity = max(max_unitarity, unit)
            max_multiset_diff = max(max_multiset_diff, diff)
            assert residual < tol, (
                n, twisted, "eigenvector identity", residual
            )
            assert unit < tol, (n, twisted, "unitarity", unit)
            assert diff < tol, (n, twisted, "multiset spectrum", diff)

        # Negative control: periodic Fourier vectors are NOT eigenvectors
        # of the one-wrap signed cycle. Z/2 holonomy changes the basis.
        periodic, vals = candidate_basis(n, False)
        wrong_residual = np.linalg.norm(
            signed @ periodic - periodic * vals[None, :], ord="fro"
        ) / n
        assert wrong_residual > 1e-3, (
            n, "bad-twist control unexpectedly accepted", wrong_residual
        )
        bad_twist_rejected += 1

    return {
        "n": f"{start}..{stop}",
        "cases": (stop - start + 1) * 2,
        "max_eigen_equation_residual": max_residual,
        "max_unitarity_residual": max_unitarity,
        "max_sorted_multiset_discrepancy": max_multiset_diff,
        "negative_controls_rejected": bad_twist_rejected,
        "status": "PASS (numerical, not a Lean theorem)",
    }


if __name__ == "__main__":
    import json

    print(json.dumps(check_all(), indent=2))
