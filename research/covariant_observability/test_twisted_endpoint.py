"""Exact U(1) twisted-cycle Riesz endpoint-kernel checks.

Three paths: analytic Fourier formula, separate uniformly distributed phase
matrix eigendecomposition, and repository's concentrated-edge convention.
These are cross-checks of a mathematical identity, not a Lean proof.
"""
import json

import numpy as np

from experiment import cycle, observables


def spectral_riesz(D):
    L = D.conj().T @ D
    vals, Q = np.linalg.eigh(L)
    assert min(vals) > 1e-10
    return D @ ((Q * (1.0 / np.sqrt(vals))) @ Q.conj().T)


def closed_form(n, theta):
    i, j = np.indices((n, n))
    q = np.exp(2j * np.pi * (i - j + 0.5) / n)
    return (-2j * np.exp(1j * theta / (2 * n))) / (n * (1 - q))


def run():
    rows = []
    max_entry_error = 0.0
    for n in [5, 8, 16, 32, 64, 128]:
        d = np.arange(n)
        csc_norm = float(np.mean(1 / np.sin(np.pi * (d + 0.5) / n)))
        dd = np.arange(2 * n)
        flat_double = float(np.mean(abs(1 / np.tan(np.pi * (dd + 0.5) / (2 * n)))))
        assert abs(csc_norm - flat_double) < 2e-12
        flat_n = float(np.mean(abs(1 / np.tan(np.pi * (d + 0.5) / n))))
        assert csc_norm > flat_n + 0.2
        for theta in [0.1, 1.2, 3.1, 5.8]:
            shift = np.roll(np.eye(n, dtype=complex), 1, axis=1)
            D = np.eye(n, dtype=complex) - np.exp(1j * theta / n) * shift
            R = spectral_riesz(D)
            K = closed_form(n, theta)
            error = float(np.max(abs(R - K)))
            assert error < 2e-8, (n, theta, error)
            op = float(np.max(abs(R).sum(axis=1)))
            assert abs(op - csc_norm) < 2e-8
            concentrated = observables(cycle(n, theta).incidence())["R"]
            op_conc = float(np.max(abs(concentrated).sum(axis=1)))
            assert abs(op_conc - csc_norm) < 2e-8, (n, theta, op_conc, csc_norm)
            max_entry_error = max(max_entry_error, error)
            rows.append({"n": n, "theta": theta, "endpoint_norm": op,
                         "concentrated_norm": op_conc,
                         "closed_form_norm": csc_norm,
                         "flat_2n_norm": flat_double,
                         "kernel_error": error})
    return {
        "status": "pass", "tests": len(rows), "max_kernel_error": max_entry_error,
        "twist_phase_invariant_up_to_n": 128,
        "evidence": "Numerical validation of TWISTED_ENDPOINT.md; not Lean formalization",
        "records": rows,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
