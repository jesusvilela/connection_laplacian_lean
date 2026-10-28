"""Independent exact-kernel check for flat-cycle Riesz endpoint obstruction."""
from __future__ import annotations

import json

import numpy as np

from experiment import cycle, norm_inf, observables


def flat_cycle_kernel(n: int) -> np.ndarray:
    """Analytic kernel for D f(j) = f(j) - f(j+1 mod n)."""
    i, j = np.indices((n, n))
    argument = np.pi * (2 * ((i - j) % n) + 1) / (2 * n)
    return 1 / (n * np.tan(argument))


def run() -> dict:
    cases = []
    for n in [5, 8, 16, 32, 64, 128]:
        R = observables(cycle(n, 0).incidence())["R"].copy()
        # Incidence convention stores the closing edge (0,n-1) rather than (n-1,0).
        # Its row is the negative of the cyclic orientation used by the formula.
        R[-1, :] *= -1
        K = flat_cycle_kernel(n)
        error = norm_inf(R - K)
        assert error < 1e-9, (n, error)
        actual = float(np.max(np.sum(np.abs(R), axis=1)))
        predicted = float(np.sum(np.abs(K[0, :])))
        assert abs(actual - predicted) < 1e-9
        cases.append({"n": n, "kernel_max_entry_error": error,
                      "operator_linf": actual, "operator_linf_formula": predicted,
                      "minus_leading_log": actual - 2 / np.pi * np.log(n)})
    assert all(b["operator_linf"] > a["operator_linf"]
               for a, b in zip(cases, cases[1:]))
    # The log-asymptotic is proved in ENDPOINT.md; this is an independent finite test.
    return {"claim": "flat-cycle discrete Riesz kernel (numeric checks, analytic proof in ENDPOINT.md)",
            "cases": cases}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
