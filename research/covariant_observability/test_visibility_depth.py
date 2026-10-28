"""Finite spectral-moment visibility depth of a mixed SU(2) holonomy.

For a theta graph with every edge subdivided s times, no closed reduced
walk can see mixed holonomy before moment 4*s. At that order the trace
contrast is 8*s times the mixed Wilson-loop trace contrast.
"""
from __future__ import annotations

import json
import numpy as np
from test_polyholonomy import matrices, base_edges, subdivide, block_laplacian


def traced_moments(mat: np.ndarray, kmax: int) -> list[float]:
    p = np.eye(mat.shape[0], dtype=complex)
    out = []
    for _ in range(1, kmax + 1):
        p = p @ mat
        out.append(float(np.trace(p).real))
    return out


def run() -> dict:
    records = []
    for subdivision in (1, 2, 3):
        a, b0 = matrices(0.)
        n, edges = subdivide(base_edges("theta", a, b0), subdivision)
        l0 = block_laplacian(n, edges)
        kstar = 4 * subdivision
        moments0 = traced_moments(l0, kstar)
        for angle in (np.pi / 3, np.pi / 2):
            _, b = matrices(float(angle))
            _, new_edges = subdivide(base_edges("theta", a, b), subdivision)
            l1 = block_laplacian(n, new_edges)
            moments1 = traced_moments(l1, kstar)
            diffs = np.array(moments1) - np.array(moments0)
            expected = 8 * subdivision * (np.trace(a @ b.conj().T).real
                                            - np.trace(a @ b0.conj().T).real)
            early_error = float(np.max(np.abs(diffs[:-1])))
            first_error = float(abs(diffs[-1] - expected))
            assert early_error < 1e-5, (subdivision, angle, early_error)
            assert first_error < 1e-5, (subdivision, angle, first_error)
            assert abs(diffs[-1]) > 1., (subdivision, angle)
            # A fixed sixth-order observer detects the base theta graph,
            # but misses the mixed loop after two or more subdivisions.
            fixed6 = float(np.trace(np.linalg.matrix_power(l1, 6)).real -
                           np.trace(np.linalg.matrix_power(l0, 6)).real)
            if subdivision == 1:
                assert abs(fixed6) > 1.0
            else:
                assert abs(fixed6) < 1e-5
            records.append({"s": subdivision, "vertices": n, "theta": float(angle),
                            "first_detectable_moment": kstar,
                            "max_lower_moment_difference": early_error,
                            "first_moment_difference": float(diffs[-1]),
                            "first_moment_predicted": float(expected),
                            "first_moment_prediction_error": first_error,
                            "sixth_moment_difference": fixed6})
    return {"status": "pass", "comparisons": len(records),
            "finite_depth_claim": "theta graph first mixed trace at k=4*s; not a complexity lower bound",
            "records": records}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
