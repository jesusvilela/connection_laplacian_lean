"""Schur-complement characteristic-polynomial oracles for two SU(2) cycle geometries.

Analytic formulas derived independently of eigensolvers and graph walk moments.
They are exact for the specific rank-two five-vertex theta and wedge cases.
"""
import json
import numpy as np

from test_polyholonomy import matrices, base_edges, subdivide, block_laplacian


def analytic_det(topology, a, b, spectral_parameter):
    z = spectral_parameter
    q = 2.0 - z
    ta, tb = float(np.trace(a).real), float(np.trace(b).real)
    if topology == "theta":
        mixed = float(np.trace(a @ b.conj().T).real)
        c = 3.0 + ta + tb + mixed
        return q * q * (((3.0 - z) * q - 3.0)**2 - c)**2
    if topology == "wedge":
        return (q * q - 1.0)**2 * ((4.0 - z) * (q * q - 1.0)
                                         - 4.0 * q - ta - tb)**2
    raise ValueError(topology)


def run():
    rows = []
    max_relative_error = 0.0
    for topology in ["theta", "wedge"]:
        for angle in [0., 0.3, 0.7, np.pi / 2]:
            a, b = matrices(angle)
            n, edges = subdivide(base_edges(topology, a, b), 1)
            assert n == 5
            L = block_laplacian(n, edges)
            for z in [-1.4, -0.5, 0.1, 0.8, 1.7, 3.3]:
                observed = np.linalg.det(L - z * np.eye(2*n))
                expected = analytic_det(topology, a, b, z)
                relative_error = float(abs(observed - expected)/max(1., abs(expected)))
                assert relative_error < 1e-9, (topology, angle, z, relative_error)
                max_relative_error = max(max_relative_error, relative_error)
            rows.append({"topology": topology, "axis_angle": float(angle),
                         "determinant_formula_verified": True})
    return {"status": "pass", "cases": len(rows), "evaluations": len(rows)*6,
            "max_relative_error": max_relative_error,
            "type": "numerical check of explicit Schur-complement characteristic polynomials",
            "note": "The polynomial proof is in SPECTRAL_IDENTIFIABILITY.md; no Lean theorem",
            "rows": rows}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
