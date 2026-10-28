"""Diffusive visibility test: fixed moment depth vs time-scaled heat trace.

Exploratory s <= 12 observed before this code was committed.
HELD-OUT s = 16, 24 have their thresholds declared below before execution.
A persistent finite-size contrast is not a theorem of continuum convergence.
"""
from __future__ import annotations

import json

import numpy as np

from test_polyholonomy import matrices, base_edges, subdivide, block_laplacian, IDENTITY, SZ, B_ANGLE


def eigs(subdivision: int, topology: str, a: np.ndarray, b: np.ndarray):
    n, edges = subdivide(base_edges(topology, a, b), subdivision)
    L = block_laplacian(n, edges)
    return np.linalg.eigvalsh(L)


def heat_trace(eigenvalues: np.ndarray, diffusion_time: float) -> float:
    assert diffusion_time > 0
    return float(np.exp(-diffusion_time * eigenvalues).sum())


def run():
    a, b0 = matrices(0.)
    _, b1 = matrices(np.pi / 2)
    # Separately matched commuting-only perturbation, for mechanism controls.
    bminus = np.cos(B_ANGLE) * IDENTITY - 1j * np.sin(B_ANGLE) * SZ

    # Pre-registered before held-out execution (not before exploratory s<=12):
    # 1. wedge heat trace contrast < 1e-8 for all s;
    # 2. theta rescaled contrast at t=3 is negative, magnitude >= 0.15
    #    for held-out s=16,24;
    # 3. theta fixed-time t=3 contrast falls below 1e-7 at held-out s.
    # Kill nonvanishing finite-range interpretation if a held-out theta test fails.
    records = []
    for s in [1, 2, 3, 4, 6, 8, 12, 16, 24]:
        row = {"subdivision": s, "vertices": 6*s-1,
               "split": "heldout" if s in [16, 24] else "exploratory"}
        for topology in ["theta", "wedge"]:
            ev0 = eigs(s, topology, a, b0)
            ev1 = eigs(s, topology, a, b1)
            contrast_fixed = heat_trace(ev1, 3.0)-heat_trace(ev0, 3.0)
            contrast_scaled = heat_trace(ev1, 3.0*s*s)-heat_trace(ev0, 3.0*s*s)
            row[topology] = {
                "fixed_t3_difference": contrast_fixed,
                "rescaled_t3s2_difference": contrast_scaled,
                "baseline_rescaled_gap": float(s*s*ev0[0]),
                "twisted_rescaled_gap": float(s*s*ev1[0]),
            }
            if topology == "wedge":
                assert abs(contrast_scaled) < 1e-8
                assert abs(contrast_fixed) < 1e-8
            else:
                assert contrast_scaled < -0.15, (s, contrast_scaled)
                if s in [16, 24]:
                    assert abs(contrast_fixed) < 1e-7, (s, contrast_fixed)
        records.append(row)

    # Compact independent commuting-vs-commuting control at s=3. No need to
    # invoke noncommutativity to obtain a theta heat-trace response.
    s = 3
    c0 = eigs(s, "theta", a, b0)
    cm = eigs(s, "theta", a, bminus)
    commuting_difference = heat_trace(cm, 3.0*s*s)-heat_trace(c0, 3.0*s*s)
    assert abs(commuting_difference) > 0.01

    return {"status": "pass",
            "instrument": "full Hermitian eigenvalues and exact scalar matrix exponential trace",
            "exploratory_sizes": [1, 2, 3, 4, 6, 8, 12],
            "heldout_sizes": [16, 24],
            "heldout_primary_gate": "theta rescaled t=3 trace contrast < -0.15 and wedge absolute contrast < 1e-8",
            "theta_commuting_only_heat_difference_s3": commuting_difference,
            "no_claims": ["continuum convergence", "hyperbolic geometry",
                          "uniform Riesz bound", "SAT computational hardness"],
            "records": records}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
