"""Sampled extension at n=6 for the most important γ-claims.

Budget: each claim receives up to a few hundred (G,W) instances at n=6.
We re-check: G3, G5, G11, G12, G14, G15, G16 (cheap + informative).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
import fuzz_gamma as F


def main(out_json):
    checks = [
        ("G3", F.claim_g3_balance_iff_all_cycle_parity_zero),
        ("G5", F.claim_g5_epsilon_multiplicity),
        ("G11", F.claim_g11_coboundary_iff_even_cycle_parity),
        ("G12", F.claim_g12_switching_preserves_beta),
        ("G14", F.claim_g14_euler_characteristic),
        ("G15", F.claim_g15_signed_kernel_dim_per_component),
        ("G16", F.claim_g16_signed_laplacian_rank),
    ]

    original = F.small_instances

    def sampled_small_instances(n_min=3, n_max=5):
        for n, G, W in original(n_min, min(5, n_max)):
            yield n, G, W
        for item in F.sample_n6(wrap_cap=16, iso_cap=24):
            yield item

    F.small_instances = sampled_small_instances

    results = []
    for idx, fn in checks:
        c = fn()
        results.append({"idx": idx + "_n6",
                        "passed": c.passed, "tested": c.tested,
                        "tau": round(c.tau, 6),
                        "counterexample": c.counterexample})

    F.small_instances = original
    Path(out_json).write_text(json.dumps(results, indent=2, default=str))
    for r in results:
        print(f"  {r['idx']}  tau={r['tau']:.4f}  ({r['passed']}/{r['tested']})")


if __name__ == "__main__":
    main(Path(__file__).parent / "results_n6.json")
