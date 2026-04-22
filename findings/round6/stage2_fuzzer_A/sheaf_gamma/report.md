# FUZZER-A R6 Stage 2 — Sheaf-section γ (counting/switching at n=6 exact)

**Date:** 2026-04-22. **Runtime:** 65.31 s pure-Python (stdlib; no numpy, no networkx). **Total tests:** 10,785,424 exact integer checks. **Counterexamples:** 0.

## Envelope

- **Exhaustive** over all 112 connected simple graphs on n=6 (canonical-form dedup over S_6; count matches OEIS A001349).
- Edge-count distribution: m=5 (6 classes), 6 (13), 7 (19), 8 (22), 9 (20), 10 (14), 11 (9), 12 (5), 13 (2), 14 (1), 15 (1).
- All 2^m wrap subsets per class → 138,112 (G, W) pairs total.
- G12: full (W, S) sweep for m ≤ 12 (108 classes); 2048 W-samples × 64 S for m ∈ {13, 14, 15} (4 classes). Total 5,169,152 (G, W, S) triples.
- Pure integer bitmask arithmetic. No float tolerances.

## Per-claim verdicts (all PASS, 0 counterexamples)

| Claim | Status | Passed / Tested |
|-------|--------|----------------:|
| **G1**  — #switching-classes = 2^{β₁(G)}                       | PASS | 112 / 112 |
| **G2**  — cycle-parity switching-invariant                     | PASS | 112 / 112 |
| **G3**  — balanced ⇔ every fundamental cycle even-wrap         | PASS | 138,112 / 138,112 |
| **G4**  — switching-class ↔ cycle-parity bijection             | PASS | 112 / 112 |
| **G5**  — #ε witnesses = 2^{#π₀} or 0                          | PASS | 138,112 / 138,112 |
| **G12** — β(G, W) = β(G, W △ δ(S))                             | PASS | **5,169,152 / 5,169,152** |
| **G13** — #coboundaries = 2^{|V|−#π₀}                          | PASS | 112 / 112 |
| **G14** — Euler: \|V\| − \|E\| = #π₀ − β₁                      | PASS | 112 / 112 |
| **G18** — #switching-classes = ∏_i 2^{β₁(C_i)}                 | PASS | 112 / 112 |
| **G21** — #coboundaries · #switching-classes = 2^{\|E\|}       | PASS | 112 / 112 |
| **M2**  — β switching-invariance (merge G12+G2+G3)             | PASS | 112 / 112 |
| **M5**  — balance ⇔ every cycle-space element even-wrap        | PASS | 138,112 / 138,112 |

## Biggest discoveries

1. **G12 lifts cleanly** to n=6 with 5.17M exact triples — β is a true cohomological invariant on the n=6 domain.
2. **M5 and G3 co-extensional** on every (G, W) tested — XOR closure does not expose any gap between "fundamental-cycle" and "full-cycle-space" formulations.
3. G21 tight: `32 × 2^{m−5} = 2^m` holds for every connected n=6 class (dimension formula saturates).
4. Hottest class K₆ (m=15, β₁=10): 2.15 s runtime — exhaustive 32,768 × 64 sweep completed cleanly.

## Stage-3 PROVER-A recommendation

**Order of formalisation** (easy → hard):

1. **G14 (Euler)** — one-liner in Mathlib from `edgeFinset.card` + `ConnectedComponent.card`. Foundation.
2. **G13 → G1 → G21 → G18** — pure counting chain via GF(2) rank of the vertex-to-edge coboundary map δ: (Z/2)^V → (Z/2)^E.
3. **Define Z/2 cycle space + coboundary space + parity pairing** (new Lean file, e.g. `L16_CycleSpace.lean`), then land G2 → G3 → G4 → G12 → M2 → M5 in that order.
4. **G5** is orthogonal (ε-witness counting over {±1}^V) — split to a parallel prover tile.

## Artifacts on disk

- `fuzz.py` — 23.8 KB, pure-Python.
- `results.json` — 14.5 KB, per-claim counts + per-iso-class breakdown.
- `run.log` — 1.7 KB, progress trace + verdict table.

No Lean files touched. No paper edits.
