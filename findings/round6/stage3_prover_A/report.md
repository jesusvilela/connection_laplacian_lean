# PROVER-A R6 Stage 3 — M6 spec-union landing

**Date:** 2026-04-22. **Outcome:** M6 + M7 landed. **File:** `ConnectionLaplacian/L16_SpectrumUnion.lean` (137 LOC). **Namespace:** `ConnectionLaplacian.ConnGraph`. **Build:** green at 1832/1832 (`lake build`). **Axioms:** clean.

## Theorems landed

| name | line | statement (informal) |
|------|-----:|----------------------|
| `connectionLaplacian_charpoly_decomposes (mobius : Bool)` | 58 | unified: charpoly of L on the cover factors according to `mobius` |
| `mobius_charpoly_eq_scalar_times_signed` | 78 | **M7 headline:** `(G.laplacian true).charpoly = G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly` |
| `flat_charpoly_eq_scalar_sq` | 87 | flat specialisation: `(G.laplacian false).charpoly = G.scalarLaplacian.charpoly ^ 2` |
| `mobius_charpoly_roots_eq_union` | 109 | **M6 headline (multiset form):** `(G.laplacian true).charpoly.roots = G.scalarLaplacian.charpoly.roots + G.signedLaplacianMobius.charpoly.roots` |
| `flat_charpoly_roots_eq_double` | 125 | flat multiset form |

## Proof strategy

Chose the **charpoly-product form (M7) → multiset-roots form (M6)**. This avoids direct eigenvalue-API entanglement with Mathlib's `Matrix.Hermitian.eigenvalues` and routes cleanly through `Polynomial.charpoly`.

Four-step pattern, mirroring `cover_charpoly_eq_scalar_times_mobius` in L10:

1. **Take `charpoly` of both sides** of `laplacian_decomposes` (`KernelDimension.lean:345`), which already supplies an invertible `P` and a `Matrix.reindex` witnessing
   `P · L_möb · P⁻¹ = reindex (Matrix.fromBlocks L_scalar 0 0 L_signed)`.
2. `Matrix.charpoly_reindex` removes the reindex.
3. `Matrix.charpoly_conj_of_isUnit_det` (already proven in L10) collapses `P · L · P⁻¹` to `L`.
4. `Matrix.charpoly_fromBlocks_zero₁₂` factors the block-diagonal charpoly into the product of block charpolys.

The multiset form (M6) is then a single `Polynomial.roots_mul` application, discharging the nonzero side-condition via monicity of the charpoly of a square matrix.

## Axiom verification

All five theorems depend only on `[propext, Classical.choice, Quot.sound]`. Verified via:

```
$ lake env lean check_axioms.lean
'ConnectionLaplacian.ConnGraph.mobius_charpoly_eq_scalar_times_signed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'ConnectionLaplacian.ConnGraph.mobius_charpoly_roots_eq_union' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'ConnectionLaplacian.ConnGraph.connectionLaplacian_charpoly_decomposes' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorry`. No new axioms. No `native_decide`.

## Files touched

- **new:** `ConnectionLaplacian/L16_SpectrumUnion.lean` (137 LOC).
- **wire-up:** `ConnectionLaplacian.lean` gained `import ConnectionLaplacian.L16_SpectrumUnion`.
- **no other modifications** to existing Lean files.

## B2 mixed-trace (fallback target) — status: SKIPPED

Not needed as a fallback since M6 did not block. Estimated ~20 LOC follow-up using `scalarLaplacian_diag` / `signedLaplacianMobius_diag` already available in `L9_Bounds.lean`, with a wrap case-split on off-diagonals. Deferred to a future stage or R7.

## What this unlocks (per fiber_2.md)

Landing M6/M7 collapses the following Stage-1 β-sheaf claims into one-line corollaries (follow-up work, not in this landing):
- B1 trace-power identity `tr(L_möb^k) = tr(L_s^k) + tr(L_sig^k)` — direct from M6.
- B6 `λ_max(L_möb) = max(λ_max(L_s), λ_max(L_sig))` — max over multiset union.
- B12 heat-trace, B13 resolvent-trace — sums of exp/reciprocal over roots.
- B17 Frobenius-norm identity `‖L_möb‖_F² = ‖L_s‖_F² + ‖L_sig‖_F²` — sum of λ² over multiset union.
- B19 smallest-positive eig, B20 `tr L_möb = 4|E|`.

These will be harvested by Stage-7 PROVER-B as short corollaries of `mobius_charpoly_roots_eq_union`.
