# PROVER-SIGNED-PSD — Lean port of signed-Laplacian PSD

**Date:** 2026-04-22. **Landing:** `ConnectionLaplacian/L13_PSD.lean` (311 LOC).

## Theorems landed

- `signedLaplacianMobius_posSemidef : G.signedLaplacianMobius.PosSemidef`
- `signedLaplacianMobius_isSymm`
- `signedLaplacianMobius_isHermitian`

## Build / axioms

- `lake build ConnectionLaplacian.L13_PSD` — green, zero `sorry`, zero warnings.
- `#print axioms signedLaplacianMobius_posSemidef` → `[propext, Classical.choice, Quot.sound]`.

## Proof route — direct SOS (Route A)

Mirrors paper.tex:996-1030 line-by-line:

1. `IsSymm` via off-diagonal case-split using `Sym2.eq_swap` (wrap is an unordered-edge property).
2. `IsHermitian` from `IsSymm` via `conjTranspose_eq_transpose_of_trivial` on ℝ.
3. Expand `x ⬝ᵥ (L_sg *ᵥ x)` entrywise: diagonal `Σ deg(i) x_i²` plus off-diagonal `Σ_{i,j adj} s(i,j) x_i x_j`, where `s = +1` on wrap edges, `−1` on non-wrap.
4. Rewrite `deg(i) x_i² = Σ_{j: Adj i j} x_i²` via `degree_eq_sum_if_adj`.
5. Symmetrise via (i ↔ j) swap: form becomes `Σ_{i,j} (x_i² + x_j²)/2 + s x_i x_j`.
6. Since `s² = 1`: `x_i² + x_j² + 2s · x_i · x_j = (x_i + s · x_j)²`, so the quadratic form equals `(1/2) Σ_{i,j adj} (x_i + s(i,j) x_j)² ≥ 0`.

## Mathlib API used

- `Matrix.PosSemidef`, `Matrix.IsHermitian`, `Matrix.IsSymm`, `Matrix.conjTranspose_eq_transpose_of_trivial`
- `SimpleGraph.degree_eq_sum_if_adj`
- `Finset.sum_add_distrib`, `sum_comm`, `sum_ite_eq`, `sum_congr`, `sum_mul`, `mul_sum`
- `sq_nonneg`, `div_nonneg`, `Sym2.eq_swap`, `Subtype.ext`, `SimpleGraph.irrefl`, `star_trivial`.

## Dependencies

L13_PSD imports only `ConnectionLaplacian.KernelDimension` and `Mathlib.LinearAlgebra.Matrix.PosDef`. No L1-L12 file modified.

`ConnectionLaplacian.lean` manifest updated with `import ConnectionLaplacian.L13_PSD`.

## Net

Appendix A row for Lemma 8.3 now references a landed Lean proof (`L13_PSD.lean`) instead of a deferred port.
