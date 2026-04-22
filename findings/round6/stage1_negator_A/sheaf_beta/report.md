# NEGATOR-A R6 — Sheaf-section β (spectral / trace / eigenvalue / norm)

**Date:** 2026-04-22. **Envelope:** exhaustive n ∈ {3,4,5} × all wrap subsets (~3,453 base configs) + deterministic n=6 sample. 21 claims orthogonal to R5 β-tile (R9, R11, R12, R17, R18, R19). ~145k configs scored.

## Summary table (ranked by τ)

| # | claim | precondition | τ | supp / total |
|---|-------|--------------|---|--------------|
| **B1** | `tr(L_möb^k) = tr(L_s^k) + tr(L_sig^k)` for k ∈ {5,6,7,8} | — | **1.0000** | 13812/13812 (+1456 n=6) |
| **B2** | `tr(L_s · L_sig) = Σ deg(u)² + 2m − 4|W|` | — | **1.0000** | 3453/3453 (+372 n=6) |
| B3 | `tr((L_s ⊗ I₂) · L_möb) = 2·tr(L_s²)` | — | **0.0142** | 49/3453 |
| **B4** | `tr(L_sig^{k+1}) ≤ tr(L_sig^k) · ‖L_sig‖_op`, k ∈ {1,2,3} | — | **1.0000** | 10359/10359 (+1143 n=6) |
| B5 | `λ_max(L_sig) ≤ λ_max(L_s)` | — | **0.1741** | 601/3453 |
| **B6** | `λ_max(L_möb) = max(λ_max(L_s), λ_max(L_sig))` | — | **1.0000** | 3453/3453 (+396 n=6) |
| **B7** | `spec(L_möb) = spec(L_s) ⊎ spec(L_sig)` (multiset union) | — | **1.0000** | 3453/3453 (+384 n=6) |
| **B8** | `λ₂(L_s) ≥ λ_min(L_sig)` | G connected | **1.0000** | 3244/3244 |
| **B9** | `dim ker L_möb = #comps(G) + β(G,W)` | — | **1.0000** | 3453/3453 (+396 n=6) |
| B10 | `‖L_sig‖_op ≤ ‖L_s‖_op` | — | **0.1741** | 601/3453 |
| **B11** | `supp(v ∈ ker L_sig) = union of balanced comps` | — | **1.0000** | 726/726 |
| **B12** | `tr(exp(−t L_möb)) = tr(exp(−t L_s)) + tr(exp(−t L_sig))` | t ∈ {0.5, 2} | **1.0000** | 6906/6906 (+768 n=6) |
| **B13** | `tr((zI − L_möb)⁻¹) = tr((zI − L_s)⁻¹) + tr((zI − L_sig)⁻¹)` | z = −1 | **1.0000** | 3453/3453 |
| **B14** | `|λᵢ(L_sig(G,W)) − λᵢ(L_sig(G,W−{e}))| ≤ 2` | single wrap flip | **1.0000** | 13543/13543 (+1433 n=6) |
| **B15** | `λᵢ(L_sig(G − E')) ≥ λ_{i−k}(L_sig(G))` and ≤ λ_{i+k} | E' ⊆ non-wrap, k=\|E'\| (k=2) | **1.0000** | 24885/24885 (+2371 n=6) |
| **B16** | G connected ∧ β=0 ⇒ `λ_min(L_sig) > 0` | G conn, β=0 | **1.0000** | 2852/2852 |
| **B17** | `‖L_möb‖_F² = ‖L_s‖_F² + ‖L_sig‖_F²` | — | **1.0000** | 3453/3453 |
| **B18** | `p_{L_möb}(x) = p_{L_s}(x) · p_{L_sig}(x)` (charpoly product) | — | **1.0000** | 13812/13812 (+1520 n=6) |
| **B19** | smallest-positive-eig(L_möb) = min over the two | — | **1.0000** | 3453/3453 |
| **B20** | `tr(L_möb) = 2 tr(L_s) = 2 tr(L_sig) = 4\|E\|` | — | **1.0000** | 3453/3453 |
| **B21** | `tr(sign(L_sig)) = n − β(G,W)` (L_sig PSD) | — | **1.0000** | 3453/3453 |

## R7 prover candidates (τ=1, ≥50 supports) — 18 qualify

Ranked by novelty + leverage:

1. **B7 spectrum-union** — highest leverage. Formalising this collapses B1, B6, B9, B12, B13, B17, B18, B19, B20 into one-line corollaries. Proof sketch: block-diagonalise L_möb in the ±-fibre basis `{(eᵤ,eᵤ)/√2, (eᵤ,−eᵤ)/√2}`; blocks = L_s and L_sig. Target: new `L16_SpectrumUnion.lean` or extend `L13_PSD.lean`.
2. **B18 charpoly factorisation** — polynomial-level equivalent of B7; often easier in Lean (Mathlib `Matrix.charpoly_blockDiagonal`). Natural addition to `L10_CoverCharpoly.lean`.
3. **B9 kernel-dim count** `dim ker L_möb = #comps + β` — immediate from B7 + R5-R10 + existing scalar kernel-dim in `KernelDimension.lean`. Coda to `L8_Recognition.lean`.
4. **B2 mixed trace** `tr(L_s L_sig) = Σdeg² + 2m − 4|W|` — ~5-line Lean proof.
5. **B20** `tr L_möb = 4\|E\|` — trivial exercise; append to `L9_Bounds.lean`.
6. **B21** `tr sign(L_sig) = n − β` — PSD + kernel-count corollary.
7. **B16** strict positivity — sharpens R5-R10.
8. **B11** kernel support — component-localised version of R5-R13.
9. **B14** single-edge flip stability — Weyl rank-2 perturbation, standard.
10. **B15** multi-edge interlacing — inductive generalisation of R5-R17.
11. **B4** Perron trace monotonicity — one-liner from PSD.
12. **B6, B8, B12, B13, B17, B19, B1** — corollaries of B7.

## Refinement band τ ∈ [0.5, 0.95]

**Empty** this round. Every claim held universally or failed with a clear structural counterexample.

## Refuted (τ < 0.2)

- **B3 (τ=0.0142)**: minimal CE `G=K₂`, `W={(0,1)}`: LHS=4, RHS=8. Root cause: L_möb is not block-diagonal in the standard `2u, 2u+1` basis, only in the ±-fibre basis. Dead; supersede by B7.
- **B5 / B10 (τ=0.1741 each)**: minimal CE `G=K₃, W={(0,1)}`. `spec(L_s)={0,3,3}`, λ_max=3; `spec(L_sig)={0,1,4}`, λ_max=4. Unbalanced triangle makes the signed spectrum exceed the scalar. Dead; correct bound `λ_max(L_sig) ≤ 2Δ(G)`.

## Sheaf-boundary section

### β ∩ α (spectral consequence of edge operation)

- **B14** — single-edge sign-flip stability: rank-2 perturbation triggered by α's wrap-flip primitive.
- **B15** — multi-edge interlacing: k non-wrap removals (α batch-op) ⇒ order-k interlacing. Generalises R5-R17.

### β ∩ γ (spectral encoding of cohomology / balance)

- **B9** — `dim ker L_möb = #comps + β`: composes β-invariant with γ-count.
- **B11** — `supp(v ∈ ker L_sig) = union of balanced comps`: eigenvector support encoded by γ-partition.
- **B16** — `conn ∧ β=0 ⇒ λ_min(L_sig) > 0`: spectral strict-positivity conditioned on γ.
- **B21** — `tr(sign L_sig) = n − β`: cleanest β ↔ γ one-liner.

## Net

18 new τ=1 β-claims (zero R5 overlap), 3 refuted with structural explanation. Central discovery: **B7** and equivalent **B18**, from which most other τ=1 claims follow.
