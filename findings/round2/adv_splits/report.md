# Adversarial audit — `scalarLap_cover_splits` strategy

**Target:** `ConnectionLaplacian/L5_Cover.lean:176`
**Reference proof (analogous, closed):** `ConnectionLaplacian/KernelDimension.lean:229-355` (`laplacian_decomposes`)
**Strategy stressed:** `P := (1 : Matrix G.V G.V ℝ) ⊗ₖ R` with R = 2×2 Hadamard, P² = 2·I so P⁻¹ = (½)P.

## Concrete 2-vertex example (1 wrap edge) — strategy IS internally consistent

V = {a,b}, single wrap edge a-b. Cover order ((a,F),(a,T),(b,F),(b,T)):
```
L̃ = [ 1  0  0 -1]     as V-major 2×2 blocks:
     [ 0  1 -1  0]       diag(a,a) = diag(b,b) = I₂
     [ 0 -1  1  0]       off-diag(a,b) = off-diag(b,a) = -σx   (wrap flips sheet)
     [-1  0  0  1]
```
With P = 1 ⊗ R, R = `!![1,1;1,-1]`, P⁻¹ = (½)P:
- P L̃ P⁻¹ in V-major 2×2 blocks: diag = I₂, off-diag = diag(-1,+1).
- After `prodBoolEquivSum` reindex (groups by Bool first): (inl,inl) agrees with `scalarLaplacian` (diag 1, off-diag -1); (inr,inr) agrees with `signedLaplacianMobius` for a wrap edge (diag 1, off-diag **+1**). Cross-blocks vanish.

## Cracks (ordered by severity)

1. **CRACK-1 (HIGH) — Cover Laplacian is NOT `laplacianBlock`.** The docstring glosses over a type-level gap. `laplacian_decomposes` operates on `G.laplacian true : Matrix (V × Fin 2) (V × Fin 2) ℝ` built from `laplacianBlock`. Here `G.orientationDoubleCover.scalarLaplacian = coverGraph.lapMatrix ℝ` is Mathlib's `degMatrix − adjMatrix` on `V × Bool`. The identity `L̃((u,b),(v,c)) = laplacianBlock ...` is NOT automatic; it requires ~60-line case analysis unfolding `coverAdj` and matching `laplacianBlock`. **This glue lemma does not currently exist.**

2. **CRACK-2 (HIGH) — Bool vs Fin 2 Hadamard mismatch.** `RhatMob : Matrix (Fin 2) (Fin 2) ℝ` not usable at L5 because `CoverV = V × Bool`. All of `RhatMob_sq`, `RhatMob_I₂_RhatMob`, `RhatMob_σx_RhatMob`, `hPent`, `hPL`, `hPLP` must be redone on Bool-indexed Hadamard, or wrapped through a `Matrix.reindex`. Non-trivial duplication; `fin_cases` becomes `cases b : Bool`.

3. **CRACK-3 (MED) — Kronecker block-axis vs reindex Sum-axis are orthogonal.** Mathlib convention: `(A ⊗ₖ B)(i₁,i₂)(j₁,j₂) = A i₁ j₁ · B i₂ j₂`. So `1_V ⊗ R` is **V-block-diagonal**. But `prodBoolEquivSum` groups codomain **Bool-first**. The `Finset.sum_eq_single` telescopes still apply but need re-derivation.

4. **CRACK-4 (MED) — `signedLaplacianMobius` sign convention.** Diagonal = degree, off-diag = **+1 on wrap** and **−1 on non-wrap**. Confirmed by the 2-vertex hand-check. Any stray "wrap = −1" expectation introduces sign error.

5. **CRACK-5 (LOW) — Nondegeneracy via `Matrix.det_kronecker`.** `det(1_V ⊗ R) = det(1)^2 · det(R)^|V| = (−2)^|V|` ≠ 0.

6. **CRACK-6 (LOW) — Cover degree = base degree.** Each G-neighbor v of u contributes exactly one cover-neighbor of (u,b). Needs ~10-line bijection lemma.

7. **CRACK-7 (LOW) — `orientationDoubleCover.wrap = const False` only used implicitly.** Target uses `scalarLaplacian` (wrap-agnostic). No crack, just confirmation.

## Verdict

Strategy is **mathematically sound** (concrete 2-vertex example checks out). However, it is **NOT a quick port** of `laplacian_decomposes`: the three non-trivial gaps are (a) translating `coverGraph.lapMatrix` to `laplacianBlock`-shaped entries (CRACK-1,6), (b) Bool-indexed Hadamard infrastructure (CRACK-2), (c) re-deriving `hPLP` with Kronecker outer-V / reindex Bool-first index inversion (CRACK-3). Estimated fresh Lean: ~200 lines.

Strategic suggestion: the downstream corollary `scalarLap_cover_kernel_dim` is strictly weaker. It can likely be closed via `symProj`/`antiProj` directly, sidestepping all six cracks above. If L8 only calls the corollary, the main `scalarLap_cover_splits` theorem may be deferrable.
