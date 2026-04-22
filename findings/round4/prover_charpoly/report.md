# PROVER-CHARPOLY — Round 4 report

**Status: LANDED (green, zero `sorry`, clean axioms).**

## What landed

- **New file:** `ConnectionLaplacian/L10_CoverCharpoly.lean`
- **Target theorem proven:**
```lean
theorem cover_charpoly_eq_scalar_times_mobius (G : ConnGraph) :
    (G.orientationDoubleCover.scalarLaplacian).charpoly =
      G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly
```
Upgrades `scalarLap_cover_kernel_dim` (kernel-dim only) to a full spectral identity.
- **Added to import manifest:** `ConnectionLaplacian.lean` now imports `L10_CoverCharpoly`.

## Bonus reusable lemma (not in Mathlib)

```lean
theorem Matrix.charpoly_conj_of_isUnit_det
    {R} [CommRing R] {n} [Fintype n] [DecidableEq n]
    {P : Matrix n n R} (hPunit : IsUnit P.det) (L : Matrix n n R) :
    (P * L * P⁻¹).charpoly = L.charpoly
```

Matrix-level similarity invariance of the characteristic polynomial. Mathlib only has `LinearEquiv.charpoly_conj` for `Module.End`.

## Axiom check

- `cover_charpoly_eq_scalar_times_mobius`: `[propext, Classical.choice, Quot.sound]`
- `Matrix.charpoly_conj_of_isUnit_det`: `[propext, Classical.choice, Quot.sound]`

No `sorryAx`. Full project `lake build` green.

## Mathlib API used

- `Matrix.charpoly`, `Matrix.charmatrix`
- `Matrix.charpoly_reindex` — strips `reindex`
- `Matrix.charpoly_fromBlocks_zero₁₂` — factors block-diagonal charpoly
- `Matrix.scalar_commute` + `Polynomial.commute_X` — centrality of `scalar n X`
- `Matrix.det_mul`, `Matrix.det_one`, `Matrix.mul_nonsing_inv`
- `RingHom.mapMatrix` multiplicativity via `map_mul`/`map_one`

## Proof skeleton

1. `scalarLap_cover_splits` produces `⟨P, hPdet, hreindex⟩` with `reindex e e (P · L̃cov · P⁻¹) = fromBlocks L_G 0 0 L_G^Möb`.
2. `congrArg Matrix.charpoly hreindex`.
3. `Matrix.charpoly_reindex` strips the reindex from the LHS.
4. `Matrix.charpoly_conj_of_isUnit_det (Ne.isUnit hPdet)` collapses `P · L̃cov · P⁻¹ → L̃cov`.
5. `Matrix.charpoly_fromBlocks_zero₁₂` factors the RHS block-diagonal.

## Upstream candidate

`Matrix.charpoly_conj_of_isUnit_det` → `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`.
