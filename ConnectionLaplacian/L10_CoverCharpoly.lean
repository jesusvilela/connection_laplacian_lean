/-
ConnectionLaplacian/L10_CoverCharpoly.lean

**Stratum L10 — Cover characteristic-polynomial split.**

Upgrades `scalarLap_cover_splits` (L5.4) from a *kernel-dimension* statement
to a *characteristic-polynomial* (i.e. full spectral) statement. Given that
the cover's scalar Laplacian is similar (via `Pcov`, reindexed by
`prodBoolEquivSum`) to the block-diagonal `fromBlocks(L_G, L_G^Möb)`,
we obtain a *multiplicative* spectral partition at the level of
characteristic polynomials:

  `(G̃).scalarLaplacian.charpoly =
     G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly`.

This is the Z/2-graded refinement of the flat/Möbius kernel-dim theorem of
L8, and feeds directly into multiplicativity of any determinantal spectral
invariant across the cover.

**Proof strategy:**
  1. Take `charpoly` of both sides of `scalarLap_cover_splits`.
  2. `charpoly_reindex` removes the `Matrix.reindex`.
  3. A bespoke `charpoly_conj` lemma (similarity invariance of the
     characteristic polynomial) collapses `P · L · P⁻¹` to `L`.
  4. `Matrix.charpoly_fromBlocks_zero₁₂` factors the block-diagonal
     charpoly into a product of the two diagonal charpolys.
-/

import ConnectionLaplacian.L5_Cover
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace ConnectionLaplacian

open Matrix BigOperators
open Polynomial (C)

namespace ConnGraph

variable (G : ConnGraph)

/-! ### Similarity invariance of the characteristic polynomial.

Classical fact: `(P · M · P⁻¹).charpoly = M.charpoly` whenever `P` is
invertible. Not available off-the-shelf for `Matrix` in Mathlib
(there is a `LinearEquiv.charpoly_conj`, but only at the level of
`Module.End`). We prove it directly via `charmatrix`.
-/

/-- Similarity by an invertible matrix preserves the characteristic
polynomial. -/
theorem _root_.Matrix.charpoly_conj_of_isUnit_det
    {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n R} (hPunit : IsUnit P.det) (L : Matrix n n R) :
    (P * L * P⁻¹).charpoly = L.charpoly := by
  classical
  set CP : Matrix n n (Polynomial R) := (C (R := R)).mapMatrix P
  set CPinv : Matrix n n (Polynomial R) := (C (R := R)).mapMatrix P⁻¹
  set CL : Matrix n n (Polynomial R) := (C (R := R)).mapMatrix L
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPunit
  -- `C.mapMatrix` preserves the product `P * P⁻¹ = 1`.
  have hCPinv_mul : CP * CPinv = 1 := by
    show (C (R := R)).mapMatrix P * (C (R := R)).mapMatrix P⁻¹ = 1
    rw [← _root_.map_mul ((C (R := R)).mapMatrix) P P⁻¹, hPinv, _root_.map_one]
  -- `C.mapMatrix` is multiplicative on the triple product too.
  have hCtriple : (C (R := R)).mapMatrix (P * L * P⁻¹) = CP * CL * CPinv := by
    rw [_root_.map_mul, _root_.map_mul]
  -- `scalar n X` is central: commutes with any `C.mapMatrix A`.
  have hcomm : ∀ A : Matrix n n R,
      Matrix.scalar n (Polynomial.X (R := R)) * (C (R := R)).mapMatrix A =
      (C (R := R)).mapMatrix A * Matrix.scalar n (Polynomial.X (R := R)) := by
    intro A
    exact (Matrix.scalar_commute _ Polynomial.commute_X _).eq
  -- Conjugating `scalar n X` by `C.mapMatrix P` is a no-op.
  have hsc : Matrix.scalar n (Polynomial.X (R := R)) =
      CP * Matrix.scalar n (Polynomial.X (R := R)) * CPinv := by
    have h1 : CP * Matrix.scalar n (Polynomial.X (R := R)) =
              Matrix.scalar n (Polynomial.X (R := R)) * CP := (hcomm P).symm
    calc Matrix.scalar n (Polynomial.X (R := R))
        = Matrix.scalar n (Polynomial.X (R := R)) * (CP * CPinv) := by
            rw [hCPinv_mul, Matrix.mul_one]
      _ = Matrix.scalar n (Polynomial.X (R := R)) * CP * CPinv := by
            rw [Matrix.mul_assoc]
      _ = CP * Matrix.scalar n (Polynomial.X (R := R)) * CPinv := by rw [← h1]
  -- `charmatrix` of the conjugate factors as a conjugation.
  have hCM : charmatrix (P * L * P⁻¹) = CP * charmatrix L * CPinv := by
    show Matrix.scalar n (Polynomial.X (R := R)) -
          (C (R := R)).mapMatrix (P * L * P⁻¹) =
        CP *
          (Matrix.scalar n (Polynomial.X (R := R)) - (C (R := R)).mapMatrix L) *
          CPinv
    rw [hCtriple, Matrix.mul_sub, Matrix.sub_mul]
    show Matrix.scalar n (Polynomial.X (R := R)) - CP * CL * CPinv =
        CP * Matrix.scalar n (Polynomial.X (R := R)) * CPinv - CP * CL * CPinv
    rw [← hsc]
  -- Take determinants on both sides.
  unfold Matrix.charpoly
  rw [hCM, Matrix.det_mul, Matrix.det_mul]
  have hdetprod : CP.det * CPinv.det = 1 := by
    rw [← Matrix.det_mul, hCPinv_mul, Matrix.det_one]
  have hring :
      CP.det * (charmatrix L).det * CPinv.det =
      CP.det * CPinv.det * (charmatrix L).det := by ring
  rw [hring, hdetprod, one_mul]

/-! ### The cover charpoly split. -/

/-- **L10 — Multiplicative spectral partition across the orientation
double cover.**

The characteristic polynomial of the cover's (ordinary) scalar Laplacian
factors as the product of the base scalar Laplacian's charpoly and the
signed (Möbius) Laplacian's charpoly. This upgrades the kernel-dim
statement of `scalarLap_cover_kernel_dim` to a full spectral identity. -/
theorem cover_charpoly_eq_scalar_times_mobius :
    (G.orientationDoubleCover.scalarLaplacian).charpoly =
      G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly := by
  -- Extract the similarity+reindex witness from L5.4.
  obtain ⟨P, hPdet, hreindex⟩ := G.scalarLap_cover_splits
  -- Step 1. Apply `charpoly` to both sides of the block-similarity identity.
  have hcp := congrArg Matrix.charpoly hreindex
  -- LHS: `charpoly (reindex e e (P · L · P⁻¹)) = charpoly (P · L · P⁻¹) = charpoly L`.
  rw [Matrix.charpoly_reindex] at hcp
  rw [Matrix.charpoly_conj_of_isUnit_det (Ne.isUnit hPdet)] at hcp
  -- RHS: block-diagonal charpoly factors.
  rw [Matrix.charpoly_fromBlocks_zero₁₂] at hcp
  exact hcp

end ConnGraph

end ConnectionLaplacian
