/-!
# Full cycle spectra, including algebraic multiplicities

This file is developed on an isolated proof branch and is not part of the
production theorem spine until the scalar and signed cycle statements have
both been checked by Lean.

The abstract Vandermonde assembly lemma below prevents the unsound inference
from per-frequency eigenpairs to multiset equality: it explicitly requires
injectivity of the spectral parameters (and hence an invertible basis).
-/
import ConnectionLaplacian.CycleSpectrum
import ConnectionLaplacian.L10_CoverCharpoly
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section

namespace ConnectionLaplacian.Cycle

open Matrix Polynomial BigOperators Complex

/-- A complete Vandermonde eigenbasis determines the entire characteristic
polynomial, including all algebraic multiplicities. The columns are
`j ↦ (root k) ^ j`; injectivity of `root` certifies they are a basis. -/
theorem charpoly_of_vandermonde_eigenbasis
    {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ)
    (root eig : Fin n → ℂ)
    (hroot : Function.Injective root)
    (heig : ∀ k : Fin n,
      M.mulVec (fun j : Fin n => root k ^ j.val) =
        eig k • (fun j : Fin n => root k ^ j.val)) :
    M.charpoly = ∏ k : Fin n, (Polynomial.X - Polynomial.C (eig k)) := by
  let V : Matrix (Fin n) (Fin n) ℂ := (Matrix.vandermonde root)ᵀ
  have hdet : V.det ≠ 0 := by
    dsimp [V]
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hroot
  have hdiag : M * V = V * Matrix.diagonal eig := by
    ext i k
    simpa only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.transpose_apply,
      Matrix.vandermonde_apply, V, Matrix.mulVec_apply_eq_sum,
      Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun (heig k) i
  have hM : M = V * Matrix.diagonal eig * V⁻¹ := by
    calc
      M = M * (V * V⁻¹) := by
        rw [Matrix.mul_nonsing_inv V (Ne.isUnit hdet), Matrix.mul_one]
      _ = (M * V) * V⁻¹ := by rw [Matrix.mul_assoc]
      _ = V * Matrix.diagonal eig * V⁻¹ := by rw [hdiag]
  rw [hM, Matrix.charpoly_conj_of_isUnit_det (Ne.isUnit hdet),
    Matrix.charpoly_diagonal]

end ConnectionLaplacian.Cycle
