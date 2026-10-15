/-
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
    have hleft : (M * V) i k =
        (M *ᵥ (fun j : Fin n => root k ^ j.val)) i := by
      rfl
    have hright : (V * Matrix.diagonal eig) i k =
        root k ^ i.val * eig k := by
      simp [Matrix.mul_apply, Matrix.diagonal, V, Matrix.vandermonde]
    rw [hleft, hright]
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      congrFun (heig k) i
  have hM : M = V * Matrix.diagonal eig * V⁻¹ := by
    calc
      M = M * (V * V⁻¹) := by
        rw [Matrix.mul_nonsing_inv V (Ne.isUnit hdet), Matrix.mul_one]
      _ = (M * V) * V⁻¹ := by rw [Matrix.mul_assoc]
      _ = V * Matrix.diagonal eig * V⁻¹ := by rw [hdiag]
  have hchar : (Matrix.diagonal eig).charpoly =
      ∏ k : Fin n, (Polynomial.X - Polynomial.C (eig k)) := by
    have hcharmatrix :
        Matrix.charmatrix (Matrix.diagonal eig) =
          Matrix.diagonal (fun k : Fin n =>
            (Polynomial.X : Polynomial ℂ) - Polynomial.C (eig k)) := by
      ext i j
      by_cases h : i = j
      · subst j
        simp [Matrix.charmatrix, Matrix.diagonal]
      · simp [Matrix.charmatrix, Matrix.diagonal, h]
    rw [Matrix.charpoly, hcharmatrix, Matrix.det_diagonal]
  rw [hM, Matrix.charpoly_conj_of_isUnit_det (Ne.isUnit hdet)]
  exact hchar

/-- The standard primitive n-th complex root used as a spectral parameter. -/
private noncomputable def ζ (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))

/-- The anti-periodic twist, whose n-th power is -1. -/
private noncomputable def α (n : ℕ) : ℂ :=
  Complex.exp (Real.pi * Complex.I / (n : ℂ))

private theorem ζ_primitive (n : ℕ) (hn : 3 ≤ n) :
    IsPrimitiveRoot (ζ n) n := by
  exact Complex.isPrimitiveRoot_exp n (by omega)

private theorem ζ_injective (n : ℕ) (hn : 3 ≤ n) :
    Function.Injective (fun k : Fin n => (ζ n) ^ k.val) := by
  intro i j hij
  exact Fin.ext ((ζ_primitive n hn).pow_inj i.isLt j.isLt hij)

private theorem αζ_injective (n : ℕ) (hn : 3 ≤ n) :
    Function.Injective (fun k : Fin n => α n * (ζ n) ^ k.val) := by
  intro i j hij
  apply ζ_injective n hn
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hij

end ConnectionLaplacian.Cycle
