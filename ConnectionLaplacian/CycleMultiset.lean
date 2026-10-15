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

/-! ### Complexification of established real cycle row identities -/

/-- Taking the real part commutes with multiplying a complex vector by a
real matrix whose coefficients have been embedded into the complex field. -/
private theorem complexify_mulVec_re {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℂ) (i : Fin n) :
    (((M.map (algebraMap ℝ ℂ)) *ᵥ w) i).re =
      (M *ᵥ (fun j => (w j).re)) i := by
  simp [Matrix.mulVec, Matrix.dotProduct, Complex.re_sum, Complex.mul_re]

/-- The corresponding imaginary-part identity. -/
private theorem complexify_mulVec_im {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℂ) (i : Fin n) :
    (((M.map (algebraMap ℝ ℂ)) *ᵥ w) i).im =
      (M *ᵥ (fun j => (w j).im)) i := by
  simp [Matrix.mulVec, Matrix.dotProduct, Complex.im_sum, Complex.mul_im]

/-- Transport any three-term real row identity to complex vectors.
All coefficients and vertex indices are preserved exactly. -/
private theorem complexify_three_term {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i p q : Fin n)
    (a b c : ℝ)
    (hrow : ∀ v : Fin n → ℝ,
      (M *ᵥ v) i = a * v i + b * v p + c * v q)
    (w : Fin n → ℂ) :
    ((M.map (algebraMap ℝ ℂ)) *ᵥ w) i =
      (a : ℂ) * w i + (b : ℂ) * w p + (c : ℂ) * w q := by
  apply Complex.ext
  · rw [complexify_mulVec_re]
    simpa [Complex.add_re, Complex.mul_re] using
      hrow (fun j => (w j).re)
  · rw [complexify_mulVec_im]
    simpa [Complex.add_im, Complex.mul_im] using
      hrow (fun j => (w j).im)

/-- Complexified scalar cycle Laplacian: a three-point row stencil.
This is obtained from the already kernel-checked real row theorem,
not from an independent reimplementation of the matrix. -/
theorem scalar_mulVec_row_complex
    (n : ℕ) (hn : 3 ≤ n) (w : Fin n → ℂ) (i : Fin n) :
    (((scalarCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ)) *ᵥ w) i =
      2 * w i - w (succFin n (by omega) i) -
        w (predFin n (by omega) i) := by
  have hrow (v : Fin n → ℝ) :
      ((scalarCycleLaplacian n (by omega)) *ᵥ v) i =
        2 * v i + (-1) * v (succFin n (by omega) i) +
          (-1) * v (predFin n (by omega) i) := by
    convert scalar_mulVec_row n hn v i using 1 <;> ring
  have h := complexify_three_term
    (scalarCycleLaplacian n (by omega)) i
    (succFin n (by omega) i) (predFin n (by omega) i)
    2 (-1) (-1) hrow w
  simpa [sub_eq_add_neg, mul_comm] using h

/-- Complexified signed cycle Laplacian, interior row. -/
theorem signed_mulVec_middle_complex
    (n : ℕ) (hn : 3 ≤ n) (w : Fin n → ℂ) (i : Fin n)
    (h1 : 1 ≤ i.val) (h2 : i.val + 1 < n) :
    (((signedCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ)) *ᵥ w) i =
      2 * w i - w ⟨i.val + 1, by omega⟩ -
        w ⟨i.val - 1, by omega⟩ := by
  have hrow (v : Fin n → ℝ) :
      ((signedCycleLaplacian n (by omega)) *ᵥ v) i =
        2 * v i + (-1) * v ⟨i.val + 1, by omega⟩ +
          (-1) * v ⟨i.val - 1, by omega⟩ := by
    convert signed_mulVec_middle n hn v i h1 h2 using 1 <;> ring
  have h := complexify_three_term
    (signedCycleLaplacian n (by omega)) i
    ⟨i.val + 1, by omega⟩ ⟨i.val - 1, by omega⟩
    2 (-1) (-1) hrow w
  simpa [sub_eq_add_neg, mul_comm] using h

/-- Complexified signed cycle Laplacian, zero row (anti-periodic seam). -/
theorem signed_mulVec_zero_complex
    (n : ℕ) (hn : 3 ≤ n) (w : Fin n → ℂ) (i : Fin n)
    (hi : i.val = 0) :
    (((signedCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ)) *ᵥ w) i =
      2 * w i - w ⟨1, by omega⟩ +
        w ⟨n - 1, by omega⟩ := by
  have hrow (v : Fin n → ℝ) :
      ((signedCycleLaplacian n (by omega)) *ᵥ v) i =
        2 * v i + (-1) * v ⟨1, by omega⟩ +
          1 * v ⟨n - 1, by omega⟩ := by
    convert signed_mulVec_zero n hn v i hi using 1 <;> ring
  have h := complexify_three_term
    (signedCycleLaplacian n (by omega)) i
    ⟨1, by omega⟩ ⟨n - 1, by omega⟩
    2 (-1) 1 hrow w
  simpa [sub_eq_add_neg, mul_comm] using h

/-- Complexified signed cycle Laplacian, final row (anti-periodic seam). -/
theorem signed_mulVec_nm1_complex
    (n : ℕ) (hn : 3 ≤ n) (w : Fin n → ℂ) (i : Fin n)
    (hi : i.val = n - 1) :
    (((signedCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ)) *ᵥ w) i =
      2 * w i - w ⟨n - 2, by omega⟩ +
        w ⟨0, by omega⟩ := by
  have hrow (v : Fin n → ℝ) :
      ((signedCycleLaplacian n (by omega)) *ᵥ v) i =
        2 * v i + (-1) * v ⟨n - 2, by omega⟩ +
          1 * v ⟨0, by omega⟩ := by
    convert signed_mulVec_nm1 n hn v i hi using 1 <;> ring
  have h := complexify_three_term
    (signedCycleLaplacian n (by omega)) i
    ⟨n - 2, by omega⟩ ⟨0, by omega⟩
    2 (-1) 1 hrow w
  simpa [sub_eq_add_neg, mul_comm] using h

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
