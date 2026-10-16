/-
# Full cycle spectra, including algebraic multiplicities

This file is in the production theorem spine. Both scalar and signed full
cycle spectral multisets, with algebraic multiplicity, are checked by Lean
for every n >= 3; the explicit end theorems appear in AxiomAudit.lean.

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


/-! ### The complete Fourier eigen-equations on both cycles -/

/-- The preceding power, written using an inverse in a field. -/
private theorem pow_pred (z : ℂ) (hz : z ≠ 0) (m : ℕ) (hm : 0 < m) :
    z ^ (m - 1) = z ^ m * z⁻¹ := by
  have hp : z ^ m = z ^ (m - 1) * z := by
    calc
      z ^ m = z ^ (m - 1 + 1) := by congr 1; omega
      _ = z ^ (m - 1) * z := pow_succ _ _
  calc
    z ^ (m - 1) = (z ^ (m - 1) * z) * z⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hz, mul_one]
    _ = z ^ m * z⁻¹ := by rw [hp]

/-- The periodic complex Fourier vectors are eigenvectors of the *actual
complexification* of the scalar cycle Laplacian, including the seam. -/
theorem scalarCycle_eigenvector_complex
    (n : ℕ) (hn : 3 ≤ n) (z : ℂ) (hz : z ^ n = 1) :
    (((scalarCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ)).mulVec
      (fun j : Fin n => z ^ j.val)) =
        (2 - z - z⁻¹) • (fun j : Fin n => z ^ j.val) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : n ≠ 0)] at hz
    norm_num at hz
  funext i
  rw [scalar_mulVec_row_complex n hn (fun j : Fin n => z ^ j.val) i,
      Pi.smul_apply, smul_eq_mul]
  change 2 * z ^ i.val -
      z ^ (succFin n (by omega) i).val -
      z ^ (predFin n (by omega) i).val =
        (2 - z - z⁻¹) * z ^ i.val
  by_cases hi0 : i.val = 0
  · have hs : (succFin n (by omega) i).val = 1 := by
      rw [succFin_val_at_lt n (by omega) i (by omega), hi0]
    have hp : (predFin n (by omega) i).val = n - 1 :=
      predFin_val_at_zero n (by omega) i hi0
    rw [hs, hp, hi0, pow_zero, pow_one,
        pow_pred z hz0 n (by omega), hz]
    ring
  · by_cases hilast : i.val + 1 = n
    · have hs : (succFin n (by omega) i).val = 0 :=
        succFin_val_at_eq n (by omega) i hilast
      have hp : (predFin n (by omega) i).val = i.val - 1 :=
        predFin_val_at_pos n (by omega) i (by omega)
      rw [hs, hp, pow_zero, pow_pred z hz0 i.val (by omega)]
      have hlast : z ^ i.val * z = 1 := by
        calc
          z ^ i.val * z = z ^ (i.val + 1) := (pow_succ _ _).symm
          _ = z ^ n := by rw [hilast]
          _ = 1 := hz
      calc
        2 * z ^ i.val - 1 - z ^ i.val * z⁻¹ =
            2 * z ^ i.val - (z ^ i.val * z) -
              z ^ i.val * z⁻¹ := by rw [hlast]
        _ = (2 - z - z⁻¹) * z ^ i.val := by ring
    · have hs : (succFin n (by omega) i).val = i.val + 1 :=
        succFin_val_at_lt n (by omega) i (by omega)
      have hp : (predFin n (by omega) i).val = i.val - 1 :=
        predFin_val_at_pos n (by omega) i (by omega)
      rw [hs, hp, pow_succ, pow_pred z hz0 i.val (by omega)]
      ring

/-- The anti-periodic complex Fourier vectors are eigenvectors of the
*actual complexification* of the one-wrap signed cycle Laplacian. -/
theorem signedCycle_eigenvector_complex
    (n : ℕ) (hn : 3 ≤ n) (z : ℂ) (hz : z ^ n = -1) :
    (((signedCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ)).mulVec
      (fun j : Fin n => z ^ j.val)) =
        (2 - z - z⁻¹) • (fun j : Fin n => z ^ j.val) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : n ≠ 0)] at hz
    norm_num at hz
  funext i
  by_cases hi0 : i.val = 0
  · rw [signed_mulVec_zero_complex n hn (fun j : Fin n => z ^ j.val) i hi0,
        Pi.smul_apply, smul_eq_mul]
    change 2 * z ^ i.val - z ^ (1 : ℕ) + z ^ (n - 1) =
      (2 - z - z⁻¹) * z ^ i.val
    rw [hi0, pow_zero, pow_one, pow_pred z hz0 n (by omega), hz]
    ring
  · by_cases hilast : i.val = n - 1
    · rw [signed_mulVec_nm1_complex n hn (fun j : Fin n => z ^ j.val) i hilast,
          Pi.smul_apply, smul_eq_mul]
      change 2 * z ^ i.val - z ^ (n - 2) + z ^ (0 : ℕ) =
        (2 - z - z⁻¹) * z ^ i.val
      have hpred : n - 2 = i.val - 1 := by omega
      rw [hpred, pow_zero, pow_pred z hz0 i.val (by omega)]
      have hlast : z ^ i.val * z = -1 := by
        calc
          z ^ i.val * z = z ^ (i.val + 1) := (pow_succ _ _).symm
          _ = z ^ n := by congr 1; omega
          _ = -1 := hz
      calc
        2 * z ^ i.val - z ^ i.val * z⁻¹ + 1 =
            2 * z ^ i.val - z ^ i.val * z⁻¹ -
              (z ^ i.val * z) := by rw [hlast]; ring
        _ = (2 - z - z⁻¹) * z ^ i.val := by ring
    · have hi : 1 ≤ i.val := by omega
      have hi' : i.val + 1 < n := by omega
      rw [signed_mulVec_middle_complex n hn
            (fun j : Fin n => z ^ j.val) i hi hi',
          Pi.smul_apply, smul_eq_mul]
      change 2 * z ^ i.val - z ^ (i.val + 1) - z ^ (i.val - 1) =
        (2 - z - z⁻¹) * z ^ i.val
      rw [pow_succ, pow_pred z hz0 i.val hi]
      ring

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


/-! ### Fourier roots and full characteristic-polynomial products -/

private theorem ζ_power_is_periodic (n : ℕ) (hn : 3 ≤ n)
    (k : Fin n) : ((ζ n) ^ k.val) ^ n = 1 := by
  rw [← pow_mul, Nat.mul_comm k.val n, pow_mul,
      (ζ_primitive n hn).pow_eq_one, one_pow]

private theorem α_power_is_antiperiodic (n : ℕ) (hn : 3 ≤ n) :
    (α n) ^ n = -1 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold α
  rw [← Complex.exp_nat_mul]
  have harg : (n : ℂ) * (Real.pi * Complex.I / (n : ℂ)) =
      Real.pi * Complex.I := by
    field_simp [hn0]
  rw [harg, Complex.exp_pi_mul_I]

private theorem αζ_power_is_antiperiodic (n : ℕ) (hn : 3 ≤ n)
    (k : Fin n) : (α n * (ζ n) ^ k.val) ^ n = -1 := by
  rw [mul_pow, α_power_is_antiperiodic n hn,
      ζ_power_is_periodic n hn k, mul_one]

/-- **Full scalar-cycle characteristic polynomial over ℂ**, including
algebraic multiplicities of equal eigenvalues. No counting-of-cosines
assumption is used: the Fourier root parameters form an injective
Vandermonde eigenbasis. -/
theorem scalarCycle_charpoly_complex (n : ℕ) (hn : 3 ≤ n) :
    ((scalarCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ)).charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (2 - (ζ n) ^ k.val - ((ζ n) ^ k.val)⁻¹)) := by
  exact charpoly_of_vandermonde_eigenbasis
    ((scalarCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ))
    (fun k : Fin n => (ζ n) ^ k.val)
    (fun k : Fin n => 2 - (ζ n) ^ k.val - ((ζ n) ^ k.val)⁻¹)
    (ζ_injective n hn)
    (fun k => scalarCycle_eigenvector_complex n hn
      ((ζ n) ^ k.val) (ζ_power_is_periodic n hn k))

/-- **Full one-wrap Möbius signed-cycle characteristic polynomial over ℂ**,
including repeated eigenvalues. The anti-periodic Fourier parameters form
an invertible Vandermonde matrix. -/
theorem signedCycle_charpoly_complex (n : ℕ) (hn : 3 ≤ n) :
    ((signedCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ)).charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (2 - α n * (ζ n) ^ k.val -
          (α n * (ζ n) ^ k.val)⁻¹)) := by
  exact charpoly_of_vandermonde_eigenbasis
    ((signedCycleLaplacian n (by omega)).map (algebraMap ℝ ℂ))
    (fun k : Fin n => α n * (ζ n) ^ k.val)
    (fun k : Fin n =>
      2 - α n * (ζ n) ^ k.val - (α n * (ζ n) ^ k.val)⁻¹)
    (αζ_injective n hn)
    (fun k => signedCycle_eigenvector_complex n hn
      (α n * (ζ n) ^ k.val) (αζ_power_is_antiperiodic n hn k))


/-! ### Euler phases and descent to the paper's real cosine spectra -/

/-- Euler's cosine identity for the unit-modulus complex phase. -/
private theorem exp_phase_plus_inv (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) +
      (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
        ((2 * Real.cos θ : ℝ) : ℂ) := by
  simp only [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos,
    neg_mul, Complex.exp_neg]
  norm_num <;> ring

private theorem ζ_power_is_phase (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    (ζ n) ^ k.val =
      Complex.exp ((((2 * Real.pi * (k.val : ℝ) / n : ℝ) : ℂ)) *
        Complex.I) := by
  unfold ζ
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem αζ_power_is_phase (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    α n * (ζ n) ^ k.val =
      Complex.exp ((((Real.pi * (2 * (k.val : ℝ) + 1) / n : ℝ) : ℂ)) *
        Complex.I) := by
  unfold α ζ
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem ζ_eigenvalue_cos (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    2 - (ζ n) ^ k.val - ((ζ n) ^ k.val)⁻¹ =
      (((2 - 2 * Real.cos (2 * Real.pi * k.val / n) : ℝ)) : ℂ) := by
  rw [ζ_power_is_phase n hn k]
  set θ : ℝ := 2 * Real.pi * (k.val : ℝ) / n
  have hphase := exp_phase_plus_inv θ
  calc
    2 - Complex.exp ((θ : ℂ) * Complex.I) -
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
          2 - (Complex.exp ((θ : ℂ) * Complex.I) +
            (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) := by ring
    _ = 2 - ((2 * Real.cos θ : ℝ) : ℂ) := by rw [hphase]
    _ = (((2 - 2 * Real.cos θ : ℝ)) : ℂ) := by push_cast; ring

private theorem αζ_eigenvalue_cos (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    2 - α n * (ζ n) ^ k.val -
        (α n * (ζ n) ^ k.val)⁻¹ =
      (((2 - 2 * Real.cos ((2 * k.val + 1) * Real.pi / n) : ℝ)) : ℂ) := by
  rw [αζ_power_is_phase n hn k]
  set θ : ℝ := Real.pi * (2 * (k.val : ℝ) + 1) / n
  have hphase := exp_phase_plus_inv θ
  have hθ : θ = (2 * (k.val : ℝ) + 1) * Real.pi / n := by
    dsimp [θ]; ring
  rw [← hθ]
  calc
    2 - Complex.exp ((θ : ℂ) * Complex.I) -
        (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
          2 - (Complex.exp ((θ : ℂ) * Complex.I) +
            (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) := by ring
    _ = 2 - ((2 * Real.cos θ : ℝ) : ℂ) := by rw [hphase]
    _ = (((2 - 2 * Real.cos θ : ℝ)) : ℂ) := by push_cast; ring

/-- The paper's **complete flat scalar cycle spectrum** as a
real characteristic-polynomial product for every n ≥ 3. The factors
are indexed by every Fourier frequency, so multiplicity is preserved. -/
theorem scalarCycle_charpoly_real (n : ℕ) (hn : 3 ≤ n) :
    (scalarCycleLaplacian n (by omega)).charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (2 - 2 * Real.cos (2 * Real.pi * k.val / n))) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
  rw [← Matrix.charpoly_map]
  rw [Polynomial.map_prod]
  simp_rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [scalarCycle_charpoly_complex n hn]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [ζ_eigenvalue_cos n hn k]
  rfl

/-- The paper's **complete one-wrap Möbius signed cycle spectrum** as a
real characteristic-polynomial product for every n ≥ 3. -/
theorem signedCycle_charpoly_real (n : ℕ) (hn : 3 ≤ n) :
    (signedCycleLaplacian n (by omega)).charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (2 - 2 * Real.cos ((2 * k.val + 1) * Real.pi / n))) := by
  apply Polynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
  rw [← Matrix.charpoly_map]
  rw [Polynomial.map_prod]
  simp_rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [signedCycle_charpoly_complex n hn]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [αζ_eigenvalue_cos n hn k]
  rfl

/-- Scalar cycle spectrum as a multiset, with algebraic multiplicity. -/
theorem scalarCycle_roots_real (n : ℕ) (hn : 3 ≤ n) :
    (scalarCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun k : Fin n => 2 - 2 * Real.cos (2 * Real.pi * k.val / n))
        (Finset.univ : Finset (Fin n)).val := by
  rw [scalarCycle_charpoly_real n hn, Polynomial.roots_prod]
  · simp_rw [Polynomial.roots_X_sub_C]
    rw [Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr
      (fun k _ => Polynomial.X_sub_C_ne_zero _)

/-- One-wrap Möbius cycle spectrum as a multiset, with algebraic multiplicity. -/
theorem signedCycle_roots_real (n : ℕ) (hn : 3 ≤ n) :
    (signedCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun k : Fin n =>
          2 - 2 * Real.cos ((2 * k.val + 1) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val := by
  rw [signedCycle_charpoly_real n hn, Polynomial.roots_prod]
  · simp_rw [Polynomial.roots_X_sub_C]
    rw [Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr
      (fun k _ => Polynomial.X_sub_C_ne_zero _)

end ConnectionLaplacian.Cycle
