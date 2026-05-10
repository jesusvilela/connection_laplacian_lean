import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Complex

noncomputable def ω (n : Nat) [NeZero n] : ℂ :=
  exp (2 * Real.pi * I / n)

theorem ω_pow_n (n : Nat) [hn : NeZero n] : (ω n) ^ n = 1 := by
  unfold ω
  have h1 : (n : ℂ) * (2 * Real.pi * I / n) = 2 * Real.pi * I := by
    field_simp [hn.out]; ring
  rw [← exp_nat_mul, h1]
  exact Complex.exp_two_pi_mul_I

theorem conj_ω (n : Nat) [NeZero n] : star (ω n) = (ω n)⁻¹ := by
  unfold ω
  show conj (exp (2 * Real.pi * I / n)) = _
  rw [Complex.exp_conj]
  have : conj (2 * Real.pi * I / n : ℂ) = -(2 * Real.pi * I / n) := by
    simp [conj_ofReal, conj_I]; ring
  rw [this, exp_neg]

theorem ω_zpow_neg (n : Nat) [NeZero n] (k : ℤ) : star ((ω n) ^ k) = (ω n) ^ (-k) := by
  rw [star_zpow₀, conj_ω, _root_.zpow_neg]

theorem ω_zpow_mod_n (n : Nat) [NeZero n] (k : ℤ) : (ω n) ^ k = (ω n) ^ (k % n) := by
  conv_lhs => rw [← Int.emod_add_ediv k n]
  have h_ne : ω n ≠ 0 := by unfold ω; exact exp_ne_zero _
  rw [zpow_add₀ h_ne, _root_.zpow_mul]
  have : (ω n) ^ (n : ℤ) = 1 := by exact_mod_cast (ω_pow_n n)
  rw [this, _root_.one_zpow, mul_one]
