import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Matrix BigOperators Complex

variable {n : Nat} [NeZero n]

noncomputable def ω (n : Nat) [NeZero n] : ℂ :=
  exp (2 * Real.pi * I / n)

theorem ω_pow_n (n : Nat) [hn : NeZero n] : (ω n) ^ n = 1 := by
  unfold ω
  have h1 : (n : ℂ) * (2 * Real.pi * I / n) = 2 * Real.pi * I := by
    field_simp [hn.out]; ring
  have h2 : (exp (2 * Real.pi * I / n)) ^ (n : ℂ) = exp (2 * Real.pi * I) := by
    rw [← exp_nat_mul]
    -- wait, exp_nat_mul is (exp z)^n = exp (n * z). The type of n is Nat.
    -- (exp z) ^ (n : Nat)
    sorry
