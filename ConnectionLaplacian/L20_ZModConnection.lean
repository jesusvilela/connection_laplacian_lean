/-
ConnectionLaplacian/L20_ZModConnection.lean

**Stratum L20 — Z/n Connection Laplacian.**

This file initiates the Z/n generalization (v1.4 roadmap).
It defines the Z/n connection graph and its complex-valued Laplacian.
-/

import ConnectionLaplacian.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace ConnectionLaplacian

open Matrix BigOperators Complex

/-- A Z/n connection graph. -/
structure ZnConnGraph (n : Nat) [NeZero n] where
  V : Type*
  [finV : Fintype V]
  [decV : DecidableEq V]
  graph : SimpleGraph V
  [decG : DecidableRel graph.Adj]
  α : graph.Dart → ZMod n
  antisym : ∀ (d : graph.Dart), α d + α d.symm = 0

namespace ZnConnGraph

variable {n : Nat} [NeZero n] (Z : ZnConnGraph n)

instance : Fintype Z.V := Z.finV
instance : DecidableEq Z.V := Z.decV
instance : DecidableRel Z.graph.Adj := Z.decG

/-- The n-th root of unity ω = exp(2πi/n). -/
noncomputable def ω (n : Nat) [NeZero n] : ℂ :=
  exp (2 * Real.pi * I / n)

theorem ω_pow_n (n : Nat) [hn : NeZero n] : (ω n) ^ n = 1 := by
  unfold ω
  have h1 : (n : ℂ) * (2 * Real.pi * I / n) = 2 * Real.pi * I := by
    field_simp [hn.out]
  rw [← exp_nat_mul, h1]
  exact exp_two_pi_mul_I

theorem ω_ne_zero (n : Nat) [NeZero n] : ω n ≠ 0 := by
  unfold ω; exact exp_ne_zero _

theorem conj_ω (n : Nat) [NeZero n] : star (ω n) = (ω n)⁻¹ := by
  unfold ω
  change (starRingEnd ℂ) (Complex.exp (2 * Real.pi * I / n)) =
    (Complex.exp (2 * Real.pi * I / n))⁻¹
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  rw [map_div₀]
  simp [Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring_nf

theorem ω_zpow_neg (n : Nat) [NeZero n] (k : ℤ) : star ((ω n) ^ k) = (ω n) ^ (-k) := by
  change (starRingEnd ℂ) ((ω n) ^ k) = (ω n) ^ (-k)
  rw [map_zpow₀]
  change star (ω n) ^ k = (ω n) ^ (-k)
  rw [conj_ω]
  rw [_root_.inv_zpow']

theorem ω_zpow_mod_n (n : Nat) [NeZero n] (k : ℤ) : (ω n) ^ k = (ω n) ^ (k % n) := by
  conv_lhs => rw [← Int.emod_add_ediv k n]
  have h_ne : ω n ≠ 0 := ω_ne_zero n
  rw [zpow_add₀ h_ne, _root_.zpow_mul]
  have : (ω n) ^ (n : ℤ) = 1 := by exact_mod_cast (ω_pow_n n)
  rw [this]
  simp

/-- The character-twisted Laplacian L_α on ℂ^V. -/
noncomputable def laplacian : Matrix Z.V Z.V ℂ := fun u v =>
  if u = v then (Z.graph.degree u : ℂ)
  else if h : Z.graph.Adj u v then 
    - (ω n) ^ (Z.α ⟨(u, v), h⟩).val
  else 0

/-- L_α is Hermitian. -/
theorem laplacian_hermitian : (Z.laplacian).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro u v
  unfold laplacian
  by_cases huv : u = v
  · subst huv
    simp
  · by_cases hvu : Z.graph.Adj v u
    · have huv_adj : Z.graph.Adj u v := hvu.symm
      simp [huv, Ne.symm huv, hvu, huv_adj]
      let d_vu : Z.graph.Dart := ⟨(v, u), hvu⟩
      let d_uv : Z.graph.Dart := ⟨(u, v), huv_adj⟩
      change (star (ω n)) ^ (Z.α d_vu).val = (ω n) ^ (Z.α d_uv).val
      rw [conj_ω]
      rw [← zpow_natCast]
      rw [_root_.inv_zpow']
      have hpow : (ω n) ^ (-((Z.α d_vu).val : ℤ)) =
          (ω n) ^ ((Z.α d_uv).val : ℤ) := by
        have hzmod : ((-((Z.α d_vu).val : ℤ) : ℤ) : ZMod n) = Z.α d_uv := by
          have hanti := Z.antisym d_uv
          have hneg : Z.α d_vu = - Z.α d_uv := by
            calc
              Z.α d_vu = Z.α d_uv.symm := rfl
              _ = - Z.α d_uv := by exact eq_neg_of_add_eq_zero_right hanti
          rw [hneg]
          simp
        have hzmod2 : ((-((Z.α d_vu).val : ℤ) : ℤ) : ZMod n) =
            (((Z.α d_uv).val : ℤ) : ZMod n) := by
          rw [hzmod]
          simp [ZMod.natCast_zmod_val]
        have hmodeq : (-((Z.α d_vu).val : ℤ)) ≡ ((Z.α d_uv).val : ℤ)
            [ZMOD (n : ℤ)] := by
          exact (ZMod.intCast_eq_intCast_iff
            (-((Z.α d_vu).val : ℤ)) ((Z.α d_uv).val : ℤ) n).mp hzmod2
        rw [ω_zpow_mod_n n (-((Z.α d_vu).val : ℤ)),
          ω_zpow_mod_n n ((Z.α d_uv).val : ℤ), hmodeq.eq]
      rw [hpow]
      rw [zpow_natCast]
    · have huv_noadj : ¬ Z.graph.Adj u v := by
        intro h
        exact hvu h.symm
      simp [huv, Ne.symm huv, hvu, huv_noadj]

end ZnConnGraph

end ConnectionLaplacian
