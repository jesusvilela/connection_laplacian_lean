import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace ConnectionLaplacian

open Matrix BigOperators Complex

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

noncomputable def ω (n : Nat) [NeZero n] : ℂ :=
  exp (2 * Real.pi * I / n)

theorem ω_pow_n (n : Nat) [hn : NeZero n] : (ω n) ^ n = 1 := by
  unfold ω
  have h1 : (n : ℂ) * (2 * Real.pi * I / n) = 2 * Real.pi * I := by
    field_simp [hn.out]; ring
  rw [← exp_nat_mul, h1]

theorem ω_ne_zero (n : Nat) [NeZero n] : ω n ≠ 0 := by
  unfold ω; exact exp_ne_zero _

theorem conj_ω (n : Nat) [NeZero n] : star (ω n) = (ω n)⁻¹ := by
  unfold ω
  have : star (2 * Real.pi * I / n : ℂ) = -(2 * Real.pi * I / n) := by
    simp [star_div, star_mul]
    ring
  simp [RCLike.star_def, exp_conj, this, exp_neg]

theorem ω_zpow_neg (n : Nat) [NeZero n] (k : ℤ) : star ((ω n) ^ k) = (ω n) ^ (-k) := by
  rw [star_zpow₀, conj_ω, inv_zpow]

theorem ω_zpow_mod_n (n : Nat) [NeZero n] (k : ℤ) : (ω n) ^ k = (ω n) ^ (k % n) := by
  conv_lhs => rw [← Int.emod_add_ediv k n]
  have h_ne : ω n ≠ 0 := by unfold ω; exact exp_ne_zero _
  rw [zpow_add₀ h_ne, _root_.zpow_mul]
  have : (ω n) ^ (n : ℤ) = 1 := by exact_mod_cast (ω_pow_n n)
  rw [this, one_zpow, mul_one]

noncomputable def laplacian : Matrix Z.V Z.V ℂ := fun u v =>
  if u = v then (Z.graph.degree u : ℂ)
  else if h : Z.graph.Adj u v then 
    - (ω n) ^ (Z.α ⟨(u, v), h⟩).val
  else 0

theorem laplacian_hermitian : (Z.laplacian).IsHermitian := by
  ext u v
  simp only [laplacian, conjTranspose_apply, star_apply]
  by_cases h_uv : u = v
  · subst h_uv; simp
    exact of_real_re (Z.graph.degree v : ℝ)
  · simp [h_uv]
    have h_vu : v ≠ u := Ne.symm h_uv
    simp [h_vu]
    by_cases h_adj : Z.graph.Adj v u
    · have h_adj_uv := h_adj.symm
      rw [dif_pos h_adj, dif_pos h_adj_uv]
      simp
      let d_vu : Z.graph.Dart := ⟨(v, u), h_adj⟩
      let d_uv : Z.graph.Dart := ⟨(u, v), h_adj_uv⟩
      have h_anti := Z.antisym d_uv
      have h_anti2 : Z.α d_vu = - Z.α d_uv := by
        calc
          Z.α d_vu = Z.α d_uv.symm := rfl
          _ = - Z.α d_uv := eq_neg_of_add_eq_zero_left h_anti
      have h_pow_eq : (ω n) ^ (Z.α d_vu).val = (ω n) ^ (-(Z.α d_uv).val : ℤ) := by
        rw [h_anti2]
        rw [ZMod.val_neg]
        split_ifs with h_val
        · simp [h_val]
        · rw [ω_zpow_mod_n n (-(Z.α d_uv).val : ℤ)]
          simp
      rw [h_pow_eq, ← zpow_nat_cast, ω_zpow_neg n (Z.α d_uv).val]
    · have h_noadj_uv : ¬ Z.graph.Adj u v := fun h => h_adj h.symm
      rw [dif_neg h_adj, dif_neg h_noadj_uv]
      simp

end ZnConnGraph

end ConnectionLaplacian
