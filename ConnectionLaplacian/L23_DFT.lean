/-
ConnectionLaplacian/L23_DFT.lean

**Stratum L23 — Discrete Fourier Transform on Z/n.**

This file formalizes the DFT basis on ℂ^n for the cyclic group Z/n.
It proves the orthogonality of characters.
-/

import ConnectionLaplacian.L21_SectoralDecomposition
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.GeomSum

namespace ConnectionLaplacian

open Complex Matrix BigOperators

variable {n : Nat} [NeZero n]

/-- The k-th additive character of ZMod n. -/
noncomputable def znChar (k : ZMod n) : ZMod n → ℂ := fun x =>
  (ZnConnGraph.ω n) ^ (k.val * x.val : ℤ)

lemma znChar_eq_ω_zpow (k x : ZMod n) : znChar k x = (ZnConnGraph.ω n) ^ (k.val * x.val : ℤ) := rfl

private noncomputable def zmodFinEquiv (n : Nat) [NeZero n] : ZMod n ≃ Fin n where
  toFun x := ⟨x.val, ZMod.val_lt x⟩
  invFun i := (i : ZMod n)
  left_inv x := by
    apply ZMod.val_injective (n := n)
    simp
  right_inv i := by
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.is_lt]

lemma znChar_add (k : ZMod n) (x y : ZMod n) : 
    znChar k (x + y) = znChar k x * znChar k y := by
  unfold znChar
  have hzmod : (((k.val * (x + y).val : ℤ) : ZMod n)) =
      (((k.val * x.val + k.val * y.val : ℤ) : ZMod n)) := by
    calc
      (((k.val * (x + y).val : ℤ) : ZMod n)) = (k.val : ZMod n) * (x + y) := by
        simp [ZMod.natCast_zmod_val]
      _ = (k.val : ZMod n) * x + (k.val : ZMod n) * y := by rw [mul_add]
      _ = (((k.val * x.val + k.val * y.val : ℤ) : ZMod n)) := by
        simp [ZMod.natCast_zmod_val, mul_add]
  have hmodeq : (k.val * (x + y).val : ℤ) ≡ (k.val * x.val + k.val * y.val : ℤ) [ZMOD (n : ℤ)] := by
    exact (ZMod.intCast_eq_intCast_iff
      (k.val * (x + y).val : ℤ) (k.val * x.val + k.val * y.val : ℤ) n).mp hzmod
  calc
    (ZnConnGraph.ω n) ^ (k.val * (x + y).val : ℤ)
        = (ZnConnGraph.ω n) ^ (k.val * x.val + k.val * y.val : ℤ) := by
            rw [ZnConnGraph.ω_zpow_mod_n n (k.val * (x + y).val : ℤ),
              ZnConnGraph.ω_zpow_mod_n n (k.val * x.val + k.val * y.val : ℤ), hmodeq.eq]
    _ = (ZnConnGraph.ω n) ^ (k.val * x.val : ℤ) * (ZnConnGraph.ω n) ^ (k.val * y.val : ℤ) := by
          rw [zpow_add₀ (ZnConnGraph.ω_ne_zero n)]

/-- Helper lemma: Sum of powers of a root of unity over ZMod n. -/
theorem sum_ω_pow_eq_zero {k : ℤ} (hk : ¬ (n : ℤ) ∣ k) :
    ∑ x : ZMod n, (ZnConnGraph.ω n) ^ (k * x.val) = 0 := by
  let e : ZMod n ≃ Fin n := zmodFinEquiv n
  have hsum :
      (∑ x : ZMod n, (ZnConnGraph.ω n) ^ (k * x.val)) =
      ∑ i : Fin n, (ZnConnGraph.ω n) ^ (k * i.val : ℤ) := by
    refine Fintype.sum_equiv e _ _ ?_
    intro x
    simp [e, zmodFinEquiv]
  rw [hsum]
  simpa [hk] using (sum_fin_omega_mul (n := n) k)

/-- Characters are orthogonal. -/
theorem znChar_orthogonality (k1 k2 : ZMod n) :
    ∑ x : ZMod n, (znChar k1 x) * star (znChar k2 x) = 
    if k1 = k2 then (n : ℂ) else 0 := by
  by_cases hEq : k1 = k2
  · subst hEq
    have hterm : ∀ x : ZMod n, (znChar k1 x) * star (znChar k1 x) = 1 := by
      intro x
      unfold znChar
      rw [ZnConnGraph.ω_zpow_neg]
      rw [← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
      simp
    rw [if_pos rfl]
    change ∑ x in Finset.univ, (znChar k1 x) * star (znChar k1 x) = (n : ℂ)
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    simp
  · have hneq_dvd : ¬ (n : ℤ) ∣ ((k1.val : ℤ) - k2.val) := by
      intro hdiv
      let i : Fin n := ⟨k2.val, ZMod.val_lt k2⟩
      let j : Fin n := ⟨k1.val, ZMod.val_lt k1⟩
      have hij : i = j := (fin_sub_dvd_iff_eq (n := n) i j).1 hdiv
      apply hEq
      apply ZMod.val_injective (n := n)
      simpa [i, j] using congrArg Fin.val hij.symm
    have hrewrite :
        (∑ x : ZMod n, (znChar k1 x) * star (znChar k2 x)) =
        ∑ x : ZMod n, (ZnConnGraph.ω n) ^ (((k1.val : ℤ) - k2.val) * x.val) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      unfold znChar
      rw [ZnConnGraph.ω_zpow_neg]
      calc
        (ZnConnGraph.ω n) ^ (k1.val * x.val : ℤ) * (ZnConnGraph.ω n) ^ (-(k2.val * x.val : ℤ))
            = (ZnConnGraph.ω n) ^ ((k1.val * x.val : ℤ) + (-(k2.val * x.val : ℤ))) := by
                rw [← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
        _ = (ZnConnGraph.ω n) ^ (((k1.val : ℤ) - k2.val) * x.val) := by
              congr 1
              ring
    rw [if_neg hEq, hrewrite]
    exact sum_ω_pow_eq_zero hneq_dvd

/-- The DFT matrix. -/
noncomputable def dftMatrix (n : Nat) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ := fun k x =>
  znChar k x

/-- The inverse DFT matrix (unnormalized). -/
noncomputable def dftInverse (n : Nat) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ := fun x k =>
  star (znChar k x)

theorem dft_mul_inv : (dftMatrix n) * (dftInverse n) = (n : ℂ) • 1 := by
  ext k j
  simpa [dftMatrix, dftInverse, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    using (znChar_orthogonality (n := n) k j)

end ConnectionLaplacian
