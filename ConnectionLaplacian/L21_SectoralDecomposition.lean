/-
ConnectionLaplacian/L21_SectoralDecomposition.lean

**Stratum L21 — Sectoral Decomposition.**

This file proves that the Z/n connection Laplacian on the n-fold cover
decomposes into character-twisted scalar Laplacians on the base graph.
-/

import ConnectionLaplacian.L20_ZModConnection
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional

namespace ConnectionLaplacian

open Matrix BigOperators Complex
open scoped Kronecker

variable {n : Nat} [NeZero n] (Z : ZnConnGraph n)

/-- The k-th character-twisted scalar Laplacian `L_k`. -/
noncomputable def sectoralLaplacian (k : Fin n) : Matrix Z.V Z.V ℂ := fun u v =>
  if u = v then (Z.graph.degree u : ℂ)
  else if h : Z.graph.Adj u v then
    - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h⟩).val)
  else 0

/-- The `n`-fold cover Laplacian `L_cover`. -/
noncomputable def coverLaplacian : Matrix (Z.V × Fin n) (Z.V × Fin n) ℂ := fun ⟨u, i⟩ ⟨v, j⟩ =>
  if u = v then
    if i = j then (Z.graph.degree u : ℂ) else 0
  else if h : Z.graph.Adj u v then
    if (i : ZMod n) = (j : ZMod n) + Z.α ⟨(u, v), h⟩ then -1 else 0
  else 0

lemma omega_zpow_eq_one_iff_dvd (m : ℤ) :
    (ZnConnGraph.ω n) ^ m = 1 ↔ (n : ℤ) ∣ m := by
  constructor
  · intro h
    have hexp : Complex.exp ((m : ℂ) * (2 * Real.pi * I / n)) = 1 := by
      simpa [ZnConnGraph.ω, Complex.exp_int_mul, mul_comm, mul_left_comm, mul_assoc] using h
    rw [Complex.exp_eq_one_iff] at hexp
    rcases hexp with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hcancel : ((m : ℂ) / n) = k := by
      apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hk
    have hmul := congrArg (fun z : ℂ => z * n) hcancel
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    field_simp [hn0] at hmul
    simpa [mul_comm] using (show m = k * (n : ℤ) from by exact_mod_cast hmul)
  · rintro ⟨k, rfl⟩
    have : (ZnConnGraph.ω n) ^ (k * (n : ℤ)) = 1 := by
      rw [show (ZnConnGraph.ω n) ^ (k * (n : ℤ)) = ((ZnConnGraph.ω n) ^ (n : ℤ)) ^ k by
        exact _root_.zpow_mul' (ZnConnGraph.ω n) k (n : ℤ)]
      have hω : (ZnConnGraph.ω n) ^ (n : ℤ) = 1 := by
        exact_mod_cast (ZnConnGraph.ω_pow_n n)
      rw [hω]
      simp
    simpa [mul_comm] using this

lemma fin_sub_dvd_iff_eq (i j : Fin n) : ((n : ℤ) ∣ ((j.val : ℤ) - i.val)) ↔ i = j := by
  constructor
  · rintro ⟨k, hk⟩
    apply Fin.ext
    have hi_lt : (i.val : ℤ) < n := by exact_mod_cast i.is_lt
    have hj_lt : (j.val : ℤ) < n := by exact_mod_cast j.is_lt
    have hlt : ((j.val : ℤ) - i.val) < n := by omega
    have hgt : -((n : ℤ)) < ((j.val : ℤ) - i.val) := by omega
    have hk_nonneg : 0 ≤ k := by
      by_contra hkneg
      have hmul_le : (n : ℤ) * k ≤ -(n : ℤ) := by nlinarith [Nat.pos_of_ne_zero (NeZero.ne n)]
      linarith [hk, hgt]
    have hk_nonpos : k ≤ 0 := by
      by_contra hkpos
      have hmul_ge : n ≤ (n : ℤ) * k := by nlinarith [Nat.pos_of_ne_zero (NeZero.ne n)]
      linarith [hk, hlt]
    have hk0 : k = 0 := by linarith
    have hdiff : ((j.val : ℤ) - i.val) = 0 := by simp [hk, hk0]
    linarith
  · intro h
    subst h
    exact ⟨0, by simp⟩

lemma sum_fin_omega_mul (m : ℤ) :
    ∑ k : Fin n, (ZnConnGraph.ω n) ^ (m * k.val : ℤ) =
      if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  by_cases hm : (n : ℤ) ∣ m
  · rcases hm with ⟨c, rfl⟩
    have hsum :
        ∑ k : Fin n, (ZnConnGraph.ω n) ^ (((n : ℤ) * c) * k.val) =
          ∑ k in Finset.range n, (ZnConnGraph.ω n) ^ (((n : ℤ) * c) * k : ℤ) := by
      simpa using (Fin.sum_univ_eq_sum_range
        (f := fun k => (ZnConnGraph.ω n) ^ (((n : ℤ) * c) * k : ℤ)) n)
    have hm' : (n : ℤ) ∣ (n : ℤ) * c := dvd_mul_of_dvd_left (dvd_refl (n : ℤ)) c
    calc
      ∑ k : Fin n, (ZnConnGraph.ω n) ^ (((n : ℤ) * c) * k.val)
          = ∑ k in Finset.range n, (ZnConnGraph.ω n) ^ (((n : ℤ) * c) * k : ℤ) := hsum
      _ = ∑ k in Finset.range n, (1 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hterm : (n : ℤ) ∣ ((n : ℤ) * c) * k := by
              refine ⟨c * k, by ring⟩
            rw [(omega_zpow_eq_one_iff_dvd (n := n) _).2 hterm]
      _ = (n : ℂ) := by simp
      _ = if (n : ℤ) ∣ (n : ℤ) * c then (n : ℂ) else 0 := by simp [hm']
  · let r : ℂ := (ZnConnGraph.ω n) ^ m
    have hr_ne : r ≠ 1 := by
      intro hr
      exact hm ((omega_zpow_eq_one_iff_dvd (n := n) m).1 hr)
    have hrn : r ^ n = 1 := by
      rw [← zpow_natCast]
      dsimp [r]
      rw [show ((ZnConnGraph.ω n) ^ m) ^ (n : ℤ) = (ZnConnGraph.ω n) ^ (m * (n : ℤ)) by
        symm
        exact zpow_mul _ m (n : ℤ)]
      rw [show (ZnConnGraph.ω n) ^ (m * (n : ℤ)) = ((ZnConnGraph.ω n) ^ (n : ℤ)) ^ m by
        exact _root_.zpow_mul' (ZnConnGraph.ω n) m (n : ℤ)]
      have hω : (ZnConnGraph.ω n) ^ ((n : ℤ)) = 1 := by
        exact_mod_cast (ZnConnGraph.ω_pow_n n)
      rw [hω]
      simp
    have hsum :
        ∑ k : Fin n, (ZnConnGraph.ω n) ^ (m * k.val : ℤ) =
          ∑ k in Finset.range n, (ZnConnGraph.ω n) ^ (m * k : ℤ) := by
      simpa using (Fin.sum_univ_eq_sum_range
        (f := fun k => (ZnConnGraph.ω n) ^ (m * k : ℤ)) n)
    rw [hsum, if_neg hm]
    calc
      ∑ x ∈ Finset.range n, (ZnConnGraph.ω n) ^ (m * x : ℤ)
          = ∑ x ∈ Finset.range n, r ^ x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              dsimp [r]
              rw [← zpow_natCast]
              simpa [mul_comm] using (zpow_mul (ZnConnGraph.ω n) m (x : ℤ))
      _ = 0 := by
            rw [geom_sum_eq hr_ne, hrn]
            simp [hr_ne]

private noncomputable def fourierNeg (n : Nat) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => (ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ)))

private noncomputable def fourierPos (n : Nat) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  fun k j => (ZnConnGraph.ω n) ^ ((k.val * j.val : ℤ))

private noncomputable def Pmat (Z : ZnConnGraph n) : Matrix (Z.V × Fin n) (Z.V × Fin n) ℂ :=
  (1 : Matrix Z.V Z.V ℂ) ⊗ₖ fourierNeg n

private noncomputable def PmatInv (Z : ZnConnGraph n) : Matrix (Z.V × Fin n) (Z.V × Fin n) ℂ :=
  (1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ fourierPos n)

lemma fourier_mul_fourier :
    fourierNeg n * fourierPos n = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  calc
    ∑ k : Fin n, fourierNeg n i k * fourierPos n k j
      = ∑ k : Fin n, (ZnConnGraph.ω n) ^ ((((j.val : ℤ) - i.val) * k.val : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          dsimp [fourierNeg, fourierPos]
          rw [← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
          congr 1
          ring
    _ = if (n : ℤ) ∣ ((j.val : ℤ) - i.val) then (n : ℂ) else 0 :=
          sum_fin_omega_mul (n := n) (((j.val : ℤ) - i.val))
    _ = if i = j then (n : ℂ) else 0 := by
          by_cases hij : i = j
          · simp [hij]
          · simp [hij, fin_sub_dvd_iff_eq (n := n) i j]
    _ = (n : ℂ) * (if i = j then 1 else 0) := by
          split_ifs <;> simp

lemma Pmat_mul_PmatInv (Z : ZnConnGraph n) : Pmat Z * PmatInv Z = 1 := by
  dsimp [Pmat, PmatInv]
  rw [Matrix.mul_smul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, fourier_mul_fourier,
    Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp [hn0]

lemma Pmat_det_ne_zero (Z : ZnConnGraph n) : (Pmat Z).det ≠ 0 := by
  intro h
  have hd := congrArg Matrix.det (Pmat_mul_PmatInv (n := n) Z)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hd
  exact zero_ne_one hd

lemma Pmat_apply (Z : ZnConnGraph n) (u v : Z.V) (i k : Fin n) :
    Pmat Z (u, i) (v, k) = if u = v then (ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ))) else 0 := by
  simp [Pmat, fourierNeg, Matrix.kroneckerMap_apply, Matrix.one_apply]

lemma phase_shift {a : ZMod n} (i l k : Fin n)
    (h : (i : ZMod n) = (l : ZMod n) + a) :
    (ZnConnGraph.ω n) ^ (-((k.val * l.val : ℤ))) =
      (ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ)) + (k.val * a.val : ℤ)) := by
  have hzmod : (((-((k.val * l.val : ℤ)) : ℤ) : ZMod n)) =
      (((-((k.val * i.val : ℤ)) + (k.val * a.val : ℤ) : ℤ) : ZMod n)) := by
    simpa [ZMod.natCast_zmod_val] using (show -((k.val : ZMod n) * l.val) =
        -((k.val : ZMod n) * i.val) + (k.val : ZMod n) * a from by
      rw [h]
      ring)
  have hmodeq : (-((k.val * l.val : ℤ))) ≡ (-((k.val * i.val : ℤ)) + (k.val * a.val : ℤ))
      [ZMOD (n : ℤ)] := by
    exact (ZMod.intCast_eq_intCast_iff
      (-((k.val * l.val : ℤ))) (-((k.val * i.val : ℤ)) + (k.val * a.val : ℤ)) n).mp hzmod
  rw [ZnConnGraph.ω_zpow_mod_n n (-((k.val * l.val : ℤ))),
    ZnConnGraph.ω_zpow_mod_n n (-((k.val * i.val : ℤ)) + (k.val * a.val : ℤ)), hmodeq.eq]

lemma Pmat_mul_block_apply (Z : ZnConnGraph n) (u v : Z.V) (i k : Fin n) :
    (Pmat Z * Matrix.blockDiagonal (fun l : Fin n => sectoralLaplacian Z l)) (u, i) (v, k) =
      (ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ))) * sectoralLaplacian Z k u v := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single k]
    · rw [Pmat_apply, if_pos rfl, Matrix.blockDiagonal_apply_eq]
    · intro l _ hl
      rw [Pmat_apply, if_pos rfl, Matrix.blockDiagonal_apply_ne _ u v hl, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro l _
    rw [Pmat_apply, if_neg hw.symm, zero_mul]
  · intro hu
    exact absurd (Finset.mem_univ u) hu

lemma cover_mul_P_apply (Z : ZnConnGraph n) (u v : Z.V) (i k : Fin n) :
    ((coverLaplacian Z) * Pmat Z) (u, i) (v, k) =
      (ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ))) * sectoralLaplacian Z k u v := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v]
  · by_cases huv : u = v
    · subst huv
      rw [Finset.sum_eq_single i]
      · simp [coverLaplacian, sectoralLaplacian, Pmat_apply,
          mul_comm, mul_left_comm, mul_assoc]
      · intro l _ hli
        have hil : i ≠ l := by simpa using hli.symm
        simp [coverLaplacian, Pmat_apply, hil]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · by_cases hadj : Z.graph.Adj u v
      · let d : Z.graph.Dart := ⟨(u, v), hadj⟩
        let l0 : Fin n := ⟨(((i : ZMod n) - Z.α d).val), by
          exact_mod_cast (ZMod.val_lt (((i : ZMod n) - Z.α d)))⟩
        have hl0 : (i : ZMod n) = (l0 : ZMod n) + Z.α d := by
          dsimp [l0]
          rw [ZMod.natCast_zmod_val]
          abel
        have hl0' : (i : ZMod n) = (l0 : ZMod n) + Z.α ⟨(u, v), hadj⟩ := by
          simpa [d] using hl0
        rw [Finset.sum_eq_single l0]
        · have hcover : coverLaplacian Z (u, i) (v, l0) = -1 := by
            change (if u = v then if i = l0 then (Z.graph.degree u : ℂ) else 0
              else if h : Z.graph.Adj u v then
                if (i : ZMod n) = (l0 : ZMod n) + Z.α ⟨(u, v), h⟩ then -1 else 0
              else 0) = -1
            by_cases huv' : u = v
            · exact (huv huv').elim
            · rw [if_neg huv']
              by_cases hadj' : Z.graph.Adj u v
              · rw [dif_pos hadj']
                have hl0'' : (i : ZMod n) = (l0 : ZMod n) + Z.α ⟨(u, v), hadj'⟩ := by
                  simpa using hl0'
                rw [if_pos hl0'']
              · exact (hadj' hadj).elim
          have hsector : -(ZnConnGraph.ω n) ^ ((k.val * (Z.α d).val : ℤ)) =
              sectoralLaplacian Z k u v := by
            rw [sectoralLaplacian, if_neg huv, dif_pos hadj]
            simpa [d] using congrArg Neg.neg
              (zpow_natCast (ZnConnGraph.ω n) (k.val * (Z.α ⟨(u, v), hadj⟩).val))
          rw [hcover, Pmat_apply, if_pos rfl]
          calc
            (-1 : ℂ) * (ZnConnGraph.ω n) ^ (-((k.val * l0.val : ℤ)))
                = -((ZnConnGraph.ω n) ^ (-((k.val * l0.val : ℤ)))) := by ring
            _ = -((ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ)) + (k.val * (Z.α d).val : ℤ))) := by
                rw [phase_shift (n := n) (a := Z.α d) i l0 k hl0]
            _ = -((ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ))) *
                  (ZnConnGraph.ω n) ^ ((k.val * (Z.α d).val : ℤ))) := by
                rw [← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
            _ = (ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ))) *
                  (-(ZnConnGraph.ω n) ^ ((k.val * (Z.α d).val : ℤ))) := by ring
            _ = (ZnConnGraph.ω n) ^ (-((k.val * i.val : ℤ))) * sectoralLaplacian Z k u v := by
                rw [hsector]
        · intro l _ hl
          have hneq : ¬ (i : ZMod n) = (l : ZMod n) + Z.α d := by
            intro hEq
            have hcast : (l : ZMod n) = (l0 : ZMod n) := by
              exact add_right_cancel (hEq.symm.trans hl0)
            have hval := congrArg ZMod.val hcast
            apply hl
            apply Fin.ext
            simpa [ZMod.val_natCast, Nat.mod_eq_of_lt l.is_lt, Nat.mod_eq_of_lt l0.is_lt] using hval
          have hneq' : ¬ (i : ZMod n) = (l : ZMod n) + Z.α ⟨(u, v), hadj⟩ := by
            simpa [d] using hneq
          simp [coverLaplacian, huv, hadj, hneq', Pmat_apply]
        · intro hl
          exact absurd (Finset.mem_univ l0) hl
      · rw [sectoralLaplacian, if_neg huv, dif_neg hadj]
        simp [coverLaplacian, huv, hadj, Pmat_apply]
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro l _
    rw [Pmat_apply, if_neg hw, mul_zero]
  · intro hv
    exact absurd (Finset.mem_univ v) hv

lemma intertwining (Z : ZnConnGraph n) :
    (coverLaplacian Z) * Pmat Z = Pmat Z * Matrix.blockDiagonal (fun l : Fin n => sectoralLaplacian Z l) := by
  ext x y
  rcases x with ⟨u, i⟩
  rcases y with ⟨v, k⟩
  rw [cover_mul_P_apply, Pmat_mul_block_apply]

/-- The total connection Laplacian on the `n`-fold cover decomposes into
    character-twisted scalar Laplacians on the base graph. -/
theorem laplacian_sectoral_decomposition :
    ∃ (P : Matrix (Z.V × Fin n) (Z.V × Fin n) ℂ),
      P.det ≠ 0 ∧
      P⁻¹ * (coverLaplacian Z) * P = Matrix.blockDiagonal (fun (k : Fin n) => sectoralLaplacian Z k) := by
  refine ⟨Pmat Z, Pmat_det_ne_zero (n := n) Z, ?_⟩
  have hunit : IsUnit (Pmat Z).det := isUnit_iff_ne_zero.mpr (Pmat_det_ne_zero (n := n) Z)
  calc
    (Pmat Z)⁻¹ * (coverLaplacian Z) * Pmat Z =
        (Pmat Z)⁻¹ * ((coverLaplacian Z) * Pmat Z) := by
          rw [← Matrix.mul_assoc]
    _ = (Pmat Z)⁻¹ * (Pmat Z * Matrix.blockDiagonal (fun k : Fin n => sectoralLaplacian Z k)) := by
          rw [intertwining (n := n) Z]
    _ = Matrix.blockDiagonal (fun k : Fin n => sectoralLaplacian Z k) := by
          simpa using Matrix.nonsing_inv_mul_cancel_left
            (A := Pmat Z)
            (B := Matrix.blockDiagonal (fun k : Fin n => sectoralLaplacian Z k))
            hunit

end ConnectionLaplacian
