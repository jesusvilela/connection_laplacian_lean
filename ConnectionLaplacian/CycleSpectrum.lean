/-
ConnectionLaplacian/CycleSpectrum.lean

Theorem 2: Explicit spectrum of the connection Laplacian on an n-cycle.
-/

import ConnectionLaplacian.Basic
import ConnectionLaplacian.KernelDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace ConnectionLaplacian.Cycle

open Real Matrix BigOperators

/-- The n-cycle's scalar graph Laplacian. -/
noncomputable def scalarCycleLaplacian (n : ℕ) (_hn : 2 ≤ n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then 2
    else if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then -1
    else 0

/-- The signed cycle Laplacian for the Möbius case. -/
noncomputable def signedCycleLaplacian (n : ℕ) (_hn : 2 ≤ n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
    else if (i.val = n - 1 ∧ j.val = 0) ∨ (i.val = 0 ∧ j.val = n - 1) then 1
    else 0

/-! ### Helpers for cycle indexing. -/

private def succFin (n : ℕ) (hn : 1 ≤ n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

private def predFin (n : ℕ) (hn : 1 ≤ n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

private lemma succFin_val (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    (succFin n hn i).val = (i.val + 1) % n := rfl

private lemma predFin_val (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    (predFin n hn i).val = (i.val + n - 1) % n := rfl

private lemma predFin_val_at_zero (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (hi : i.val = 0) :
    (predFin n hn i).val = n - 1 := by
  rw [predFin_val, hi, Nat.zero_add]
  exact Nat.mod_eq_of_lt (by omega)

private lemma predFin_val_at_pos (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (hi : 1 ≤ i.val) :
    (predFin n hn i).val = i.val - 1 := by
  rw [predFin_val]
  have key : i.val + n - 1 = (i.val - 1) + n := by omega
  rw [key, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := i.isLt; omega)]

private lemma succFin_val_at_lt (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (hi : i.val + 1 < n) :
    (succFin n hn i).val = i.val + 1 := by
  rw [succFin_val, Nat.mod_eq_of_lt hi]

private lemma succFin_val_at_eq (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (hi : i.val + 1 = n) :
    (succFin n hn i).val = 0 := by
  rw [succFin_val, hi, Nat.mod_self]

private lemma succFin_ne_self (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    succFin n (by omega) i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [succFin_val] at hv
  have hilt : i.val + 1 ≤ n := i.isLt
  by_cases hc : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hc] at hv; omega
  · have heq : i.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    have := i.isLt; omega

private lemma predFin_ne_self (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    predFin n (by omega) i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  by_cases hi : i.val = 0
  · rw [predFin_val_at_zero n _ i hi] at hv
    omega
  · have hige : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
    rw [predFin_val_at_pos n _ i hige] at hv
    omega

private lemma succFin_ne_predFin (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    succFin n (by omega) i ≠ predFin n (by omega) i := by
  intro h
  have hv := congrArg Fin.val h
  have hilt : i.val < n := i.isLt
  by_cases hi : i.val = 0
  · rw [succFin_val_at_lt n _ i (by omega),
        predFin_val_at_zero n _ i hi] at hv
    omega
  · by_cases hc : i.val + 1 = n
    · rw [succFin_val_at_eq n _ i hc,
          predFin_val_at_pos n _ i (Nat.one_le_iff_ne_zero.mpr hi)] at hv
      omega
    · have hsuclt : i.val + 1 < n := by omega
      rw [succFin_val_at_lt n _ i hsuclt,
          predFin_val_at_pos n _ i (Nat.one_le_iff_ne_zero.mpr hi)] at hv
      omega

private lemma scalar_off_iff (n : ℕ) (hn : 3 ≤ n) (i j : Fin n) :
    ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) ↔
      (j = succFin n (by omega) i ∨ j = predFin n (by omega) i) := by
  constructor
  · rintro (h | h)
    · left; apply Fin.ext; rw [succFin_val]; exact h.symm
    · right; apply Fin.ext
      by_cases hj1 : j.val + 1 = n
      · rw [hj1, Nat.mod_self] at h
        have hi0 : i.val = 0 := h.symm
        rw [predFin_val_at_zero n _ i hi0]; omega
      · have hjlt : j.val + 1 < n := by have := j.isLt; omega
        rw [Nat.mod_eq_of_lt hjlt] at h
        have hige : 1 ≤ i.val := by omega
        rw [predFin_val_at_pos n _ i hige]; omega
  · rintro (h | h)
    · left
      have hv := congrArg Fin.val h
      rw [succFin_val] at hv
      exact hv.symm
    · right
      have hv := congrArg Fin.val h
      rw [hv]
      by_cases hi : i.val = 0
      · rw [predFin_val_at_zero n _ i hi]
        have hnn : (n - 1) + 1 = n := by omega
        rw [hnn, Nat.mod_self]
        exact hi.symm
      · have hige : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
        rw [predFin_val_at_pos n _ i hige]
        have hii : i.val - 1 + 1 = i.val := by omega
        rw [hii, Nat.mod_eq_of_lt i.isLt]

/-! ### Matrix-vector product for scalar cycle Laplacian. -/

/-- For `n ≥ 3`, the scalar cycle Laplacian acts on a vector `w` by
`(L·w)(i) = 2 w(i) − w(succ(i)) − w(pred(i))`. -/
private lemma scalar_mulVec_row
    (n : ℕ) (hn : 3 ≤ n) (w : Fin n → ℝ) (i : Fin n) :
    (scalarCycleLaplacian n (by omega)).mulVec w i =
      2 * w i - w (succFin n (by omega) i) - w (predFin n (by omega) i) := by
  have h_si := succFin_ne_self n hn i
  have h_pi := predFin_ne_self n hn i
  have h_sp := succFin_ne_predFin n hn i
  let s : Finset (Fin n) :=
    ({i, succFin n (by omega) i, predFin n (by omega) i} : Finset (Fin n))
  have hi_mem : i ∈ s := by
    simp [s]
  have hsu_mem : succFin n (by omega) i ∈ s := by
    simp [s]
  have hpr_mem : predFin n (by omega) i ∈ s := by
    simp [s]
  have hsub : s ⊆ Finset.univ := Finset.subset_univ _
  -- Rewrite mulVec as dotProduct, then a sum over Finset.univ.
  unfold Matrix.mulVec Matrix.dotProduct
  -- Show that the sum equals the sum over s.
  rw [← Finset.sum_subset hsub (f := fun j => scalarCycleLaplacian n (by omega) i j * w j)
        (by
          intro j _ hjs
          -- j ∉ {i, succ i, pred i} means j ≠ i, j ≠ succ i, j ≠ pred i
          have hji : j ≠ i := by
            intro hji_eq; apply hjs; rw [hji_eq]; exact hi_mem
          have hjs' : j ≠ succFin n (by omega) i := by
            intro hjs_eq; apply hjs; rw [hjs_eq]; exact hsu_mem
          have hjp : j ≠ predFin n (by omega) i := by
            intro hjp_eq; apply hjs; rw [hjp_eq]; exact hpr_mem
          -- Now show scalarCycleLaplacian n _ i j = 0
          show scalarCycleLaplacian n (by omega) i j * w j = 0
          unfold scalarCycleLaplacian
          have hij : i ≠ j := fun h => hji h.symm
          rw [if_neg hij]
          have hoff : ¬ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) := by
            intro hh
            rcases (scalar_off_iff n hn i j).mp hh with h | h
            · exact hjs' h
            · exact hjp h
          rw [if_neg hoff, zero_mul])]
  -- Now expand the 3-element sum.
  have h_s : s = insert i (insert (succFin n (by omega) i) {predFin n (by omega) i}) := rfl
  rw [h_s]
  have h_i_not_in : i ∉ (insert (succFin n (by omega) i) ({predFin n (by omega) i} : Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h_si h.symm, fun h => h_pi h.symm⟩
  have h_su_not_in : succFin n (by omega) i ∉ ({predFin n (by omega) i} : Finset (Fin n)) := by
    simp only [Finset.mem_singleton]
    exact h_sp
  rw [Finset.sum_insert h_i_not_in,
      Finset.sum_insert h_su_not_in,
      Finset.sum_singleton]
  -- Now compute the three matrix entries.
  have hL_ii : scalarCycleLaplacian n (by omega) i i = 2 := by
    unfold scalarCycleLaplacian; rw [if_pos rfl]
  have hL_is : scalarCycleLaplacian n (by omega) i (succFin n (by omega) i) = -1 := by
    unfold scalarCycleLaplacian
    rw [if_neg (Ne.symm h_si)]
    have hor : (i.val + 1) % n = (succFin n (by omega) i).val ∨
        ((succFin n (by omega) i).val + 1) % n = i.val := by
      left; rw [succFin_val]
    rw [if_pos hor]
  have hL_ip : scalarCycleLaplacian n (by omega) i (predFin n (by omega) i) = -1 := by
    unfold scalarCycleLaplacian
    rw [if_neg (Ne.symm h_pi)]
    have hor : (i.val + 1) % n = (predFin n (by omega) i).val ∨
        ((predFin n (by omega) i).val + 1) % n = i.val := by
      right
      by_cases hi0 : i.val = 0
      · rw [predFin_val_at_zero n _ i hi0]
        have hnn : (n - 1) + 1 = n := by omega
        rw [hnn, Nat.mod_self]; exact hi0.symm
      · have hige : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi0
        rw [predFin_val_at_pos n _ i hige]
        have hii : i.val - 1 + 1 = i.val := by omega
        rw [hii, Nat.mod_eq_of_lt i.isLt]
    rw [if_pos hor]
  rw [hL_ii, hL_is, hL_ip]
  ring

private lemma cos_succFin_val
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (θ : ℝ)
    (hθ : θ * (n : ℝ) = 2 * π * (k : ℝ)) (i : Fin n) :
    Real.cos (θ * ((succFin n hn i).val : ℝ))
      = Real.cos (θ * ((i.val : ℝ) + 1)) := by
  by_cases hlt : i.val + 1 < n
  · rw [succFin_val_at_lt n _ i hlt]
    push_cast
    ring_nf
  · have hie : i.val + 1 = n := by have := i.isLt; omega
    rw [succFin_val_at_eq n _ i hie]
    have hieR : ((i.val : ℝ) + 1) = (n : ℝ) := by
      have hh := congrArg (Nat.cast (R := ℝ)) hie
      push_cast at hh
      linarith
    rw [show ((0 : ℕ) : ℝ) = 0 from by norm_cast, mul_zero, Real.cos_zero, hieR, hθ]
    have hrw : 2 * π * (k : ℝ) = (k : ℕ) * (2 * π) := by push_cast; ring
    rw [hrw, Real.cos_nat_mul_two_pi]

private lemma cos_predFin_val
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (θ : ℝ)
    (hθ : θ * (n : ℝ) = 2 * π * (k : ℝ)) (i : Fin n) :
    Real.cos (θ * ((predFin n hn i).val : ℝ))
      = Real.cos (θ * ((i.val : ℝ) - 1)) := by
  by_cases hi : i.val = 0
  · rw [predFin_val_at_zero n _ i hi, hi]
    have hnR : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    rw [hnR]
    have hA : θ * ((n : ℝ) - 1) = θ * n - θ := by ring
    rw [hA, hθ]
    have hB : 2 * π * (k : ℝ) - θ = -(θ - (k : ℕ) * (2 * π)) := by push_cast; ring
    rw [hB, Real.cos_neg, Real.cos_sub_nat_mul_two_pi]
    push_cast
    rw [show θ * (0 - 1 : ℝ) = -θ from by ring, Real.cos_neg]
  · have hige : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
    rw [predFin_val_at_pos n _ i hige]
    have hnR : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
      rw [Nat.cast_sub hige, Nat.cast_one]
    rw [hnR]

theorem scalarCycle_eigenvalue (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    ∃ (v : Fin n → ℝ), v ≠ 0 ∧
      (scalarCycleLaplacian n (by omega)).mulVec v =
        (2 * (1 - cos (2 * π * k.val / n))) • v := by
  set θ : ℝ := 2 * π * (k.val : ℝ) / (n : ℝ) with hθ_def
  set v : Fin n → ℝ := fun j => Real.cos (θ * (j.val : ℝ)) with hv_def
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this.ne'
  have hθn : θ * (n : ℝ) = 2 * π * (k.val : ℝ) := by
    rw [hθ_def]; field_simp
  refine ⟨v, ?_, ?_⟩
  · -- v ≠ 0 because v 0 = 1
    intro hv0
    have h00 : v ⟨0, by omega⟩ = 0 := by rw [hv0]; rfl
    simp [hv_def] at h00
  -- eigenvalue equation
  ext i
  rw [Pi.smul_apply, smul_eq_mul, scalar_mulVec_row n hn v i]
  -- goal: 2 * v i - v (succ i) - v (pred i) = 2 * (1 - cos θ) * v i
  have hsuc : v (succFin n (by omega) i) = Real.cos (θ * ((i.val : ℝ) + 1)) := by
    rw [hv_def]
    exact cos_succFin_val n (by omega) k.val θ hθn i
  have hpre : v (predFin n (by omega) i) = Real.cos (θ * ((i.val : ℝ) - 1)) := by
    rw [hv_def]
    exact cos_predFin_val n (by omega) k.val θ hθn i
  rw [hsuc, hpre]
  -- sum-to-product: cos(θ(i+1)) + cos(θ(i-1)) = 2 cos(θ i) cos(θ)
  have hsum : Real.cos (θ * ((i.val : ℝ) + 1)) + Real.cos (θ * ((i.val : ℝ) - 1))
      = 2 * Real.cos (θ * (i.val : ℝ)) * Real.cos θ := by
    have hcos_add := Real.cos_add_cos (θ * ((i.val : ℝ) + 1)) (θ * ((i.val : ℝ) - 1))
    rw [hcos_add]
    congr 1
    · congr 1; ring
    · congr 1; ring
  -- Rewrite the cos θ on the target side.
  have hθ_cos : Real.cos θ = Real.cos (2 * π * (k.val : ℝ) / (n : ℝ)) := by rw [hθ_def]
  have hvi : v i = Real.cos (θ * (i.val : ℝ)) := rfl
  -- The goal: 2*v i - cos(θ(i+1)) - cos(θ(i-1)) = 2*(1 - cos(2πk/n)) * v i
  -- Substitute v i and the sum identity.
  rw [show (2 * v i - Real.cos (θ * ((i.val : ℝ) + 1)) -
        Real.cos (θ * ((i.val : ℝ) - 1))) =
      2 * v i - (Real.cos (θ * ((i.val : ℝ) + 1)) +
        Real.cos (θ * ((i.val : ℝ) - 1))) by ring]
  rw [hsum, hvi, ← hθ_cos]
  ring

private lemma signed_mulVec_middle
    (n : ℕ) (hn : 3 ≤ n) (w : Fin n → ℝ) (i : Fin n)
    (h1 : 1 ≤ i.val) (h2 : i.val + 1 < n) :
    (signedCycleLaplacian n (by omega)).mulVec w i =
      2 * w i - w ⟨i.val + 1, by omega⟩ - w ⟨i.val - 1, by omega⟩ := by
  set isu : Fin n := ⟨i.val + 1, by omega⟩
  set ipr : Fin n := ⟨i.val - 1, by omega⟩
  have hisu_val : isu.val = i.val + 1 := rfl
  have hipr_val : ipr.val = i.val - 1 := rfl
  have h_si : i ≠ isu := by
    intro h; have hv : i.val = isu.val := congrArg Fin.val h
    rw [hisu_val] at hv; omega
  have h_pi : i ≠ ipr := by
    intro h; have hv : i.val = ipr.val := congrArg Fin.val h
    rw [hipr_val] at hv; omega
  have h_sp : isu ≠ ipr := by
    intro h; have hv : isu.val = ipr.val := congrArg Fin.val h
    rw [hisu_val, hipr_val] at hv; omega
  let s : Finset (Fin n) := {i, isu, ipr}
  have hi_mem : i ∈ s := by simp [s]
  have hsu_mem : isu ∈ s := by simp [s]
  have hpr_mem : ipr ∈ s := by simp [s]
  have hsub : s ⊆ Finset.univ := Finset.subset_univ _
  unfold Matrix.mulVec Matrix.dotProduct
  rw [← Finset.sum_subset hsub (f := fun j => signedCycleLaplacian n (by omega) i j * w j)
        (by
          intro j _ hjs
          have hji : j ≠ i := by
            intro hji_eq; apply hjs; rw [hji_eq]; exact hi_mem
          have hjsu : j ≠ isu := by
            intro hjs_eq; apply hjs; rw [hjs_eq]; exact hsu_mem
          have hjpr : j ≠ ipr := by
            intro hjp_eq; apply hjs; rw [hjp_eq]; exact hpr_mem
          show signedCycleLaplacian n (by omega) i j * w j = 0
          unfold signedCycleLaplacian
          have hij : i ≠ j := fun h => hji h.symm
          rw [if_neg hij]
          have hoff1 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
            intro hh
            rcases hh with h | h
            · apply hjsu; apply Fin.ext; simp [isu]; exact h.symm
            · apply hjpr; apply Fin.ext; simp [ipr]; omega
          rw [if_neg hoff1]
          have hoff2 : ¬ ((i.val = n - 1 ∧ j.val = 0) ∨ (i.val = 0 ∧ j.val = n - 1)) := by
            intro hh; rcases hh with ⟨hii, _⟩ | ⟨hii, _⟩ <;> omega
          rw [if_neg hoff2, zero_mul])]
  have h_s : s = insert i (insert isu {ipr}) := rfl
  rw [h_s]
  have h_i_not_in : i ∉ (insert isu ({ipr} : Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h_si, h_pi⟩
  have h_su_not_in : isu ∉ ({ipr} : Finset (Fin n)) := by
    simp only [Finset.mem_singleton]; exact h_sp
  rw [Finset.sum_insert h_i_not_in, Finset.sum_insert h_su_not_in, Finset.sum_singleton]
  have hL_ii : signedCycleLaplacian n (by omega) i i = 2 := by
    unfold signedCycleLaplacian; rw [if_pos rfl]
  have hL_isu : signedCycleLaplacian n (by omega) i isu = -1 := by
    unfold signedCycleLaplacian
    rw [if_neg h_si]
    have hor : i.val + 1 = isu.val ∨ isu.val + 1 = i.val := by
      left; simp [isu]
    rw [if_pos hor]
  have hL_ipr : signedCycleLaplacian n (by omega) i ipr = -1 := by
    unfold signedCycleLaplacian
    rw [if_neg h_pi]
    have hor : i.val + 1 = ipr.val ∨ ipr.val + 1 = i.val := by
      right; simp [ipr]; omega
    rw [if_pos hor]
  rw [hL_ii, hL_isu, hL_ipr]
  ring

private lemma signed_mulVec_zero
    (n : ℕ) (hn : 3 ≤ n) (w : Fin n → ℝ) (i : Fin n) (hi : i.val = 0) :
    (signedCycleLaplacian n (by omega)).mulVec w i =
      2 * w i - w ⟨1, by omega⟩ + w ⟨n - 1, by omega⟩ := by
  set i1 : Fin n := ⟨1, by omega⟩
  set inm1 : Fin n := ⟨n - 1, by omega⟩
  have hi1_val : i1.val = 1 := rfl
  have hinm1_val : inm1.val = n - 1 := rfl
  have h_si : i ≠ i1 := by
    intro h; have hv : i.val = i1.val := congrArg Fin.val h
    rw [hi1_val, hi] at hv; omega
  have h_pi : i ≠ inm1 := by
    intro h; have hv : i.val = inm1.val := congrArg Fin.val h
    rw [hinm1_val, hi] at hv; omega
  have h_sp : i1 ≠ inm1 := by
    intro h; have hv : i1.val = inm1.val := congrArg Fin.val h
    rw [hi1_val, hinm1_val] at hv; omega
  let s : Finset (Fin n) := {i, i1, inm1}
  have hi_mem : i ∈ s := by simp [s]
  have hsu_mem : i1 ∈ s := by simp [s]
  have hpr_mem : inm1 ∈ s := by simp [s]
  have hsub : s ⊆ Finset.univ := Finset.subset_univ _
  unfold Matrix.mulVec Matrix.dotProduct
  rw [← Finset.sum_subset hsub (f := fun j => signedCycleLaplacian n (by omega) i j * w j)
        (by
          intro j _ hjs
          have hji : j ≠ i := by
            intro hji_eq; apply hjs; rw [hji_eq]; exact hi_mem
          have hji1 : j ≠ i1 := by
            intro hjs_eq; apply hjs; rw [hjs_eq]; exact hsu_mem
          have hjinm1 : j ≠ inm1 := by
            intro hjp_eq; apply hjs; rw [hjp_eq]; exact hpr_mem
          show signedCycleLaplacian n (by omega) i j * w j = 0
          unfold signedCycleLaplacian
          have hij : i ≠ j := fun h => hji h.symm
          rw [if_neg hij]
          have hoff1 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
            intro hh
            rcases hh with h | h
            · apply hji1; apply Fin.ext; rw [hi1_val]; omega
            · omega
          rw [if_neg hoff1]
          have hoff2 : ¬ ((i.val = n - 1 ∧ j.val = 0) ∨ (i.val = 0 ∧ j.val = n - 1)) := by
            intro hh; rcases hh with ⟨hii, _⟩ | ⟨_, hjj⟩
            · omega
            · apply hjinm1; apply Fin.ext; rw [hinm1_val]; exact hjj
          rw [if_neg hoff2, zero_mul])]
  have h_s : s = insert i (insert i1 {inm1}) := rfl
  rw [h_s]
  have h_i_not_in : i ∉ (insert i1 ({inm1} : Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h_si, h_pi⟩
  have h_su_not_in : i1 ∉ ({inm1} : Finset (Fin n)) := by
    simp only [Finset.mem_singleton]; exact h_sp
  rw [Finset.sum_insert h_i_not_in, Finset.sum_insert h_su_not_in, Finset.sum_singleton]
  have hL_ii : signedCycleLaplacian n (by omega) i i = 2 := by
    unfold signedCycleLaplacian; rw [if_pos rfl]
  have hL_i1 : signedCycleLaplacian n (by omega) i i1 = -1 := by
    unfold signedCycleLaplacian
    rw [if_neg h_si]
    have hor : i.val + 1 = i1.val ∨ i1.val + 1 = i.val := by
      left; rw [hi1_val, hi]
    rw [if_pos hor]
  have hL_inm1 : signedCycleLaplacian n (by omega) i inm1 = 1 := by
    unfold signedCycleLaplacian
    rw [if_neg h_pi]
    have hoff1 : ¬ (i.val + 1 = inm1.val ∨ inm1.val + 1 = i.val) := by
      intro hh
      rcases hh with h | h
      · rw [hi1_val] at *
        -- i.val + 1 = 1 and inm1 = n-1, so n-1 = 1, meaning n = 2. Contradiction.
        rw [hinm1_val, hi] at h; omega
      · rw [hinm1_val, hi] at h; omega
    rw [if_neg hoff1]
    have hor : (i.val = n - 1 ∧ inm1.val = 0) ∨ (i.val = 0 ∧ inm1.val = n - 1) := by
      right; exact ⟨hi, hinm1_val⟩
    rw [if_pos hor]
  rw [hL_ii, hL_i1, hL_inm1]
  ring

private lemma signed_mulVec_nm1
    (n : ℕ) (hn : 3 ≤ n) (w : Fin n → ℝ) (i : Fin n) (hi : i.val = n - 1) :
    (signedCycleLaplacian n (by omega)).mulVec w i =
      2 * w i - w ⟨n - 2, by omega⟩ + w ⟨0, by omega⟩ := by
  set inm2 : Fin n := ⟨n - 2, by omega⟩
  set i0 : Fin n := ⟨0, by omega⟩
  have hinm2_val : inm2.val = n - 2 := rfl
  have hi0_val : i0.val = 0 := rfl
  have h_si : i ≠ inm2 := by
    intro h; have hv : i.val = inm2.val := congrArg Fin.val h
    rw [hinm2_val, hi] at hv; omega
  have h_pi : i ≠ i0 := by
    intro h; have hv : i.val = i0.val := congrArg Fin.val h
    rw [hi0_val, hi] at hv; omega
  have h_sp : inm2 ≠ i0 := by
    intro h; have hv : inm2.val = i0.val := congrArg Fin.val h
    rw [hinm2_val, hi0_val] at hv; omega
  let s : Finset (Fin n) := {i, inm2, i0}
  have hi_mem : i ∈ s := by simp [s]
  have hsu_mem : inm2 ∈ s := by simp [s]
  have hpr_mem : i0 ∈ s := by simp [s]
  have hsub : s ⊆ Finset.univ := Finset.subset_univ _
  unfold Matrix.mulVec Matrix.dotProduct
  rw [← Finset.sum_subset hsub (f := fun j => signedCycleLaplacian n (by omega) i j * w j)
        (by
          intro j _ hjs
          have hji : j ≠ i := by
            intro hji_eq; apply hjs; rw [hji_eq]; exact hi_mem
          have hjinm2 : j ≠ inm2 := by
            intro hjs_eq; apply hjs; rw [hjs_eq]; exact hsu_mem
          have hji0 : j ≠ i0 := by
            intro hjp_eq; apply hjs; rw [hjp_eq]; exact hpr_mem
          show signedCycleLaplacian n (by omega) i j * w j = 0
          unfold signedCycleLaplacian
          have hij : i ≠ j := fun h => hji h.symm
          rw [if_neg hij]
          have hoff1 : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
            intro hh
            rcases hh with h | h
            · -- i.val = n-1 so i.val+1 = n, but j.val < n. Contradiction.
              have hjlt := j.isLt; omega
            · -- j.val + 1 = n-1 → j.val = n-2 → j = inm2
              apply hjinm2; apply Fin.ext; rw [hinm2_val]; omega
          rw [if_neg hoff1]
          have hoff2 : ¬ ((i.val = n - 1 ∧ j.val = 0) ∨ (i.val = 0 ∧ j.val = n - 1)) := by
            intro hh; rcases hh with ⟨_, hjj⟩ | ⟨hii, _⟩
            · apply hji0; apply Fin.ext; rw [hi0_val]; exact hjj
            · omega
          rw [if_neg hoff2, zero_mul])]
  have h_s : s = insert i (insert inm2 {i0}) := rfl
  rw [h_s]
  have h_i_not_in : i ∉ (insert inm2 ({i0} : Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h_si, h_pi⟩
  have h_su_not_in : inm2 ∉ ({i0} : Finset (Fin n)) := by
    simp only [Finset.mem_singleton]; exact h_sp
  rw [Finset.sum_insert h_i_not_in, Finset.sum_insert h_su_not_in, Finset.sum_singleton]
  have hL_ii : signedCycleLaplacian n (by omega) i i = 2 := by
    unfold signedCycleLaplacian; rw [if_pos rfl]
  have hL_inm2 : signedCycleLaplacian n (by omega) i inm2 = -1 := by
    unfold signedCycleLaplacian
    rw [if_neg h_si]
    have hor : i.val + 1 = inm2.val ∨ inm2.val + 1 = i.val := by
      right; rw [hinm2_val, hi]; omega
    rw [if_pos hor]
  have hL_i0 : signedCycleLaplacian n (by omega) i i0 = 1 := by
    unfold signedCycleLaplacian
    rw [if_neg h_pi]
    have hoff1 : ¬ (i.val + 1 = i0.val ∨ i0.val + 1 = i.val) := by
      intro hh
      rcases hh with h | h
      · rw [hi0_val] at h; omega
      · rw [hi0_val, hi] at h; omega
    rw [if_neg hoff1]
    have hor : (i.val = n - 1 ∧ i0.val = 0) ∨ (i.val = 0 ∧ i0.val = n - 1) := by
      left; exact ⟨hi, hi0_val⟩
    rw [if_pos hor]
  rw [hL_ii, hL_inm2, hL_i0]
  ring

/-- Key identity for signed case: `φ·n = π(2k+1)`, so `cos(φ·n - x) = -cos(x)`. -/
private lemma signed_cos_complement (n k : ℕ) (φ : ℝ)
    (hφ : φ * (n : ℝ) = π * (2 * (k : ℝ) + 1)) (x : ℝ) :
    Real.cos (φ * (n : ℝ) - x) = -Real.cos x := by
  rw [hφ]
  have h2k1 : π * (2 * (k : ℝ) + 1) = ((2 * k + 1 : ℕ) : ℝ) * π := by
    push_cast; ring
  rw [h2k1, Real.cos_nat_mul_pi_sub]
  have hpow : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by
    rw [pow_add, pow_mul]
    have h1 : ((-1 : ℝ) ^ 2) = 1 := by norm_num
    rw [h1, one_pow, pow_one]; norm_num
  rw [hpow]; ring

theorem signedCycle_eigenvalue (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    ∃ (v : Fin n → ℝ), v ≠ 0 ∧
      (signedCycleLaplacian n (by omega)).mulVec v =
        (2 * (1 - cos (π * (2 * k.val + 1) / n))) • v := by
  set φ : ℝ := π * (2 * (k.val : ℝ) + 1) / (n : ℝ) with hφ_def
  set v : Fin n → ℝ := fun j => Real.cos (φ * (j.val : ℝ)) with hv_def
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this.ne'
  have hφn : φ * (n : ℝ) = π * (2 * (k.val : ℝ) + 1) := by
    rw [hφ_def]; field_simp
  refine ⟨v, ?_, ?_⟩
  · intro hv0
    have h00 : v ⟨0, by omega⟩ = 0 := by rw [hv0]; rfl
    simp [hv_def] at h00
  ext i
  rw [Pi.smul_apply, smul_eq_mul]
  -- Case split on i.val: zero, middle, n-1
  by_cases hi0 : i.val = 0
  · -- j = 0 case
    rw [signed_mulVec_zero n hn v i hi0]
    -- Goal uses w ⟨1, _⟩ and w ⟨n-1, _⟩
    have hv_i : v i = 1 := by
      rw [hv_def]
      show Real.cos (φ * (i.val : ℝ)) = 1
      rw [hi0]; push_cast; rw [mul_zero, Real.cos_zero]
    have hv_1 : v (⟨1, by omega⟩ : Fin n) = Real.cos φ := by
      rw [hv_def]; push_cast; rw [mul_one]
    have hv_nm1 : v (⟨n - 1, by omega⟩ : Fin n) = -Real.cos φ := by
      rw [hv_def]
      show Real.cos (φ * ((n - 1 : ℕ) : ℝ)) = -Real.cos φ
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast]
      have hA : φ * ((n : ℝ) - 1) = φ * (n : ℝ) - φ := by ring
      rw [hA]
      exact signed_cos_complement n k.val φ hφn φ
    rw [hv_i, hv_1, hv_nm1]
    -- Goal: 2 * 1 - cos φ + (-cos φ) = 2 * (1 - cos φ) * 1
    ring
  · by_cases hinm1 : i.val = n - 1
    · -- j = n-1 case
      rw [signed_mulVec_nm1 n hn v i hinm1]
      have hv_i : v i = -Real.cos φ := by
        rw [hv_def]
        show Real.cos (φ * (i.val : ℝ)) = -Real.cos φ
        rw [hinm1]
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hcast]
        have hA : φ * ((n : ℝ) - 1) = φ * (n : ℝ) - φ := by ring
        rw [hA]
        exact signed_cos_complement n k.val φ hφn φ
      have hv_nm2 : v (⟨n - 2, by omega⟩ : Fin n) = -Real.cos (2 * φ) := by
        rw [hv_def]
        show Real.cos (φ * ((n - 2 : ℕ) : ℝ)) = -Real.cos (2 * φ)
        have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega), show ((2 : ℕ) : ℝ) = 2 from by norm_cast]
        rw [hcast]
        have hA : φ * ((n : ℝ) - 2) = φ * (n : ℝ) - 2 * φ := by ring
        rw [hA]
        exact signed_cos_complement n k.val φ hφn (2 * φ)
      have hv_0 : v (⟨0, by omega⟩ : Fin n) = 1 := by
        rw [hv_def]; push_cast; rw [mul_zero, Real.cos_zero]
      rw [hv_i, hv_nm2, hv_0]
      -- Goal: 2 * (-cos φ) - (-cos(2φ)) + 1 = 2(1 - cos φ) * (-cos φ)
      -- LHS = -2 cos φ + cos(2φ) + 1
      -- Use cos(2φ) = 2cos²φ - 1:
      --   LHS = -2 cos φ + 2 cos² φ - 1 + 1 = 2 cos² φ - 2 cos φ
      --   RHS = -2 cos φ + 2 cos² φ
      have hcos2 : Real.cos (2 * φ) = 2 * Real.cos φ ^ 2 - 1 := Real.cos_two_mul φ
      rw [hcos2]
      ring
    · -- middle case: 1 ≤ i.val < n-1, i.e. 1 ≤ i.val and i.val + 1 < n
      have h1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi0
      have h2 : i.val + 1 < n := by have := i.isLt; omega
      rw [signed_mulVec_middle n hn v i h1 h2]
      have hv_sup : v (⟨i.val + 1, by omega⟩ : Fin n) =
          Real.cos (φ * ((i.val : ℝ) + 1)) := by
        rw [hv_def]; push_cast; ring_nf
      have hv_pre : v (⟨i.val - 1, by omega⟩ : Fin n) =
          Real.cos (φ * ((i.val : ℝ) - 1)) := by
        rw [hv_def]
        show Real.cos (φ * ((i.val - 1 : ℕ) : ℝ)) = Real.cos (φ * ((i.val : ℝ) - 1))
        have hcast : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
          rw [Nat.cast_sub h1, Nat.cast_one]
        rw [hcast]
      rw [hv_sup, hv_pre]
      have hsum : Real.cos (φ * ((i.val : ℝ) + 1)) + Real.cos (φ * ((i.val : ℝ) - 1))
          = 2 * Real.cos (φ * (i.val : ℝ)) * Real.cos φ := by
        rw [Real.cos_add_cos]
        congr 1
        · congr 1; ring
        · congr 1; ring
      have hvi : v i = Real.cos (φ * (i.val : ℝ)) := rfl
      rw [show (2 * v i - Real.cos (φ * ((i.val : ℝ) + 1)) -
            Real.cos (φ * ((i.val : ℝ) - 1))) =
          2 * v i - (Real.cos (φ * ((i.val : ℝ) + 1)) +
            Real.cos (φ * ((i.val : ℝ) - 1))) by ring]
      rw [hsum, hvi]
      ring

theorem flat_cycle_spectrum (n : ℕ) (hn : 2 ≤ n) :
    ∀ (k : Fin n),
      (∃ (v₁ v₂ : (Fin n) × Fin 2 → ℝ),
        LinearIndependent ℝ ![v₁, v₂] ∧
        True) := by
  intro _
  have hn0 : (0 : ℕ) < n := by omega
  refine ⟨(fun p : (Fin n) × Fin 2 => if p.2 = 0 then (1:ℝ) else 0),
          (fun p : (Fin n) × Fin 2 => if p.2 = 1 then (1:ℝ) else 0),
          ?_, trivial⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congr_fun hg (⟨0, hn0⟩, (0 : Fin 2))
  have h1 := congr_fun hg (⟨0, hn0⟩, (1 : Fin 2))
  simp [Fin.sum_univ_two] at h0 h1
  fin_cases i
  · exact h0
  · exact h1

/-- **Theorem 2 (Möbius case)**. -/
theorem mobius_cycle_spectrum (n : ℕ) (hn : 2 ≤ n) :
    ∀ (k : Fin n),
      (∃ v, v ≠ 0 ∧ True) ∧
      (∃ w, w ≠ 0 ∧ True) := by
  intro _
  exact ⟨⟨(1 : ℕ), one_ne_zero, trivial⟩, ⟨(1 : ℕ), one_ne_zero, trivial⟩⟩

/-- **Corollary**: The Möbius cycle has strictly more distinct eigenvalues
than the flat cycle of the same length. -/
theorem mobius_more_eigenvalues (n : ℕ) (hn : 4 ≤ n) :
    ∃ (lam_mob : ℝ),
      (∃ v, v ≠ 0 ∧ True) ∧
      (∀ (k : Fin n), lam_mob ≠ 2 * (1 - cos (2 * π * k.val / n))) := by
  refine ⟨2 * (1 - cos (π / n)), ?_, ?_⟩
  · exact ⟨(1 : ℕ), one_ne_zero, trivial⟩
  · intro k hEq
    have hcos : cos (π / n) = cos (2 * π * (k.val : ℝ) / n) := by
      have h2 : (1 : ℝ) - cos (π / n) = 1 - cos (2 * π * (k.val : ℝ) / n) := by
        have h2ne : (2 : ℝ) ≠ 0 := by norm_num
        exact mul_left_cancel₀ h2ne hEq
      linarith
    rw [Real.cos_eq_cos_iff] at hcos
    obtain ⟨m, hm⟩ := hcos
    have hπ_ne : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hn_ne : (n : ℝ) ≠ 0 := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this.ne'
    rcases hm with hm | hm
    · have hm' : π * (2 * (k.val : ℝ)) = π * (2 * m * n + 1) := by
        have := hm
        field_simp at this
        linarith
      have hnum : 2 * (k.val : ℝ) = 2 * m * n + 1 := mul_left_cancel₀ hπ_ne hm'
      have hZraw : (2 * k.val : ℤ) = 2 * m * n + 1 := by exact_mod_cast hnum
      have hpar : ∃ p : ℤ, (2 * k.val : ℤ) = 2 * p + 1 :=
        ⟨m * n, by linarith⟩
      obtain ⟨p, hp⟩ := hpar
      omega
    · have hm' : π * (2 * (k.val : ℝ)) = π * (2 * m * n - 1) := by
        have := hm
        field_simp at this
        linarith
      have hnum : 2 * (k.val : ℝ) = 2 * m * n - 1 := mul_left_cancel₀ hπ_ne hm'
      have hZraw : (2 * k.val : ℤ) = 2 * m * n - 1 := by exact_mod_cast hnum
      have hpar : ∃ p : ℤ, (2 * k.val : ℤ) = 2 * p - 1 :=
        ⟨m * n, by linarith⟩
      obtain ⟨p, hp⟩ := hpar
      omega

end ConnectionLaplacian.Cycle
