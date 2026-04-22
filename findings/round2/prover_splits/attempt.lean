/-
findings/round2/prover_splits/attempt.lean

Sorry-free proof of `scalarLap_cover_splits`
(ConnectionLaplacian/L5_Cover.lean:176).

Strategy (mirrors laplacian_decomposes / Möbius branch):
  P = 1_V ⊗ₖ RhatBool  with RhatBool = (!![1,1;1,-1] indexed by Bool)
  RhatBool * RhatBool = 2 • 1, so P⁻¹ = (1/2) • P
  Then (P · L̃ · P⁻¹) = (1/2) (P · L̃ · P)
  Compute entries via Kronecker-style collapse to reduce to
    (RhatBool * covBlock u v * RhatBool) i j
  where covBlock u v is a 2×2 Bool × Bool block of L̃.
  Case on u = v / adj / wrap to finish.
-/

import ConnectionLaplacian.L5_Cover

namespace ConnectionLaplacian

open Matrix BigOperators
open scoped Kronecker

namespace ConnGraph

variable (G : ConnGraph)

/-! ## Hadamard rotation on the Bool fibre. -/

/-- `RhatBool[b, c] = +1` unless both `b = true` and `c = true`, in which
case it is `-1`. Equivalently: `!![1,1 ; 1,-1]` under `false ↦ 0, true ↦ 1`. -/
private def RhatBool : Matrix Bool Bool ℝ :=
  fun i j => if i = true ∧ j = true then (-1 : ℝ) else 1

@[simp] private lemma RhatBool_ff : RhatBool false false = 1 := by simp [RhatBool]
@[simp] private lemma RhatBool_ft : RhatBool false true  = 1 := by simp [RhatBool]
@[simp] private lemma RhatBool_tf : RhatBool true  false = 1 := by simp [RhatBool]
@[simp] private lemma RhatBool_tt : RhatBool true  true  = -1 := by simp [RhatBool]

private lemma Bool_sum (f : Bool → ℝ) :
    ∑ b : Bool, f b = f false + f true := by
  rw [Fintype.sum_bool]; ring

private lemma RhatBool_sq :
    RhatBool * RhatBool = (2 : ℝ) • (1 : Matrix Bool Bool ℝ) := by
  ext i j
  rw [Matrix.mul_apply, Bool_sum]
  cases i <;> cases j <;>
    simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;> ring

/-! ## The similarity matrix `Pcov`. -/

private noncomputable def Pcov : Matrix G.CoverV G.CoverV ℝ :=
  (1 : Matrix G.V G.V ℝ) ⊗ₖ RhatBool

private lemma Pcov_apply (u v : G.V) (i j : Bool) :
    G.Pcov (u, i) (v, j) = if u = v then RhatBool i j else 0 := by
  show ((1 : Matrix G.V G.V ℝ) ⊗ₖ RhatBool) (u, i) (v, j) = _
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs with huv
  · rw [one_mul]
  · rw [zero_mul]

private lemma Pcov_mul_Pcov :
    G.Pcov * G.Pcov = (2 : ℝ) • (1 : Matrix G.CoverV G.CoverV ℝ) := by
  show ((1 : Matrix G.V G.V ℝ) ⊗ₖ RhatBool) *
       ((1 : Matrix G.V G.V ℝ) ⊗ₖ RhatBool)
     = (2 : ℝ) • (1 : Matrix G.CoverV G.CoverV ℝ)
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, RhatBool_sq,
      Matrix.kronecker_smul, Matrix.one_kronecker_one]

private lemma Pcov_inv_eq : G.Pcov⁻¹ = (1/2 : ℝ) • G.Pcov := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, G.Pcov_mul_Pcov, smul_smul]
  norm_num

private lemma Pcov_det_ne_zero : G.Pcov.det ≠ 0 := by
  intro h
  have hPinvP : G.Pcov * ((1/2 : ℝ) • G.Pcov) = 1 := by
    rw [Matrix.mul_smul, G.Pcov_mul_Pcov, smul_smul]; norm_num
  have hd := congrArg Matrix.det hPinvP
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hd
  exact zero_ne_one hd

/-! ## Cover-Laplacian entries — the "block" view.

`covBlock u v : Matrix Bool Bool ℝ` gives the 2×2 block at rows `{u}×Bool`,
cols `{v}×Bool` of the cover's scalar Laplacian `L̃`. -/

private noncomputable def covBlock (u v : G.V) : Matrix Bool Bool ℝ :=
  fun i j => G.orientationDoubleCover.scalarLaplacian (u, i) (v, j)

@[simp] private lemma covBlock_apply (u v : G.V) (i j : Bool) :
    G.covBlock u v i j = G.orientationDoubleCover.scalarLaplacian (u, i) (v, j) := rfl

/-! ### Cover-adjacency unfolding. -/

private lemma coverAdj_iff (u v : G.V) (b c : Bool) :
    G.coverGraph.Adj (u, b) (v, c) ↔
      ∃ h : G.graph.Adj u v,
        G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ ↔ b ≠ c := by
  show G.coverAdj (u, b) (v, c) ↔ _
  unfold coverAdj
  split_ifs with h
  · simp [h]
  · simp [h]

/-! ### Degree of `(u, b)` in the cover equals the degree of `u` in `G`.

The neighbours of `(u, b)` in `coverGraph` are in bijection with the
neighbours of `u` in `G`: for each `v ∼ u` there is exactly one sheet
`b'` with `(u,b) ∼ (v,b')`, determined by wrap status. -/

private lemma coverGraph_degree_eq (u : G.V) (b : Bool) :
    G.coverGraph.degree (u, b) = G.graph.degree u := by
  classical
  -- Build a bijection neighbourFinset u → neighbourFinset (u, b)
  -- via v ↦ (v, c) where c = b if not wrap, else !b.
  set f : G.V → G.CoverV := fun v =>
    if h : G.graph.Adj u v then
      if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ then (v, !b) else (v, b)
    else (v, b)
  have f_target : ∀ v, G.graph.Adj u v → G.coverGraph.Adj (u, b) (f v) := by
    intro v hv
    simp only [f, dif_pos hv]
    by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hv⟩
    · rw [if_pos hw]
      show G.coverAdj (u, b) (v, !b)
      rw [show G.coverAdj (u, b) (v, !b) ↔ _ from G.coverAdj_iff u v b (!b)]
      refine ⟨hv, ?_⟩
      simp [hw, Bool.not_eq_self]
    · rw [if_neg hw]
      show G.coverAdj (u, b) (v, b)
      rw [show G.coverAdj (u, b) (v, b) ↔ _ from G.coverAdj_iff u v b b]
      refine ⟨hv, ?_⟩
      simp [hw]
  unfold SimpleGraph.degree SimpleGraph.neighborFinset SimpleGraph.neighborSet
  rw [Set.toFinset_setOf, Set.toFinset_setOf]
  symm
  apply Finset.card_bij (fun v _ => f v)
  · -- maps filter → filter
    intro v hv
    rw [Finset.mem_filter] at hv
    have hv' : G.graph.Adj u v := hv.2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact f_target v hv'
  · -- injectivity: f v₁ = f v₂ ⇒ v₁ = v₂
    intro v₁ hv₁ v₂ hv₂ hfeq
    rw [Finset.mem_filter] at hv₁ hv₂
    -- The first component of f v is v itself (by construction).
    have e1 : (f v₁).1 = v₁ := by
      simp only [f]; split_ifs <;> rfl
    have e2 : (f v₂).1 = v₂ := by
      simp only [f]; split_ifs <;> rfl
    have := congrArg Prod.fst hfeq
    rw [e1, e2] at this
    exact this
  · -- surjectivity: every cover-neighbour of (u, b) is f v for some v ∼ u.
    intro x hx
    rw [Finset.mem_filter] at hx
    rcases x with ⟨v, c⟩
    have hadj : G.coverGraph.Adj (u, b) (v, c) := hx.2
    have := (G.coverAdj_iff u v b c).mp hadj
    obtain ⟨hG, hw⟩ := this
    refine ⟨v, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hG⟩
    -- f v vs (v, c): check they match.
    simp only [f, dif_pos hG]
    by_cases hwrap : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hG⟩
    · rw [if_pos hwrap]
      -- c = !b since wrap forces b ≠ c
      have hbc : b ≠ c := hw.mp hwrap
      have : c = !b := by cases b <;> cases c <;> simp_all
      rw [this]
    · rw [if_neg hwrap]
      -- c = b since no wrap forces b = c
      have hbc : ¬ (b ≠ c) := fun h => hwrap (hw.mpr h)
      have : c = b := by cases b <;> cases c <;> simp_all
      rw [this]

/-! ### Entry-wise formula for the cover's scalar Laplacian. -/

private lemma cover_lap_entry (u v : G.V) (b c : Bool) :
    G.orientationDoubleCover.scalarLaplacian (u, b) (v, c) =
      (if (u, b) = (v, c) then (G.graph.degree u : ℝ) else 0)
      - (if G.coverGraph.Adj (u, b) (v, c) then 1 else 0) := by
  show G.coverGraph.lapMatrix ℝ (u, b) (v, c) = _
  rw [SimpleGraph.lapMatrix]
  simp only [Matrix.sub_apply]
  rw [SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply]
  by_cases h : (u, b) = (v, c)
  · obtain ⟨rfl, rfl⟩ : u = v ∧ b = c := Prod.mk.inj_iff.mp h
    simp only [if_true, G.coverGraph_degree_eq u b]
  · rw [if_neg h, if_neg h]

/-! ### The 2×2 block `covBlock u v` in the three structural cases. -/

/-- Case 1: diagonal block `covBlock u u = deg u · I₂` (Bool version). -/
private lemma covBlock_diag (u : G.V) :
    G.covBlock u u = (G.graph.degree u : ℝ) •
      (1 : Matrix Bool Bool ℝ) := by
  ext i j
  rw [covBlock_apply, G.cover_lap_entry u u i j]
  by_cases hij : i = j
  · subst hij
    have h_eq : ((u, i) : G.CoverV) = (u, i) := rfl
    rw [if_pos h_eq]
    have hirr : ¬ G.coverGraph.Adj (u, i) (u, i) := G.coverGraph.loopless _
    rw [if_neg hirr]
    simp [Matrix.smul_apply, Matrix.one_apply_eq]
  · have h_ne : ((u, i) : G.CoverV) ≠ (u, j) := by
      intro heq; exact hij (Prod.mk.inj_iff.mp heq).2
    rw [if_neg h_ne]
    have hirr : ¬ G.coverGraph.Adj (u, i) (u, j) := by
      intro hadj
      have : G.graph.Adj u u :=
        ((G.coverAdj_iff u u i j).mp hadj).1
      exact SimpleGraph.irrefl _ this
    rw [if_neg hirr]
    simp [Matrix.smul_apply, Matrix.one_apply_ne hij]

/-- Case 2a: off-diagonal adjacent non-wrap block is `-1 · I₂`. -/
private lemma covBlock_nonwrap (u v : G.V) (huv : u ≠ v) (hadj : G.graph.Adj u v)
    (hnw : ¬ G.wrap ⟨s(u,v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩) :
    G.covBlock u v = (-1 : ℝ) • (1 : Matrix Bool Bool ℝ) := by
  ext i j
  rw [covBlock_apply, G.cover_lap_entry u v i j]
  have h_ne : ((u, i) : G.CoverV) ≠ (v, j) := by
    intro heq; exact huv (Prod.mk.inj_iff.mp heq).1
  rw [if_neg h_ne]
  by_cases hij : i = j
  · -- non-wrap + same sheet → adjacent
    subst hij
    have hcadj : G.coverGraph.Adj (u, i) (v, i) := by
      rw [G.coverAdj_iff u v i i]
      refine ⟨hadj, ?_⟩
      simp [hnw]
    rw [if_pos hcadj]
    simp [Matrix.smul_apply, Matrix.one_apply_eq]
  · -- non-wrap + diff sheet → not adjacent
    have hcnadj : ¬ G.coverGraph.Adj (u, i) (v, j) := by
      intro hadj'
      rw [G.coverAdj_iff u v i j] at hadj'
      obtain ⟨_, hw⟩ := hadj'
      have hne : i ≠ j := hij
      exact hnw (hw.mpr hne)
    rw [if_neg hcnadj]
    simp [Matrix.smul_apply, Matrix.one_apply_ne hij]

/-- Case 2b: off-diagonal adjacent wrap block is `-σx` (Bool version) — i.e.
zero on the diagonal and `-1` off-diagonal. -/
private lemma covBlock_wrap (u v : G.V) (huv : u ≠ v) (hadj : G.graph.Adj u v)
    (hw : G.wrap ⟨s(u,v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩) :
    ∀ i j : Bool, G.covBlock u v i j = if i = j then 0 else -1 := by
  intro i j
  rw [covBlock_apply, G.cover_lap_entry u v i j]
  have h_ne : ((u, i) : G.CoverV) ≠ (v, j) := by
    intro heq; exact huv (Prod.mk.inj_iff.mp heq).1
  rw [if_neg h_ne]
  by_cases hij : i = j
  · subst hij
    have hcnadj : ¬ G.coverGraph.Adj (u, i) (v, i) := by
      intro hadj'
      rw [G.coverAdj_iff u v i i] at hadj'
      obtain ⟨_, hw'⟩ := hadj'
      exact (hw'.mp hw) rfl
    rw [if_neg hcnadj, if_pos rfl]
    ring
  · have hcadj : G.coverGraph.Adj (u, i) (v, j) := by
      rw [G.coverAdj_iff u v i j]
      refine ⟨hadj, ?_⟩
      simp [hw, hij]
    rw [if_pos hcadj, if_neg hij]
    ring

/-- Case 3: non-adjacent off-diagonal block is 0. -/
private lemma covBlock_nonadj (u v : G.V) (huv : u ≠ v) (hnadj : ¬ G.graph.Adj u v) :
    G.covBlock u v = 0 := by
  ext i j
  rw [covBlock_apply, G.cover_lap_entry u v i j]
  have h_ne : ((u, i) : G.CoverV) ≠ (v, j) := by
    intro heq; exact huv (Prod.mk.inj_iff.mp heq).1
  rw [if_neg h_ne]
  have hcnadj : ¬ G.coverGraph.Adj (u, i) (v, j) := by
    intro hadj'
    exact hnadj ((G.coverAdj_iff u v i j).mp hadj').1
  rw [if_neg hcnadj]
  simp [Matrix.zero_apply]

/-! ## Conjugation reduces to a block computation. -/

/-- The cover Laplacian, type-cast to `Matrix G.CoverV G.CoverV ℝ`
(definitionally equal, but we spell it out so Lean sees compatible types
with `Pcov`). -/
private noncomputable def Lcov : Matrix G.CoverV G.CoverV ℝ :=
  G.orientationDoubleCover.scalarLaplacian

@[simp] private lemma Lcov_apply (x y : G.CoverV) :
    G.Lcov x y = G.orientationDoubleCover.scalarLaplacian x y := rfl

private lemma Pcov_mul_L_apply (u v : G.V) (i j : Bool) :
    (G.Pcov * G.Lcov) (u, i) (v, j) =
      (RhatBool * G.covBlock u v) i j := by
  -- Rewrite as an explicit double sum over V × Bool
  have heq : (G.Pcov * G.Lcov) (u, i) (v, j)
       = ∑ w : G.V, ∑ k : Bool,
           G.Pcov (u, i) (w, k) * G.Lcov (w, k) (v, j) := by
    rw [show (G.Pcov * G.Lcov) (u, i) (v, j) =
          ∑ x : G.V × Bool, G.Pcov (u, i) x * G.Lcov x (v, j) from
          Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
  rw [heq, Finset.sum_eq_single u]
  · rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [G.Pcov_apply u u i k, if_pos rfl]
    rfl
  · intro w _ hne
    apply Finset.sum_eq_zero
    intro k _
    rw [G.Pcov_apply u w i k, if_neg hne.symm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma Pcov_mul_L_mul_Pcov_apply (u v : G.V) (i j : Bool) :
    ((G.Pcov * G.Lcov) * G.Pcov) (u, i) (v, j) =
      (RhatBool * G.covBlock u v * RhatBool) i j := by
  have heq : ((G.Pcov * G.Lcov) * G.Pcov) (u, i) (v, j)
       = ∑ w : G.V, ∑ k : Bool,
           (G.Pcov * G.Lcov) (u, i) (w, k) * G.Pcov (w, k) (v, j) := by
    rw [show ((G.Pcov * G.Lcov) * G.Pcov) (u, i) (v, j) =
          ∑ x : G.V × Bool, (G.Pcov * G.Lcov) (u, i) x * G.Pcov x (v, j) from
          Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
  rw [heq, Finset.sum_eq_single v]
  · conv_rhs => rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [G.Pcov_mul_L_apply u v i k, G.Pcov_apply v v k j, if_pos rfl]
  · intro w _ hne
    apply Finset.sum_eq_zero
    intro k _
    rw [G.Pcov_apply w v k j, if_neg hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Rotated 2×2 blocks — entries after Hadamard conjugation. -/

/-- Key identity: RhatBool * (α • I) * RhatBool = diag(2α, 2α) on Bool. -/
private lemma RhatBool_smul_one_RhatBool (α : ℝ) (i j : Bool) :
    (RhatBool * (α • (1 : Matrix Bool Bool ℝ)) * RhatBool) i j =
      if i = j then 2 * α else 0 := by
  have h1 : RhatBool * (α • (1 : Matrix Bool Bool ℝ)) =
      α • RhatBool := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  rw [h1, Matrix.smul_mul, RhatBool_sq]
  simp only [Matrix.smul_apply, smul_eq_mul]
  cases i <;> cases j <;>
    simp [Matrix.one_apply] <;> ring

/-- The "off-diagonal wrap block" as a real Bool×Bool matrix. -/
private def wrapOffMat : Matrix Bool Bool ℝ :=
  fun a b => if a = b then (0 : ℝ) else -1

/-- Key identity: RhatBool * wrapOffMat * RhatBool = diag(−2, +2) (Bool).
    Symmetric fibre (i = false) sees `-2`, antisymmetric fibre (i = true)
    sees `+2`. -/
private lemma RhatBool_offdiag_RhatBool (i j : Bool) :
    (RhatBool * wrapOffMat * RhatBool) i j =
      if i = j then (if i = false then -2 else 2) else 0 := by
  -- Expand the three matrix multiplications via Bool_sum.
  have step1 : ∀ a b : Bool, (RhatBool * wrapOffMat) a b =
      RhatBool a false * wrapOffMat false b + RhatBool a true * wrapOffMat true b := by
    intro a b; rw [Matrix.mul_apply, Bool_sum]
  have step2 : ∀ a b : Bool, ((RhatBool * wrapOffMat) * RhatBool) a b =
      (RhatBool * wrapOffMat) a false * RhatBool false b
       + (RhatBool * wrapOffMat) a true * RhatBool true b := by
    intro a b; rw [Matrix.mul_apply, Bool_sum]
  rw [step2]
  simp only [step1]
  cases i <;> cases j <;>
    simp [wrapOffMat] <;> ring

/-! ## Core entry identity after rotation. -/

private lemma rotated_entry (u v : G.V) (i j : Bool) :
    (RhatBool * G.covBlock u v * RhatBool) i j =
      if i = j then
        2 * (if i = false then G.scalarLaplacian u v
             else G.signedLaplacianMobius u v)
      else 0 := by
  by_cases huv : u = v
  · subst huv
    rw [covBlock_diag G u]
    rw [RhatBool_smul_one_RhatBool (G.graph.degree u : ℝ) i j]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      -- Show 2 * deg u = 2 * scalarLaplacian u u (for i = false) / signedLaplacianMobius u u (for i = true)
      unfold scalarLaplacian signedLaplacianMobius
      have hna : ¬ G.graph.Adj u u := SimpleGraph.irrefl _
      simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
                 Matrix.diagonal_apply_eq, SimpleGraph.adjMatrix_apply,
                 if_pos rfl, if_neg hna, Matrix.zero_apply, sub_zero]
      unfold SimpleGraph.degree
      cases i <;> simp
    · simp [if_neg hij]
  · by_cases hadj : G.graph.Adj u v
    · by_cases hw : G.wrap ⟨s(u,v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
      · -- wrap edge
        have hblk : G.covBlock u v = wrapOffMat := by
          ext a b
          rw [covBlock_wrap G u v huv hadj hw a b]
          rfl
        rw [hblk, RhatBool_offdiag_RhatBool i j]
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, if_pos rfl]
          -- scalarLaplacian u v vs signedLaplacianMobius u v
          unfold scalarLaplacian signedLaplacianMobius
          simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
                     Matrix.diagonal_apply_ne _ huv, SimpleGraph.adjMatrix_apply,
                     if_pos hadj, if_neg huv, Matrix.zero_apply, zero_sub,
                     dif_pos hadj, if_pos hw]
          cases i <;> simp
        · simp [if_neg hij]
      · -- non-wrap adjacent edge
        have hblk : G.covBlock u v = (-1 : ℝ) • (1 : Matrix Bool Bool ℝ) :=
          covBlock_nonwrap G u v huv hadj hw
        rw [hblk, RhatBool_smul_one_RhatBool (-1 : ℝ) i j]
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, if_pos rfl]
          unfold scalarLaplacian signedLaplacianMobius
          simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
                     Matrix.diagonal_apply_ne _ huv, SimpleGraph.adjMatrix_apply,
                     if_pos hadj, if_neg huv, Matrix.zero_apply, zero_sub,
                     dif_pos hadj, if_neg hw]
          cases i <;> simp
        · simp [if_neg hij]
    · -- not adjacent
      rw [covBlock_nonadj G u v huv hadj]
      simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        unfold scalarLaplacian signedLaplacianMobius
        simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
                   Matrix.diagonal_apply_ne _ huv, SimpleGraph.adjMatrix_apply,
                   if_neg hadj, Matrix.zero_apply, sub_zero, zero_sub, neg_zero,
                   if_neg huv, dif_neg hadj]
        cases i <;> simp
      · simp [if_neg hij]

/-! ## The main theorem. -/

theorem scalarLap_cover_splits_proof :
    ∃ (P : Matrix G.CoverV G.CoverV ℝ),
      P.det ≠ 0 ∧
      Matrix.reindex G.prodBoolEquivSum G.prodBoolEquivSum
        (P * (show Matrix G.CoverV G.CoverV ℝ from
                G.orientationDoubleCover.scalarLaplacian) * P⁻¹) =
      Matrix.fromBlocks G.scalarLaplacian 0 0 G.signedLaplacianMobius := by
  refine ⟨G.Pcov, Pcov_det_ne_zero G, ?_⟩
  -- Replace `G.orientationDoubleCover.scalarLaplacian` with `G.Lcov` (defeq)
  change Matrix.reindex G.prodBoolEquivSum G.prodBoolEquivSum
      (G.Pcov * G.Lcov * G.Pcov⁻¹) = _
  rw [Pcov_inv_eq G, Matrix.mul_smul]
  ext a b
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      smul_eq_mul]
  have hsym_inl : ∀ w : G.V, G.prodBoolEquivSum.symm (Sum.inl w) = (w, false) := by
    intro w; rfl
  have hsym_inr : ∀ w : G.V, G.prodBoolEquivSum.symm (Sum.inr w) = (w, true) := by
    intro w; rfl
  rcases a with u | u <;> rcases b with v | v
  · rw [hsym_inl, hsym_inl, Matrix.fromBlocks_apply₁₁,
        Pcov_mul_L_mul_Pcov_apply G u v false false,
        rotated_entry G u v false false, if_pos rfl, if_pos rfl]
    ring
  · rw [hsym_inl, hsym_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
        Pcov_mul_L_mul_Pcov_apply G u v false true,
        rotated_entry G u v false true, if_neg (by decide : false ≠ true)]
    ring
  · rw [hsym_inr, hsym_inl, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        Pcov_mul_L_mul_Pcov_apply G u v true false,
        rotated_entry G u v true false, if_neg (by decide : true ≠ false)]
    ring
  · rw [hsym_inr, hsym_inr, Matrix.fromBlocks_apply₂₂,
        Pcov_mul_L_mul_Pcov_apply G u v true true,
        rotated_entry G u v true true, if_pos rfl,
        if_neg (by decide : true ≠ false)]
    ring

end ConnGraph

end ConnectionLaplacian

/-
Sanity check: the proof depends only on the three standard Lean axioms:
  propext, Classical.choice, Quot.sound.
-/
#print axioms ConnectionLaplacian.ConnGraph.scalarLap_cover_splits_proof
