/-
ConnectionLaplacian/L5_Cover.lean

**Stratum L5 — Orientation Double Cover.**

Given `G : ConnGraph` with `wrap : edgeSet → Prop`, the orientation double
cover `G̃ : ConnGraph` is the 2-fold graph cover whose vertex set is
`G.V × Bool`, with an edge `(u, b) — (v, c)` iff `G.graph.Adj u v` and
`(b = c) ↔ ¬ wrap e`. Wrap edges flip the sheet; interior edges
preserve it. On `G̃`, the wrap structure is trivial (the cover
"unwraps" the non-orientability).

The Z/2 deck transformation `δ : G̃.V → G̃.V, (v, b) ↦ (v, ¬b)` is a
graph automorphism of `G̃`. Functions on `G̃` split into deck-invariant
(+1 eigenspace = functions on `G`, the flat connection kernel) and
deck-antiinvariant (−1 eigenspace = "twisted" sections of `G`, the
signed connection kernel).

The key theorem is `scalarLap_cover_splits`: the ordinary (scalar) graph
Laplacian of `G̃` is similar to the block-diagonal sum
`fromBlocks(scalarLaplacian G, signedLaplacianMobius G)`. Combined with
Mathlib's `card_ConnectedComponent_eq_rank_ker_lapMatrix` on `G̃`, this
reduces the signed kernel-dimension theorem to a scalar one on the
cover — dodging any bespoke Zaslavsky/signed-graph library.

Parallelization surface: the four pieces below can be owned by
independent agents once the types are fixed.
-/

import ConnectionLaplacian.KernelDimension

namespace ConnectionLaplacian

open Matrix BigOperators FiniteDimensional
open scoped Kronecker

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L5.1 — GraphCover construction -/

/-- Vertex set of the orientation double cover: two sheets over each
vertex of `G`, indexed by `Bool`. -/
def CoverV : Type _ := G.V × Bool

noncomputable instance : Fintype G.CoverV := by
  unfold CoverV; infer_instance

instance : DecidableEq G.CoverV := by
  unfold CoverV; infer_instance

/-- Adjacency on the orientation double cover: `(u,b)—(v,c)` iff
`G.graph.Adj u v`, with sheets related by wrap status of the edge.
Wrap edges flip sheet (b ≠ c); non-wrap edges preserve sheet (b = c). -/
def coverAdj : G.CoverV → G.CoverV → Prop :=
  fun x y =>
    if h : G.graph.Adj x.1 y.1 then
      (G.wrap ⟨s(x.1, y.1), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ ↔ x.2 ≠ y.2)
    else False

instance : DecidableRel G.coverAdj := by
  intro x y
  unfold coverAdj
  infer_instance

lemma coverAdj_symm : ∀ {x y : G.CoverV}, G.coverAdj x y → G.coverAdj y x := by
  rintro ⟨u, b⟩ ⟨v, c⟩ h
  by_cases hadj : G.graph.Adj u v
  · have hadj' : G.graph.Adj v u := hadj.symm
    have hedge :
        (⟨s(v, u), (SimpleGraph.mem_edgeSet G.graph).mpr hadj'⟩ :
              G.graph.edgeSet) =
          ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩ := by
      apply Subtype.ext; exact Sym2.eq_swap
    have hwrap : (G.coverAdj ⟨u, b⟩ ⟨v, c⟩) ↔
        (G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩ ↔ b ≠ c) := by
      show (if h : G.graph.Adj u v then _ else False) ↔ _
      rw [dif_pos hadj]
    have hwrap' : (G.coverAdj ⟨v, c⟩ ⟨u, b⟩) ↔
        (G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩ ↔ c ≠ b) := by
      show (if h : G.graph.Adj v u then _ else False) ↔ _
      rw [dif_pos hadj', hedge]
    rw [hwrap] at h
    rw [hwrap']
    tauto
  · exfalso
    have : G.coverAdj ⟨u, b⟩ ⟨v, c⟩ ↔ False := by
      show (if h : G.graph.Adj u v then _ else False) ↔ _
      rw [dif_neg hadj]
    exact this.mp h

lemma coverAdj_irrefl : ∀ (x : G.CoverV), ¬ G.coverAdj x x := by
  rintro ⟨u, b⟩ h
  have hnadj : ¬ G.graph.Adj u u := SimpleGraph.irrefl _
  have : G.coverAdj ⟨u, b⟩ ⟨u, b⟩ ↔ False := by
    show (if h : G.graph.Adj u u then _ else False) ↔ _
    rw [dif_neg hnadj]
  exact this.mp h

/-- The orientation double cover as a `SimpleGraph` on `G.V × Bool`. -/
def coverGraph : SimpleGraph G.CoverV where
  Adj := G.coverAdj
  symm _ _ := G.coverAdj_symm
  loopless := G.coverAdj_irrefl

instance : DecidableRel G.coverGraph.Adj :=
  (inferInstance : DecidableRel G.coverAdj)

/-- The orientation double cover lifted to a `ConnGraph` with trivial
wrap (every edge on `G̃` is an interior edge of its connection). -/
noncomputable def orientationDoubleCover : ConnGraph where
  V := G.CoverV
  graph := G.coverGraph
  wrap := fun _ => False

/-! ### L5.2 — Deck transformation (Z/2 action) -/

/-- The deck transformation: swap the two sheets over each vertex. -/
def deck : G.CoverV → G.CoverV := fun x => (x.1, !x.2)

/-- `deck` is an involution. -/
lemma deck_involution : ∀ x : G.CoverV, G.deck (G.deck x) = x := by
  intro ⟨v, b⟩
  simp [deck, Bool.not_not]

/-- `deck` is a graph automorphism of the cover. -/
lemma deck_adj_iff : ∀ x y : G.CoverV,
    G.coverAdj (G.deck x) (G.deck y) ↔ G.coverAdj x y := by
  rintro ⟨u, b⟩ ⟨v, c⟩
  unfold coverAdj deck
  by_cases hadj : G.graph.Adj u v
  · rw [dif_pos hadj, dif_pos hadj]
    constructor
    · intro h
      constructor
      · intro hw; have := h.mp hw; intro heq; exact this (by rw [heq])
      · intro hne; exact h.mpr (fun heq => hne (Bool.not_inj heq))
    · intro h
      constructor
      · intro hw; have := h.mp hw; intro heq; exact this (Bool.not_inj heq)
      · intro hne; exact h.mpr (fun heq => hne (by rw [heq]))
  · rw [dif_neg hadj, dif_neg hadj]

/-! ### L5.3 — Symmetric / antisymmetric decomposition -/

/-- Projection from `CoverV → ℝ` onto deck-invariant (+1 eigenspace)
sections — corresponds to pulling back functions from `G`. -/
noncomputable def symProj (f : G.CoverV → ℝ) : G.V → ℝ :=
  fun v => (f (v, false) + f (v, true)) / 2

/-- Projection onto deck-antiinvariant (−1 eigenspace) sections —
corresponds to signed sections on `G`. -/
noncomputable def antiProj (f : G.CoverV → ℝ) : G.V → ℝ :=
  fun v => (f (v, false) - f (v, true)) / 2

/-- Re-indexing equivalence for the cover: `G.V × Bool ≃ G.V ⊕ G.V`,
sending `(v, false) ↦ inl v` and `(v, true) ↦ inr v`. Aligns the cover's
sheet-indexed vertex set with a `fromBlocks` direct sum. -/
def prodBoolEquivSum : G.CoverV ≃ G.V ⊕ G.V :=
  (Equiv.prodComm _ _).trans (Equiv.boolProdEquivSum _)

/-! ### L5.4 — Cover splits scalar Laplacian into flat ⊕ signed

**Statement.** Under the reindexing `G.V × Bool ≃ G.V ⊕ G.V` and a
Hadamard-rotation conjugation, the cover's scalar Laplacian is similar
to the block-diagonal `fromBlocks(scalarLaplacian G, signedLaplacianMobius G)`.

**Proof.** Use `RhatBool : Matrix Bool Bool ℝ` (the 2×2 Hadamard), lift to
`P = (1 : Matrix V V ℝ) ⊗ᵏ RhatBool` via the Kronecker product. Then
`P * L̃ * P⁻¹`, when reindexed through `prodBoolEquivSum`, has off-diagonal
blocks that vanish entry-wise (wrap/no-wrap entries interfere destructively),
leaving the `fromBlocks` shape on the diagonal. Mirrors the Möbius branch of
`laplacian_decomposes` in `KernelDimension.lean`. -/

/-! #### Private helpers for `scalarLap_cover_splits`. -/

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

/-- The similarity matrix `Pcov = 1_V ⊗ₖ RhatBool`. -/
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

/-- The 2×2 `Bool × Bool` block of the cover's scalar Laplacian at `(u, v)`. -/
private noncomputable def covBlock (u v : G.V) : Matrix Bool Bool ℝ :=
  fun i j => G.orientationDoubleCover.scalarLaplacian (u, i) (v, j)

@[simp] private lemma covBlock_apply (u v : G.V) (i j : Bool) :
    G.covBlock u v i j = G.orientationDoubleCover.scalarLaplacian (u, i) (v, j) := rfl

private lemma coverAdj_iff (u v : G.V) (b c : Bool) :
    G.coverGraph.Adj (u, b) (v, c) ↔
      ∃ h : G.graph.Adj u v,
        G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ ↔ b ≠ c := by
  show G.coverAdj (u, b) (v, c) ↔ _
  unfold coverAdj
  split_ifs with h
  · simp [h]
  · simp [h]

private lemma coverGraph_degree_eq (u : G.V) (b : Bool) :
    G.coverGraph.degree (u, b) = G.graph.degree u := by
  classical
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
  · intro v hv
    rw [Finset.mem_filter] at hv
    have hv' : G.graph.Adj u v := hv.2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact f_target v hv'
  · intro v₁ hv₁ v₂ hv₂ hfeq
    rw [Finset.mem_filter] at hv₁ hv₂
    have e1 : (f v₁).1 = v₁ := by
      simp only [f]; split_ifs <;> rfl
    have e2 : (f v₂).1 = v₂ := by
      simp only [f]; split_ifs <;> rfl
    have := congrArg Prod.fst hfeq
    rw [e1, e2] at this
    exact this
  · intro x hx
    rw [Finset.mem_filter] at hx
    rcases x with ⟨v, c⟩
    have hadj : G.coverGraph.Adj (u, b) (v, c) := hx.2
    have := (G.coverAdj_iff u v b c).mp hadj
    obtain ⟨hG, hw⟩ := this
    refine ⟨v, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hG⟩
    simp only [f, dif_pos hG]
    by_cases hwrap : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hG⟩
    · rw [if_pos hwrap]
      have hbc : b ≠ c := hw.mp hwrap
      have : c = !b := by cases b <;> cases c <;> simp_all
      rw [this]
    · rw [if_neg hwrap]
      have hbc : ¬ (b ≠ c) := fun h => hwrap (hw.mpr h)
      have : c = b := by cases b <;> cases c <;> simp_all
      rw [this]

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

private lemma covBlock_nonwrap (u v : G.V) (huv : u ≠ v) (hadj : G.graph.Adj u v)
    (hnw : ¬ G.wrap ⟨s(u,v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩) :
    G.covBlock u v = (-1 : ℝ) • (1 : Matrix Bool Bool ℝ) := by
  ext i j
  rw [covBlock_apply, G.cover_lap_entry u v i j]
  have h_ne : ((u, i) : G.CoverV) ≠ (v, j) := by
    intro heq; exact huv (Prod.mk.inj_iff.mp heq).1
  rw [if_neg h_ne]
  by_cases hij : i = j
  · subst hij
    have hcadj : G.coverGraph.Adj (u, i) (v, i) := by
      rw [G.coverAdj_iff u v i i]
      refine ⟨hadj, ?_⟩
      simp [hnw]
    rw [if_pos hcadj]
    simp [Matrix.smul_apply, Matrix.one_apply_eq]
  · have hcnadj : ¬ G.coverGraph.Adj (u, i) (v, j) := by
      intro hadj'
      rw [G.coverAdj_iff u v i j] at hadj'
      obtain ⟨_, hw⟩ := hadj'
      have hne : i ≠ j := hij
      exact hnw (hw.mpr hne)
    rw [if_neg hcnadj]
    simp [Matrix.smul_apply, Matrix.one_apply_ne hij]

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

private noncomputable def Lcov : Matrix G.CoverV G.CoverV ℝ :=
  G.orientationDoubleCover.scalarLaplacian

@[simp] private lemma Lcov_apply (x y : G.CoverV) :
    G.Lcov x y = G.orientationDoubleCover.scalarLaplacian x y := rfl

private lemma Pcov_mul_L_apply (u v : G.V) (i j : Bool) :
    (G.Pcov * G.Lcov) (u, i) (v, j) =
      (RhatBool * G.covBlock u v) i j := by
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

private def wrapOffMat : Matrix Bool Bool ℝ :=
  fun a b => if a = b then (0 : ℝ) else -1

private lemma RhatBool_offdiag_RhatBool (i j : Bool) :
    (RhatBool * wrapOffMat * RhatBool) i j =
      if i = j then (if i = false then -2 else 2) else 0 := by
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
      · have hblk : G.covBlock u v = wrapOffMat := by
          ext a b
          rw [covBlock_wrap G u v huv hadj hw a b]
          rfl
        rw [hblk, RhatBool_offdiag_RhatBool i j]
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, if_pos rfl]
          unfold scalarLaplacian signedLaplacianMobius
          simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
                     Matrix.diagonal_apply_ne _ huv, SimpleGraph.adjMatrix_apply,
                     if_pos hadj, if_neg huv, Matrix.zero_apply, zero_sub,
                     dif_pos hadj, if_pos hw]
          cases i <;> simp
        · simp [if_neg hij]
      · have hblk : G.covBlock u v = (-1 : ℝ) • (1 : Matrix Bool Bool ℝ) :=
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
    · rw [covBlock_nonadj G u v huv hadj]
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

theorem scalarLap_cover_splits :
    ∃ (P : Matrix G.CoverV G.CoverV ℝ),
      P.det ≠ 0 ∧
      Matrix.reindex G.prodBoolEquivSum G.prodBoolEquivSum
        (P * (show Matrix G.CoverV G.CoverV ℝ from
                G.orientationDoubleCover.scalarLaplacian) * P⁻¹) =
      Matrix.fromBlocks G.scalarLaplacian 0 0 G.signedLaplacianMobius := by
  refine ⟨G.Pcov, Pcov_det_ne_zero G, ?_⟩
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

/-- **Kernel-dim corollary of L5.4** (what L8 actually uses).

The kernel of the cover's scalar Laplacian decomposes as the direct
sum of `ker(scalarLaplacian G)` (deck-invariant sections) and
`ker(signedLaplacianMobius G)` (deck-antiinvariant sections). Hence
dimensions add.

This is strictly weaker than `scalarLap_cover_splits` — it only asserts
the kernel-dim equality, not the existence of an explicit similarity `P`.
Proof strategy: the symProj/antiProj projections split `CoverV → ℝ` into
the `±1` eigenspaces of the deck involution; on each eigenspace the cover
Laplacian acts as the corresponding base Laplacian. Alternatively, derive
from `scalarLap_cover_splits` via `rank_reindex` + similarity-invariance
of kernel dim + block-diagonal kernel decomposition. -/
theorem scalarLap_cover_kernel_dim :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian)) =
      FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' G.scalarLaplacian)) +
      FiniteDimensional.finrank ℝ
          (LinearMap.ker (toLin' G.signedLaplacianMobius)) := by
  obtain ⟨P, hPdet, hreindex⟩ := G.scalarLap_cover_splits
  -- Normalize `hreindex`: the `show Matrix G.CoverV G.CoverV ℝ from ...` creates a `let_fun`
  -- that obscures the shape. `change` unfolds it to the `G.Lcov` alias.
  change Matrix.reindex G.prodBoolEquivSum G.prodBoolEquivSum
      (P * G.Lcov * P⁻¹) =
    Matrix.fromBlocks G.scalarLaplacian 0 0 G.signedLaplacianMobius at hreindex
  -- Similarity preserves kernel dim.
  have hsim :
      finrank ℝ (LinearMap.ker (Matrix.toLin' (P * G.Lcov * P⁻¹))) =
      finrank ℝ (LinearMap.ker (Matrix.toLin' G.Lcov)) :=
    finrank_ker_toLin'_conj P G.Lcov hPdet
  -- Reindex preserves kernel dim.
  have hreidx :
      finrank ℝ (LinearMap.ker (Matrix.toLin'
        (Matrix.reindex G.prodBoolEquivSum G.prodBoolEquivSum
          (P * G.Lcov * P⁻¹)))) =
      finrank ℝ (LinearMap.ker (Matrix.toLin' (P * G.Lcov * P⁻¹))) :=
    finrank_ker_toLin'_reindex G.prodBoolEquivSum _
  -- Rewrite the reindexed term as the fromBlocks RHS.
  rw [hreindex] at hreidx
  -- Block-diagonal kernel splits as a sum.
  have hsplit :=
    finrank_ker_toLin'_fromBlocks_diag (K := ℝ)
      G.scalarLaplacian G.signedLaplacianMobius
  -- Goal uses `G.orientationDoubleCover.scalarLaplacian`, `hsim` uses `G.Lcov` (defeq).
  change finrank ℝ (LinearMap.ker (toLin' G.Lcov)) = _
  linarith [hsim, hreidx, hsplit]

end ConnGraph

end ConnectionLaplacian
