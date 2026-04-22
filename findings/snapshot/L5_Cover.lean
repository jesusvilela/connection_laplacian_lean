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

open Matrix BigOperators
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

**Proof sketch (not yet formalized).** Use `RhatBool : Matrix Bool Bool ℝ`
(the 2×2 Hadamard), lift to `P = (1 : Matrix V V ℝ) ⊗ᵏ RhatBool` via the
Kronecker product. Then `P * L̃ * P⁻¹`, when reindexed through
`prodBoolEquivSum`, has off-diagonal blocks that vanish entry-wise
(wrap/no-wrap entries interfere destructively), leaving the `fromBlocks`
shape on the diagonal. This mirrors the pattern used to close the
Möbius branch of `laplacian_decomposes` in `KernelDimension.lean`. -/
theorem scalarLap_cover_splits :
    ∃ (P : Matrix G.CoverV G.CoverV ℝ),
      P.det ≠ 0 ∧
      Matrix.reindex G.prodBoolEquivSum G.prodBoolEquivSum
        (P * G.orientationDoubleCover.scalarLaplacian * P⁻¹) =
      Matrix.fromBlocks G.scalarLaplacian 0 0 G.signedLaplacianMobius := by
  sorry

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
  sorry

end ConnGraph

end ConnectionLaplacian
