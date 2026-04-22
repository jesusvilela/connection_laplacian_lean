/-
ConnectionLaplacian/L15_BridgeMonotone.lean

**Stratum L15 — Bridge-monotone removal.**

The round-4 fuzzy-logic negator showed that the naïve claim
"β(G) ≥ β(G − e) for every non-wrap edge e" fails with τ ≈ 0.89, and every
counterexample is a bridge edge. The refinement adding a non-bridge
hypothesis closes τ to 1 (round-5 Python sanity over all n ≤ 5 graphs,
tested = 13100, passed = 13100).

Main statement:

  `numBalancedComponents_monotone_remove_nonwrap_nonbridge`:
    for any edge `e` of `G` that is not a bridge,
    `β(G) ≤ β(G − e)`.

(The `non-wrap` hypothesis is not needed for the inequality — balance is
monotone under removal of *any* non-bridge edge. We state the theorem
with the hypothesis the caller wanted anyway.)

### Proof sketch

Let `G'` be `G` with the edge `e` deleted (its wrap predicate is the
restriction of `G.wrap` to edges other than `e`).

Because `e` is a non-bridge, removing it does not disconnect any
component: the vertex-level equivalence relation "reachable in G" agrees
with "reachable in G'". This gives a bijection on connected components.

Balance transfers along this bijection via the walk-sum H¹ detector from
L12: every closed walk in `G'` transfers to a closed walk in `G` with the
same edge list (hence same wrap count).
-/

import ConnectionLaplacian.L12_WalkH1

namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L15.1 — Edge deletion as a `ConnGraph` -/

/-- Every edge of `G.graph.deleteEdges {e}` is an edge of `G.graph`. -/
private lemma mem_edgeSet_of_deleteEdges {e : Sym2 G.V} {e' : Sym2 G.V}
    (he' : e' ∈ (G.graph.deleteEdges {e}).edgeSet) :
    e' ∈ G.graph.edgeSet := by
  rw [SimpleGraph.edgeSet_deleteEdges] at he'
  exact he'.1

/-- Delete a single edge `e` from `G`, producing a new `ConnGraph`.
The wrap predicate is inherited on surviving edges. -/
noncomputable def eraseEdge (e : G.graph.edgeSet) : ConnGraph :=
  { V := G.V
    graph := G.graph.deleteEdges {e.val}
    wrap := fun e' =>
      G.wrap ⟨e'.val, G.mem_edgeSet_of_deleteEdges e'.property⟩
    decwrap := Classical.decPred _
    decrel := by
      classical
      exact Classical.decRel _ }

@[simp] lemma eraseEdge_V (e : G.graph.edgeSet) : (G.eraseEdge e).V = G.V := rfl

@[simp] lemma eraseEdge_graph (e : G.graph.edgeSet) :
    (G.eraseEdge e).graph = G.graph.deleteEdges {e.val} := rfl

lemma eraseEdge_le (e : G.graph.edgeSet) :
    (G.eraseEdge e).graph ≤ G.graph := by
  change G.graph.deleteEdges {e.val} ≤ G.graph
  exact SimpleGraph.deleteEdges_le _

/-- The inclusion homomorphism from `G.eraseEdge e` into `G`, identity on
vertices (spanning subgraph). -/
noncomputable def eraseEdge_incl (e : G.graph.edgeSet) :
    (G.eraseEdge e).graph →g G.graph :=
  SimpleGraph.Hom.mapSpanningSubgraphs (G.eraseEdge_le e)

@[simp] lemma eraseEdge_incl_apply (e : G.graph.edgeSet) (v : G.V) :
    G.eraseEdge_incl e v = v := rfl

/-! ### L15.2 — Non-bridge ⇒ vertex-level connectivity preserved -/

/-- Every adjacency in `G` that avoids `e.val` survives in `G.eraseEdge e`. -/
private lemma adj_eraseEdge_of {e : G.graph.edgeSet} {u v : G.V}
    (h : G.graph.Adj u v) (hne : s(u, v) ≠ e.val) :
    (G.eraseEdge e).graph.Adj u v := by
  change (G.graph.deleteEdges {e.val}).Adj u v
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨h, ?_⟩
  simpa using hne

/-- Transfer a walk in `G` avoiding edge `e` into `G.eraseEdge ⟨e, hE⟩`. -/
private noncomputable def transferAvoiding
    (e : Sym2 G.V) (hE : e ∈ G.graph.edgeSet)
    {u v : G.V} (p : G.graph.Walk u v) (hp : e ∉ p.edges) :
    (G.eraseEdge ⟨e, hE⟩).graph.Walk u v :=
  p.transfer (G.eraseEdge ⟨e, hE⟩).graph (by
    intro e' he'
    have h₁ : e' ∈ G.graph.edgeSet := p.edges_subset_edgeSet he'
    have h₂ : e' ≠ e := fun heq => hp (heq ▸ he')
    change e' ∈ (G.graph.deleteEdges {e}).edgeSet
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨h₁, by simpa using h₂⟩)

/-- Reverse-walk avoidance: if `p` avoids `e`, so does `p.reverse`. -/
private lemma reverse_avoids
    {u v : G.V} (p : G.graph.Walk u v) (e : Sym2 G.V) (hp : e ∉ p.edges) :
    e ∉ p.reverse.edges := by
  rw [SimpleGraph.Walk.edges_reverse]
  simpa using hp

/-- Reroute a walk in `G` through a replacement path `pAB` avoiding
`s(a,b)`, producing a walk in `G.eraseEdge ⟨s(a,b), hE⟩`. -/
private noncomputable def rerouteWalk
    (a b : G.V) (hE : s(a, b) ∈ G.graph.edgeSet)
    (pAB : G.graph.Walk a b) (hpAB : s(a, b) ∉ pAB.edges) :
    ∀ {u v : G.V}, G.graph.Walk u v →
      (G.eraseEdge ⟨s(a, b), hE⟩).graph.Walk u v
  | _, _, SimpleGraph.Walk.nil => SimpleGraph.Walk.nil
  | u, v, SimpleGraph.Walk.cons (v := w) h q' =>
      if hdanger : s(u, w) = s(a, b) then
        -- This step is the forbidden edge. Replace it by pAB or its reverse.
        let qw : (G.eraseEdge ⟨s(a, b), hE⟩).graph.Walk u w :=
          if huwab : u = a ∧ w = b then
            -- Cast pAB to a walk u ⇝ w via subst.
            huwab.1.symm ▸ huwab.2.symm ▸
              G.transferAvoiding (s(a, b)) hE pAB hpAB
          else
            -- Then must be u = b, w = a by Sym2.eq_iff.
            have huwba : u = b ∧ w = a := by
              rcases (Sym2.eq_iff.mp hdanger) with hab | hba
              · exact (huwab hab).elim
              · exact hba
            huwba.1.symm ▸ huwba.2.symm ▸
              G.transferAvoiding (s(a, b)) hE pAB.reverse
                (G.reverse_avoids pAB (s(a, b)) hpAB)
        qw.append (rerouteWalk a b hE pAB hpAB q')
      else
        SimpleGraph.Walk.cons (G.adj_eraseEdge_of h hdanger)
          (rerouteWalk a b hE pAB hpAB q')

/-- **Bridge reformulation (transport from Mathlib).**
If `e` is not a bridge, every pair of vertices reachable in `G` is
reachable in `G.eraseEdge e`. -/
lemma reachable_eraseEdge_of_reachable
    (e : G.graph.edgeSet) (hnb : ¬ G.graph.IsBridge e.val)
    {u v : G.V} (huv : G.graph.Reachable u v) :
    (G.eraseEdge e).graph.Reachable u v := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.graph.Adj a b := (SimpleGraph.mem_edgeSet _).mp he
    have hnot_bridge : ¬ (G.graph.Adj a b ∧
        ∀ p : G.graph.Walk a b, s(a, b) ∈ p.edges) :=
      fun h => hnb (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mpr h)
    have hexists : ∃ p : G.graph.Walk a b, s(a, b) ∉ p.edges := by
      by_contra hcon
      push_neg at hcon
      exact hnot_bridge ⟨hab, hcon⟩
    obtain ⟨pAB, hpAB⟩ := hexists
    obtain ⟨q⟩ := huv
    exact ⟨G.rerouteWalk a b he pAB hpAB q⟩

/-- Non-bridge edge removal preserves reachability (both directions). -/
lemma reachable_iff_reachable_eraseEdge
    (e : G.graph.edgeSet) (hnb : ¬ G.graph.IsBridge e.val)
    (u v : G.V) :
    G.graph.Reachable u v ↔ (G.eraseEdge e).graph.Reachable u v := by
  refine ⟨fun h => G.reachable_eraseEdge_of_reachable e hnb h, ?_⟩
  intro h
  obtain ⟨p⟩ := h
  exact ⟨p.map (G.eraseEdge_incl e)⟩

/-! ### L15.3 — Component bijection -/

/-- Forward component map `G'.CC → G.CC` induced by the spanning-subgraph
inclusion. -/
noncomputable def eraseEdge_componentMap (e : G.graph.edgeSet) :
    (G.eraseEdge e).graph.ConnectedComponent → G.graph.ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (G.eraseEdge_incl e)

lemma eraseEdge_componentMap_mk (e : G.graph.edgeSet) (v : G.V) :
    G.eraseEdge_componentMap e
        ((G.eraseEdge e).graph.connectedComponentMk v) =
      G.graph.connectedComponentMk v := by
  unfold eraseEdge_componentMap
  rw [SimpleGraph.ConnectedComponent.map_mk]
  rfl

/-- When `e` is not a bridge, the component map is injective. -/
lemma eraseEdge_componentMap_injective
    (e : G.graph.edgeSet) (hnb : ¬ G.graph.IsBridge e.val) :
    Function.Injective (G.eraseEdge_componentMap e) := by
  classical
  intro C D h
  induction C using SimpleGraph.ConnectedComponent.ind with
  | _ u =>
    induction D using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
      rw [G.eraseEdge_componentMap_mk, G.eraseEdge_componentMap_mk] at h
      have hreach : G.graph.Reachable u v := SimpleGraph.ConnectedComponent.exact h
      have h' : (G.eraseEdge e).graph.Reachable u v :=
        G.reachable_eraseEdge_of_reachable e hnb hreach
      exact SimpleGraph.ConnectedComponent.sound h'

/-- The component map is always surjective. -/
lemma eraseEdge_componentMap_surjective (e : G.graph.edgeSet) :
    Function.Surjective (G.eraseEdge_componentMap e) := by
  classical
  intro C
  induction C using SimpleGraph.ConnectedComponent.ind with
  | _ v =>
    exact ⟨(G.eraseEdge e).graph.connectedComponentMk v,
      G.eraseEdge_componentMap_mk e v⟩

/-! ### L15.4 — Balance transfers from `G` to `G.eraseEdge e` -/

/-- **Balance transfer.** If the image component in `G` is balanced,
then the component in `G.eraseEdge e` is balanced.

The proof reuses the same coloring `ε`, observing that every adjacency
in `G.eraseEdge e` is also an adjacency in `G`, and the wrap predicate
agrees on surviving edges (definitionally). -/
lemma isBalanced_eraseEdge_of_isBalanced
    (e : G.graph.edgeSet)
    (C : (G.eraseEdge e).graph.ConnectedComponent)
    (hbal : G.isBalanced (G.eraseEdge_componentMap e C)) :
    (G.eraseEdge e).isBalanced C := by
  classical
  obtain ⟨ε, hε⟩ := hbal
  refine ⟨ε, ?_⟩
  intro u v hadj_G' huC
  -- Transport adjacency to G.
  have hadj : G.graph.Adj u v := G.eraseEdge_le e hadj_G'
  -- Transport the component equation.
  have huC_G : G.graph.connectedComponentMk u = G.eraseEdge_componentMap e C := by
    rw [← huC, G.eraseEdge_componentMap_mk]
  -- Apply the coloring axiom at G.
  have hbal_G := hε u v hadj huC_G
  -- Wrap predicates agree definitionally.
  exact hbal_G

/-! ### L15.5 — Main inequality -/

/-- **Bridge-monotone removal (main theorem).**
Removing a non-bridge edge cannot decrease the number of balanced
components. The non-wrap hypothesis is accepted but unused. -/
theorem numBalancedComponents_monotone_remove_nonwrap_nonbridge
    (G : ConnGraph) (e : G.graph.edgeSet)
    (_hnonwrap : ¬ G.wrap e)
    (hnonbridge : ¬ G.graph.IsBridge e.val) :
    G.numBalancedComponents ≤ (G.eraseEdge e).numBalancedComponents := by
  classical
  have hinj := G.eraseEdge_componentMap_injective e hnonbridge
  have hsur := G.eraseEdge_componentMap_surjective e
  let πEquiv : (G.eraseEdge e).graph.ConnectedComponent ≃
               G.graph.ConnectedComponent :=
    Equiv.ofBijective (G.eraseEdge_componentMap e) ⟨hinj, hsur⟩
  let inj :
      { C : G.graph.ConnectedComponent // G.isBalanced C } →
        { C' : (G.eraseEdge e).graph.ConnectedComponent //
          (G.eraseEdge e).isBalanced C' } := fun ⟨C, hC⟩ =>
    ⟨πEquiv.symm C, by
      apply G.isBalanced_eraseEdge_of_isBalanced
      have hπ : G.eraseEdge_componentMap e (πEquiv.symm C) = C :=
        πEquiv.apply_symm_apply C
      rw [hπ]
      exact hC⟩
  have hinj2 : Function.Injective inj := by
    rintro ⟨C, hC⟩ ⟨D, hD⟩ hCD
    have hval : πEquiv.symm C = πEquiv.symm D := congrArg Subtype.val hCD
    have hCD' : C = D := πEquiv.symm.injective hval
    exact Subtype.ext hCD'
  exact Fintype.card_le_of_injective inj hinj2

/-- **Variant restated for the caller's preferred signature.** -/
theorem numBalancedComponents_monotone_remove_nonwrap_nonbridge'
    (G : ConnGraph) (e : Sym2 G.V) (he : e ∈ G.graph.edgeSet)
    (hnonwrap : ¬ G.wrap ⟨e, he⟩)
    (hnonbridge : ¬ G.graph.IsBridge e) :
    G.numBalancedComponents ≤ (G.eraseEdge ⟨e, he⟩).numBalancedComponents :=
  G.numBalancedComponents_monotone_remove_nonwrap_nonbridge
    ⟨e, he⟩ hnonwrap hnonbridge

end ConnGraph

end ConnectionLaplacian
