/-
ConnectionLaplacian/L6_Cohomology.lean

**Stratum L6 — Z/2 Cohomology of the connection.**

The wrap predicate `wrap : edgeSet → Prop` is a 1-cocycle with
coefficients in Z/2: `σ : edgeSet → ZMod 2, σ(e) = 1 if wrap e else 0`.
Its class `[σ] ∈ H¹(G; Z/2)` is the topological obstruction to
orientability of the Z/2 line bundle defined by `wrap`.

For a connected component `C`, `[σ|_C] = 0 ∈ H¹(C; Z/2)` iff there
exists a vertex 2-coloring `ε : V(C) → Bool` with
`wrap e ↔ ε(u) ≠ ε(v)` for every edge `e = {u, v}` in `C`. Such a
component is called **balanced** (Zaslavsky / Harary-Kabell). A
component is balanced iff its orientation double cover preimage has
two disconnected sheets (equivalently: the deck action restricted to
that component fixes each sheet as a set).

The signed-Laplacian kernel dimension is `numBalancedComponents`
(proved in L8 using the L5 cover split + Mathlib scalar kernel dim).

For the pre-registered scope (n-cycle): `H¹(C_n; Z/2) = ZMod 2`, and
the class is detected by `(total wrap count in C_n) mod 2`. This is
why the original `numOddWrapComponents` formula is correct on cycles
but false in general (non-cycle connected components have
`H¹ = (ZMod 2)^(|E| − |V| + 1)` with multiple independent classes).
-/

import ConnectionLaplacian.KernelDimension
import ConnectionLaplacian.L5_Cover

namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L6.1 — The wrap cocycle -/

/-- The wrap predicate reified as a Z/2-valued 1-cochain on edges. -/
noncomputable def wrapCocycle : G.graph.edgeSet → ZMod 2 :=
  fun e => if G.wrap e then 1 else 0

/-! ### L6.2 — Balanced components via vertex 2-coloring -/

/-- A connected component `C` is **balanced** iff there is a vertex
2-coloring `ε : G.V → Bool` such that on every edge of the component,
the coloring changes sign exactly on wrap edges. Equivalently: the
restriction of the wrap cocycle to `C` is a coboundary. -/
def isBalanced (C : G.graph.ConnectedComponent) : Prop :=
  ∃ ε : G.V → Bool, ∀ (u v : G.V), ∀ (h : G.graph.Adj u v),
    G.graph.connectedComponentMk u = C →
    (G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ ↔ ε u ≠ ε v)

noncomputable instance decIsBalanced (C : G.graph.ConnectedComponent) :
    Decidable (G.isBalanced C) := Classical.dec _

/-- Number of balanced components. Corrected replacement for
`numComponents − numOddWrapComponents` — agrees with the latter on
cycle graphs but not in general. -/
noncomputable def numBalancedComponents : ℕ :=
  Fintype.card { C : G.graph.ConnectedComponent // G.isBalanced C }

/-! ### L6.3 — Bound: balanced count ≤ total component count -/

lemma numBalancedComponents_le :
    G.numBalancedComponents ≤ G.numComponents := by
  unfold numBalancedComponents numComponents
  exact Fintype.card_subtype_le _

/-! ### L6.4 — Cover-count formula (bridge to L5) -/

/-- The sheet-forgetting projection `(v, b) ↦ v`, a graph homomorphism
from the orientation double cover to the base graph. An edge in the cover
`(u, b) — (v, c)` requires `G.graph.Adj u v` (the wrap-status of the edge
only constrains `b` vs `c`), so `Prod.fst` preserves adjacency. -/
def coverProj : G.coverGraph →g G.graph where
  toFun := Prod.fst
  map_rel' := by
    rintro ⟨u, b⟩ ⟨v, c⟩ h
    -- `h : G.coverGraph.Adj (u,b) (v,c)` unfolds to `G.coverAdj (u,b) (v,c)`.
    -- The `dif_pos hadj` branch of `coverAdj` requires `G.graph.Adj u v`.
    change G.coverAdj (u, b) (v, c) at h
    unfold coverAdj at h
    by_cases hadj : G.graph.Adj u v
    · exact hadj
    · rw [dif_neg hadj] at h; exact h.elim

/-- The induced projection π₀(G̃) → π₀(G) on connected components. -/
noncomputable def componentProj :
    G.coverGraph.ConnectedComponent → G.graph.ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map G.coverProj

/-! #### Candidate lifts -/

/-- Candidate lift of the component of `v₀` on sheet `b`. -/
noncomputable def candidateLift (v₀ : G.V) (b : Bool) :
    G.coverGraph.ConnectedComponent :=
  G.coverGraph.connectedComponentMk (v₀, b)

private lemma coverProj_apply (x : G.CoverV) : G.coverProj x = x.1 := rfl

private lemma componentProj_candidateLift (v₀ : G.V) (b : Bool) :
    G.componentProj (G.candidateLift v₀ b) =
      G.graph.connectedComponentMk v₀ := by
  show ((G.coverGraph.connectedComponentMk (v₀, b)).map G.coverProj) =
         G.graph.connectedComponentMk v₀
  rw [SimpleGraph.ConnectedComponent.map_mk]
  rfl

/-! #### RS1: Path lifting (by induction on walks) -/

/-- The sheet after traversing an edge from sheet `b`. -/
noncomputable def nextSheet {u v : G.V} (h : G.graph.Adj u v) (b : Bool) : Bool :=
  if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ then !b else b

private lemma coverAdj_nextSheet {u v : G.V} (h : G.graph.Adj u v) (b : Bool) :
    G.coverAdj (u, b) (v, G.nextSheet h b) := by
  show (if h' : G.graph.Adj u v then _ else False)
  rw [dif_pos h]
  show G.wrap ⟨s(u, v), _⟩ ↔ (b ≠ G.nextSheet h b)
  unfold nextSheet
  by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
  · rw [if_pos hw]
    refine iff_of_true hw ?_
    cases b <;> decide
  · rw [if_neg hw]
    refine iff_of_false hw ?_
    intro hbad; exact hbad rfl

/-- **Path-lift core.** A base walk `u → v` lifts to a cover walk
`(u, b) → (v, b')` for some `b'` determined by wrap-parity along the walk. -/
noncomputable def walkLift :
    ∀ {u v : G.V}, G.graph.Walk u v → (b : Bool) →
      Σ b' : Bool, G.coverGraph.Walk (u, b) (v, b')
  | _, _, SimpleGraph.Walk.nil, b => ⟨b, SimpleGraph.Walk.nil⟩
  | _, _, SimpleGraph.Walk.cons (v := w) h p, b =>
      let rec_ : Σ b' : Bool, G.coverGraph.Walk (w, G.nextSheet h b) (_, b') :=
        walkLift p (G.nextSheet h b)
      ⟨rec_.1,
        SimpleGraph.Walk.cons
          (show G.coverGraph.Adj (_, b) (w, G.nextSheet h b) from
            G.coverAdj_nextSheet h b)
          rec_.2⟩

private lemma reachable_from_rep_sheet (v₀ u : G.V) (b : Bool)
    (hu : G.graph.connectedComponentMk v₀ = G.graph.connectedComponentMk u) :
    ∃ b'' : Bool, G.coverGraph.Reachable (v₀, b) (u, b'') := by
  have hreach : G.graph.Reachable v₀ u := SimpleGraph.ConnectedComponent.exact hu
  obtain ⟨p⟩ := hreach
  refine ⟨(G.walkLift p b).1, ?_⟩
  exact ⟨(G.walkLift p b).2⟩

private lemma reachable_to_rep_sheet (v₀ u : G.V) (b : Bool)
    (hu : G.graph.connectedComponentMk u = G.graph.connectedComponentMk v₀) :
    ∃ b'' : Bool, G.coverGraph.Reachable (u, b) (v₀, b'') := by
  have hreach : G.graph.Reachable u v₀ := SimpleGraph.ConnectedComponent.exact hu
  obtain ⟨p⟩ := hreach
  refine ⟨(G.walkLift p b).1, ?_⟩
  exact ⟨(G.walkLift p b).2⟩

/-! #### Fiber ⊆ two candidates -/

private lemma fiber_subset_candidates (C : G.graph.ConnectedComponent) (v₀ : G.V)
    (hv₀ : G.graph.connectedComponentMk v₀ = C)
    (D : G.coverGraph.ConnectedComponent) (hD : G.componentProj D = C) :
    D = G.candidateLift v₀ false ∨ D = G.candidateLift v₀ true := by
  revert hD
  refine SimpleGraph.ConnectedComponent.ind ?_ D
  rintro ⟨w, b⟩ hproj
  have hπ :
      G.componentProj (G.coverGraph.connectedComponentMk (w, b)) =
        G.graph.connectedComponentMk w := by
    show ((G.coverGraph.connectedComponentMk (w, b)).map G.coverProj) =
           G.graph.connectedComponentMk w
    rw [SimpleGraph.ConnectedComponent.map_mk]; rfl
  have hwC : G.graph.connectedComponentMk w = C := by
    rw [hπ] at hproj; exact hproj
  have hww₀ :
      G.graph.connectedComponentMk w = G.graph.connectedComponentMk v₀ := by
    rw [hwC, ← hv₀]
  obtain ⟨b'', hreach⟩ := G.reachable_to_rep_sheet v₀ w b hww₀
  have hcomp :
      G.coverGraph.connectedComponentMk (w, b) =
        G.coverGraph.connectedComponentMk (v₀, b'') :=
    SimpleGraph.ConnectedComponent.sound hreach
  cases b'' with
  | false => left; exact hcomp
  | true  => right; exact hcomp

/-! #### Deck helpers -/

private lemma deck_coverAdj {x y : G.CoverV}
    (h : G.coverAdj x y) : G.coverAdj (G.deck x) (G.deck y) :=
  (G.deck_adj_iff x y).mpr h

private noncomputable def coverGraph_walk_deck :
    ∀ {x y : G.CoverV}, G.coverGraph.Walk x y →
      G.coverGraph.Walk (G.deck x) (G.deck y)
  | _, _, SimpleGraph.Walk.nil => SimpleGraph.Walk.nil
  | _, _, SimpleGraph.Walk.cons h p =>
      SimpleGraph.Walk.cons
        (show G.coverGraph.Adj _ _ from G.deck_coverAdj h)
        (coverGraph_walk_deck p)

private lemma coverGraph_reachable_deck {x y : G.CoverV}
    (h : G.coverGraph.Reachable x y) :
    G.coverGraph.Reachable (G.deck x) (G.deck y) :=
  h.elim fun p => ⟨G.coverGraph_walk_deck p⟩

/-! #### RS2(a): Balanced ⇒ sheets separated -/

private lemma walk_preserves_xor_invariant
    (v₀ : G.V) (ε : G.V → Bool)
    (hε : ∀ (u v : G.V), ∀ (h : G.graph.Adj u v),
        G.graph.connectedComponentMk u = G.graph.connectedComponentMk v₀ →
        (G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ ↔ ε u ≠ ε v)) :
    ∀ {x y : G.CoverV}, G.coverGraph.Walk x y →
      G.graph.connectedComponentMk x.1 = G.graph.connectedComponentMk v₀ →
      (xor (ε x.1) x.2) = (xor (ε y.1) y.2) := by
  intro x y p
  induction p with
  | nil => intro _; rfl
  | @cons x w y hxw _ ih =>
      intro hxC
      have hxw' : G.coverAdj x w := hxw
      have hadj_base : G.graph.Adj x.1 w.1 := by
        by_contra hna
        have hfalse : G.coverAdj x w ↔ False := by
          show (if h : G.graph.Adj x.1 w.1 then _ else False) ↔ _
          rw [dif_neg hna]
        exact (hfalse.mp hxw').elim
      have hunfold : G.coverAdj x w ↔
          (G.wrap ⟨s(x.1, w.1), (SimpleGraph.mem_edgeSet G.graph).mpr hadj_base⟩ ↔
            x.2 ≠ w.2) := by
        show (if h : G.graph.Adj x.1 w.1 then _ else False) ↔ _
        rw [dif_pos hadj_base]
      have hwrap_iff :
          G.wrap ⟨s(x.1, w.1), (SimpleGraph.mem_edgeSet G.graph).mpr hadj_base⟩ ↔
            x.2 ≠ w.2 := hunfold.mp hxw'
      have hεaxiom := hε x.1 w.1 hadj_base hxC
      have hε_iff : ε x.1 ≠ ε w.1 ↔ x.2 ≠ w.2 := hεaxiom.symm.trans hwrap_iff
      have hxor_eq : xor (ε x.1) x.2 = xor (ε w.1) w.2 := by
        revert hε_iff
        cases ε x.1 <;> cases ε w.1 <;>
            cases x.2 <;> cases w.2 <;>
          intro hε_iff <;> simp_all
      have hwC : G.graph.connectedComponentMk w.1 = G.graph.connectedComponentMk v₀ := by
        have hmk := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj_base
        rw [← hmk]; exact hxC
      exact hxor_eq.trans (ih hwC)

private lemma sheets_ne_of_balanced (v₀ : G.V)
    (hbal : G.isBalanced (G.graph.connectedComponentMk v₀)) :
    G.candidateLift v₀ false ≠ G.candidateLift v₀ true := by
  intro hcollapse
  obtain ⟨ε, hε⟩ := hbal
  have hreach : G.coverGraph.Reachable (v₀, false) (v₀, true) :=
    SimpleGraph.ConnectedComponent.exact hcollapse
  obtain ⟨p⟩ := hreach
  have hxC : G.graph.connectedComponentMk (v₀, false).1 =
             G.graph.connectedComponentMk v₀ := rfl
  have hinv := G.walk_preserves_xor_invariant v₀ ε hε p hxC
  cases hεv : ε v₀ <;> simp [hεv] at hinv

/-! #### RS2(b): Sheets separated ⇒ balanced -/

private lemma unique_sheet_above
    (v₀ u : G.V)
    (hsep : G.candidateLift v₀ false ≠ G.candidateLift v₀ true)
    {b₁ b₂ : Bool}
    (h₁ : G.coverGraph.Reachable (v₀, false) (u, b₁))
    (h₂ : G.coverGraph.Reachable (v₀, false) (u, b₂)) :
    b₁ = b₂ := by
  by_contra hne
  have hflip : (!b₁) = b₂ := by
    cases b₁ <;> cases b₂ <;> first | rfl | (exact (hne rfl).elim)
  have hdeck : G.coverGraph.Reachable (v₀, true) (u, !b₁) := by
    have h := G.coverGraph_reachable_deck h₁
    simpa [deck] using h
  rw [hflip] at hdeck
  have hconnect : G.coverGraph.Reachable (v₀, false) (v₀, true) :=
    h₂.trans hdeck.symm
  exact hsep (SimpleGraph.ConnectedComponent.sound hconnect)

lemma balanced_of_sheets_separated (v₀ : G.V)
    (hsep : G.candidateLift v₀ false ≠ G.candidateLift v₀ true) :
    G.isBalanced (G.graph.connectedComponentMk v₀) := by
  classical
  let ε : G.V → Bool := fun u =>
    if h : G.graph.connectedComponentMk v₀ = G.graph.connectedComponentMk u then
      (G.reachable_from_rep_sheet v₀ u false h).choose
    else false
  have hε_reach : ∀ u, G.graph.connectedComponentMk v₀ =
        G.graph.connectedComponentMk u →
      G.coverGraph.Reachable (v₀, false) (u, ε u) := by
    intro u hu
    show G.coverGraph.Reachable (v₀, false)
        (u, if h : _ then _ else _)
    rw [dif_pos hu]
    exact (G.reachable_from_rep_sheet v₀ u false hu).choose_spec
  refine ⟨ε, ?_⟩
  intro u v hadj huC
  have huC' : G.graph.connectedComponentMk v₀ = G.graph.connectedComponentMk u :=
    huC.symm
  have hvC' : G.graph.connectedComponentMk v₀ = G.graph.connectedComponentMk v := by
    rw [huC', SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj]
  have hreach_u : G.coverGraph.Reachable (v₀, false) (u, ε u) := hε_reach u huC'
  have hreach_v : G.coverGraph.Reachable (v₀, false) (v, ε v) := hε_reach v hvC'
  have hedge : G.coverAdj (u, ε u) (v, G.nextSheet hadj (ε u)) :=
    G.coverAdj_nextSheet hadj (ε u)
  have hedge_walk : G.coverGraph.Walk (u, ε u) (v, G.nextSheet hadj (ε u)) :=
    SimpleGraph.Walk.cons
      (show G.coverGraph.Adj (u, ε u) (v, G.nextSheet hadj (ε u)) from hedge)
      SimpleGraph.Walk.nil
  have hreach_v' : G.coverGraph.Reachable (v₀, false) (v, G.nextSheet hadj (ε u)) :=
    hreach_u.trans ⟨hedge_walk⟩
  have hε_v_eq : G.nextSheet hadj (ε u) = ε v :=
    G.unique_sheet_above v₀ v hsep hreach_v' hreach_v
  unfold nextSheet at hε_v_eq
  by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
  · rw [if_pos hw] at hε_v_eq
    refine iff_of_true hw ?_
    intro heq
    rw [heq] at hε_v_eq
    cases ε v <;> simp at hε_v_eq
  · rw [if_neg hw] at hε_v_eq
    refine iff_of_false hw ?_
    intro hne
    exact hne hε_v_eq

/-! #### Main lemma -/

/-- **Fiber-cardinality lemma.** The number of connected components of
`G̃` mapping to a fixed component `C` of `G` is:
- 2 if `C` is balanced (the two sheets stay separated)
- 1 if `C` is unbalanced (the wrap non-trivialities merge the sheets).

Key direction of the proof: use a path-based construction. Pick a vertex
`v ∈ C`. Balanced ↔ (v, false) and (v, true) lie in different G̃-components
↔ the fiber has two elements rather than one. -/
lemma componentProj_fiber_card (C : G.graph.ConnectedComponent) :
    letI : DecidableEq G.graph.ConnectedComponent := Classical.decEq _
    Fintype.card
      { D : G.coverGraph.ConnectedComponent // G.componentProj D = C } =
      (if G.isBalanced C then 2 else 1) := by
  classical
  obtain ⟨v₀, hv₀⟩ :
      ∃ v₀ : G.V, G.graph.connectedComponentMk v₀ = C := Quot.exists_rep C
  subst hv₀
  let φ : Bool →
      { D : G.coverGraph.ConnectedComponent //
        G.componentProj D = G.graph.connectedComponentMk v₀ } :=
    fun b => ⟨G.candidateLift v₀ b, G.componentProj_candidateLift v₀ b⟩
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨D, hD⟩
    rcases G.fiber_subset_candidates _ v₀ rfl D hD with hD0 | hD1
    · exact ⟨false, by apply Subtype.ext; exact hD0.symm⟩
    · exact ⟨true,  by apply Subtype.ext; exact hD1.symm⟩
  by_cases hbal : G.isBalanced (G.graph.connectedComponentMk v₀)
  · have hne : G.candidateLift v₀ false ≠ G.candidateLift v₀ true :=
      G.sheets_ne_of_balanced v₀ hbal
    have hφ_inj : Function.Injective φ := by
      intro b₁ b₂ h
      have hval : G.candidateLift v₀ b₁ = G.candidateLift v₀ b₂ :=
        congrArg Subtype.val h
      cases b₁ <;> cases b₂
      · rfl
      · exact (hne hval).elim
      · exact (hne hval.symm).elim
      · rfl
    have hcard :
        Fintype.card { D : G.coverGraph.ConnectedComponent //
            G.componentProj D = G.graph.connectedComponentMk v₀ }
          = Fintype.card Bool :=
      (Fintype.card_of_bijective ⟨hφ_inj, hφ_surj⟩).symm
    simp only [if_pos hbal]
    rw [hcard]
    decide
  · have hsep_fails : ¬ (G.candidateLift v₀ false ≠ G.candidateLift v₀ true) := by
      intro hsep
      exact hbal (G.balanced_of_sheets_separated v₀ hsep)
    have heq : G.candidateLift v₀ false = G.candidateLift v₀ true := by
      by_contra h; exact hsep_fails h
    have hall_eq :
        ∀ x : { D : G.coverGraph.ConnectedComponent //
              G.componentProj D = G.graph.connectedComponentMk v₀ },
          x = φ false := by
      intro x
      obtain ⟨b, hb⟩ := hφ_surj x
      rw [← hb]
      cases b
      · rfl
      · apply Subtype.ext
        show G.candidateLift v₀ true = G.candidateLift v₀ false
        exact heq.symm
    haveI : Subsingleton { D : G.coverGraph.ConnectedComponent //
              G.componentProj D = G.graph.connectedComponentMk v₀ } :=
      ⟨fun a b => (hall_eq a).trans (hall_eq b).symm⟩
    haveI : Inhabited { D : G.coverGraph.ConnectedComponent //
              G.componentProj D = G.graph.connectedComponentMk v₀ } :=
      ⟨φ false⟩
    haveI : Unique { D : G.coverGraph.ConnectedComponent //
              G.componentProj D = G.graph.connectedComponentMk v₀ } :=
      Unique.mk' _
    simp only [if_neg hbal]
    exact Fintype.card_unique

/-- **Bridge to L5.** The number of connected components of the
orientation double cover equals `numComponents G + numBalancedComponents G`
(each balanced component lifts to 2 components; each unbalanced lifts
to 1). Used by L8 to translate Mathlib's scalar kernel-dim theorem on
`G̃` into the signed kernel-dim formula on `G`.

Proof: partition π₀(G̃) by the base projection; each fiber has size 2
(balanced) or 1 (unbalanced); sum gives `#balanced · 2 + #unbalanced · 1 =
#total + #balanced`. -/
theorem numComponents_cover :
    G.orientationDoubleCover.numComponents =
      G.numComponents + G.numBalancedComponents := by
  letI : DecidableEq G.graph.ConnectedComponent := Classical.decEq _
  show Fintype.card G.orientationDoubleCover.graph.ConnectedComponent = _
  change Fintype.card G.coverGraph.ConnectedComponent = _
  -- Step 1: π₀(G̃) ≃ Σ C : π₀(G), fiber over C, via D ↦ ⟨projD, D, rfl⟩.
  have hsig : Fintype.card G.coverGraph.ConnectedComponent =
      Fintype.card
        (Σ C : G.graph.ConnectedComponent,
            { D : G.coverGraph.ConnectedComponent // G.componentProj D = C }) := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun D => ⟨G.componentProj D, D, rfl⟩
        invFun := fun p => p.2.1
        left_inv := fun _ => rfl
        right_inv := fun ⟨_, _, hDC⟩ => by subst hDC; rfl }
  rw [hsig, Fintype.card_sigma]
  -- Step 2: replace each fiber-card with (if balanced then 2 else 1).
  simp_rw [G.componentProj_fiber_card]
  -- Step 3: combinatorial sum identity.
  unfold numComponents numBalancedComponents
  rw [show (fun C : G.graph.ConnectedComponent =>
              if G.isBalanced C then (2 : ℕ) else 1) =
          (fun C => 1 + if G.isBalanced C then 1 else 0) from
      funext (fun _ => by split_ifs <;> rfl)]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one]
  congr 1
  rw [Fintype.card_subtype]
  simp [Finset.sum_boole]

/-! ### L6.5 — Cycle-case: balanced iff even total wrap count

**Cycle corollary.** For a cycle graph (where `H¹ = ZMod 2`),
a connected component is balanced iff its total wrap count is even.
This recovers the original `numOddWrapComponents` formulation as the
correct characterization on the pre-registered (cycle) scope, so the
old `signedLaplacian_kernel_dim` statement on cycles is a corollary
of the general statement in L8.

Statement `theorem cycle_isBalanced_iff_even_wrap` TBD once the
cycle-specific `ConnGraph` construction is factored out of
`CycleSpectrum.lean`. -/

end ConnGraph

end ConnectionLaplacian
