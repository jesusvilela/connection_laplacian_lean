/-
findings/round2/prover_fiber/attempt.lean

Prover's attempt at `componentProj_fiber_card`
(`ConnectionLaplacian/L6_Cohomology.lean:104`).

Strategy: close the two residual sorries RS1 (path-lift), RS2 (balanced ↔
sheets separated), then assemble the final lemma by Bool⇄fiber equivalence.

Self-contained: imports the target file.
-/

import ConnectionLaplacian.L6_Cohomology

namespace ConnectionLaplacian

open SimpleGraph

namespace ConnGraph

variable (G : ConnGraph)

/-! ### Candidate lifts -/

/-- Candidate lift of the component of `v₀` on sheet `b`. -/
noncomputable def candidateLift (v₀ : G.V) (b : Bool) :
    G.coverGraph.ConnectedComponent :=
  G.coverGraph.connectedComponentMk (v₀, b)

lemma coverProj_apply (x : G.CoverV) : G.coverProj x = x.1 := rfl

lemma componentProj_candidateLift (v₀ : G.V) (b : Bool) :
    G.componentProj (G.candidateLift v₀ b) =
      G.graph.connectedComponentMk v₀ := by
  show ((G.coverGraph.connectedComponentMk (v₀, b)).map G.coverProj) =
         G.graph.connectedComponentMk v₀
  rw [ConnectedComponent.map_mk]
  rfl

/-! ### RS1: Path lifting (by induction on walks) -/

/-- The sheet after traversing an edge `h : Adj u v` from sheet `b`. -/
noncomputable def nextSheet {u v : G.V} (h : G.graph.Adj u v) (b : Bool) : Bool :=
  if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ then !b else b

/-- Lifted cover adjacency from base adjacency + sheet. -/
lemma coverAdj_nextSheet {u v : G.V} (h : G.graph.Adj u v) (b : Bool) :
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

/-- **RS1 core.** -/
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

lemma reachable_from_rep_sheet (v₀ u : G.V) (b : Bool)
    (hu : G.graph.connectedComponentMk v₀ = G.graph.connectedComponentMk u) :
    ∃ b'' : Bool, G.coverGraph.Reachable (v₀, b) (u, b'') := by
  have hreach : G.graph.Reachable v₀ u := ConnectedComponent.exact hu
  obtain ⟨p⟩ := hreach
  refine ⟨(G.walkLift p b).1, ?_⟩
  exact ⟨(G.walkLift p b).2⟩

lemma reachable_to_rep_sheet (v₀ u : G.V) (b : Bool)
    (hu : G.graph.connectedComponentMk u = G.graph.connectedComponentMk v₀) :
    ∃ b'' : Bool, G.coverGraph.Reachable (u, b) (v₀, b'') := by
  have hreach : G.graph.Reachable u v₀ := ConnectedComponent.exact hu
  obtain ⟨p⟩ := hreach
  refine ⟨(G.walkLift p b).1, ?_⟩
  exact ⟨(G.walkLift p b).2⟩

/-! ### Fiber ⊆ two candidates -/

lemma fiber_subset_candidates (C : G.graph.ConnectedComponent) (v₀ : G.V)
    (hv₀ : G.graph.connectedComponentMk v₀ = C)
    (D : G.coverGraph.ConnectedComponent) (hD : G.componentProj D = C) :
    D = G.candidateLift v₀ false ∨ D = G.candidateLift v₀ true := by
  revert hD
  refine ConnectedComponent.ind ?_ D
  rintro ⟨w, b⟩ hproj
  have hπ :
      G.componentProj (G.coverGraph.connectedComponentMk (w, b)) =
        G.graph.connectedComponentMk w := by
    show ((G.coverGraph.connectedComponentMk (w, b)).map G.coverProj) =
           G.graph.connectedComponentMk w
    rw [ConnectedComponent.map_mk]; rfl
  have hwC : G.graph.connectedComponentMk w = C := by
    rw [hπ] at hproj; exact hproj
  have hww₀ :
      G.graph.connectedComponentMk w = G.graph.connectedComponentMk v₀ := by
    rw [hwC, ← hv₀]
  obtain ⟨b'', hreach⟩ := G.reachable_to_rep_sheet v₀ w b hww₀
  have hcomp :
      G.coverGraph.connectedComponentMk (w, b) =
        G.coverGraph.connectedComponentMk (v₀, b'') :=
    ConnectedComponent.sound hreach
  cases b'' with
  | false => left; exact hcomp
  | true  => right; exact hcomp

/-! ### Deck helpers -/

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

/-! ### RS2(a): Balanced ⇒ sheets separated -/

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
        have hmk := ConnectedComponent.connectedComponentMk_eq_of_adj hadj_base
        rw [← hmk]; exact hxC
      exact hxor_eq.trans (ih hwC)

lemma sheets_ne_of_balanced (v₀ : G.V)
    (hbal : G.isBalanced (G.graph.connectedComponentMk v₀)) :
    G.candidateLift v₀ false ≠ G.candidateLift v₀ true := by
  intro hcollapse
  obtain ⟨ε, hε⟩ := hbal
  have hreach : G.coverGraph.Reachable (v₀, false) (v₀, true) :=
    ConnectedComponent.exact hcollapse
  obtain ⟨p⟩ := hreach
  have hxC : G.graph.connectedComponentMk (v₀, false).1 =
             G.graph.connectedComponentMk v₀ := rfl
  have hinv := G.walk_preserves_xor_invariant v₀ ε hε p hxC
  cases hεv : ε v₀ <;> simp [hεv] at hinv

/-! ### RS2(b): Sheets separated ⇒ balanced -/

private lemma unique_sheet_above
    (v₀ u : G.V)
    (hsep : G.candidateLift v₀ false ≠ G.candidateLift v₀ true)
    {b₁ b₂ : Bool}
    (h₁ : G.coverGraph.Reachable (v₀, false) (u, b₁))
    (h₂ : G.coverGraph.Reachable (v₀, false) (u, b₂)) :
    b₁ = b₂ := by
  by_contra hne
  have hflip : (!b₁) = b₂ := by
    cases b₁ <;> cases b₂ <;> first | rfl | (exact (hne rfl).elim) | decide
  have hdeck : G.coverGraph.Reachable (v₀, true) (u, !b₁) := by
    have h := G.coverGraph_reachable_deck h₁
    simpa [deck] using h
  rw [hflip] at hdeck
  have hconnect : G.coverGraph.Reachable (v₀, false) (v₀, true) :=
    h₂.trans hdeck.symm
  exact hsep (ConnectedComponent.sound hconnect)

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
    rw [huC', ConnectedComponent.connectedComponentMk_eq_of_adj hadj]
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

/-! ### Main lemma -/

lemma componentProj_fiber_card_proved (C : G.graph.ConnectedComponent) :
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

end ConnGraph
end ConnectionLaplacian
