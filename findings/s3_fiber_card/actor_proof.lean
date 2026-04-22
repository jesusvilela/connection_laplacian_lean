/-
findings/s3_fiber_card/actor_proof.lean

Candidate proof for `componentProj_fiber_card` in
`ConnectionLaplacian/L6_Cohomology.lean` (line 104).

Live source is NOT modified. This is a candidate written for review.

Strategy (standard orientation double cover fiber theorem):
  For a fixed base component `C`, pick a representative vertex
  `v₀ ∈ C`. The fiber over `C` is exactly
    { componentMk (v₀, false),  componentMk (v₀, true) }
  as a two-element (possibly collapsed) set inside
  `G.coverGraph.ConnectedComponent`. Moreover
    componentMk (v₀, false) = componentMk (v₀, true)
        ↔  G.coverGraph.Reachable (v₀, false) (v₀, true)
        ↔  C is *un*balanced.

So the fiber has 2 elements if `C` is balanced and 1 element otherwise,
matching the RHS `if G.isBalanced C then 2 else 1`.

Residual sorries. Only two pieces of nontrivial path/coloring
combinatorics are left open; both are honestly named so the caller can
slot them in later without disturbing the overall shape. See
`actor_notes.md` for details.

  (RS1)  `reachable_to_rep_sheet` —
         path-lift: `(w, b)` in cover reaches some `(v₀, b'')`.
  (RS2)  `sheets_merge_iff_unbalanced` —
         `(v₀, false) ~_cover (v₀, true)  ↔  ¬ G.isBalanced C`.
-/

import ConnectionLaplacian.L6_Cohomology

namespace ConnectionLaplacian
namespace ConnGraph

open SimpleGraph

variable (G : ConnGraph)

/-! ### Step 1. Two candidate lifts of a component.

For a representative vertex `v₀ : G.V` we pick the two cover-components
containing `(v₀, false)` and `(v₀, true)`. Both project to the base
component of `v₀`. -/

/-- The candidate lift of the component of `v₀` on the `b` sheet. -/
noncomputable def candidateLift (v₀ : G.V) (b : Bool) :
    G.coverGraph.ConnectedComponent :=
  G.coverGraph.connectedComponentMk (v₀, b)

lemma coverProj_apply (x : G.CoverV) : G.coverProj x = x.1 := rfl

lemma componentProj_candidateLift (v₀ : G.V) (b : Bool) :
    G.componentProj (G.candidateLift v₀ b) =
      G.graph.connectedComponentMk v₀ := by
  -- By definitional unfolding:
  --   componentProj (candidateLift v₀ b)
  --     = (connectedComponentMk (v₀, b)).map coverProj
  --     = connectedComponentMk (coverProj (v₀, b))   [by `map_mk`]
  --     = connectedComponentMk v₀.
  show ((G.coverGraph.connectedComponentMk (v₀, b)).map G.coverProj) =
         G.graph.connectedComponentMk v₀
  rw [ConnectedComponent.map_mk, G.coverProj_apply]

/-! ### Step 2. Path-lift core lemma.

For a vertex `w` in the same base component as `v₀`, the cover vertex
`(w, b)` is reachable (in the cover graph) to `(v₀, b')` for some
`b' : Bool`. This is the path-lift lemma: a walk in `G` from `w` to `v₀`
lifts to a walk in `G̃` starting at any sheet, with the ending sheet
determined by the wrap-parity along the walk.

We state this as an existence result because all we need downstream is
"some sheet works".

**Status: residual sorry (RS1) — see `actor_notes.md`.** A full
formalisation proceeds by induction on the base walk:

    * `Walk.nil` : take `b' := b`; the lifted walk is `Walk.nil`.
    * `Walk.cons h p` from `w` to `v₀`, with first edge `{w, x}`:
        Inductively lift `p : G.Walk x v₀` starting at sheet `b_x`
        where `b_x = b` if the edge is non-wrap, else `!b`.
        Then `coverAdj (w, b) (x, b_x)` holds by construction, so
        `Walk.cons` in the cover gives a lift starting at `(w, b)` and
        ending where the recursion ends.
-/

/-- Path-lift reachability: any cover vertex `(w, b)` with `w` in the
base component of `v₀` is reachable to `(v₀, b'')` on some sheet `b''`. -/
lemma reachable_to_rep_sheet (v₀ w : G.V) (b : Bool)
    (hw : G.graph.connectedComponentMk w = G.graph.connectedComponentMk v₀) :
    ∃ b'' : Bool, G.coverGraph.Reachable (w, b) (v₀, b'') := by
  -- RS1: path lift by induction on a base walk w → v₀.
  -- Strategy sketch (not yet closed):
  --   obtain ⟨p⟩ := (ConnectedComponent.eq.mp hw)
  --   refine (walk_lift p b).elim fun b'' q => ⟨b'', q.reachable⟩
  -- where `walk_lift` is proved by `induction p`.
  sorry

/-! ### Step 3. The fiber is contained in the two candidates. -/

/-- Any cover-component projecting to `C` equals one of the two candidate
lifts of a chosen representative. -/
lemma fiber_subset_candidates (C : G.graph.ConnectedComponent) (v₀ : G.V)
    (hv₀ : G.graph.connectedComponentMk v₀ = C)
    (D : G.coverGraph.ConnectedComponent) (hD : G.componentProj D = C) :
    D = G.candidateLift v₀ false ∨ D = G.candidateLift v₀ true := by
  -- Peel off the quotient representative of `D`. We use `ConnectedComponent.ind`
  -- after generalising `hD` so that the induction target is propositional.
  revert hD
  refine ConnectedComponent.ind ?_ D
  rintro ⟨w, b⟩ hproj
  -- `componentProj (mk (w,b)) = mk w`, so `mk w = C = mk v₀`.
  have hπ :
      G.componentProj (G.coverGraph.connectedComponentMk (w, b)) =
        G.graph.connectedComponentMk w := by
    show ((G.coverGraph.connectedComponentMk (w, b)).map G.coverProj) =
           G.graph.connectedComponentMk w
    rw [ConnectedComponent.map_mk, G.coverProj_apply]
  have hwC : G.graph.connectedComponentMk w = C := by
    rw [hπ] at hproj; exact hproj
  have hww₀ :
      G.graph.connectedComponentMk w = G.graph.connectedComponentMk v₀ := by
    rw [hwC, ← hv₀]
  -- Path-lift: `(w, b)` reaches `(v₀, b'')` for some `b''`.
  obtain ⟨b'', hreach⟩ := G.reachable_to_rep_sheet v₀ w b hww₀
  have hcomp :
      G.coverGraph.connectedComponentMk (w, b) =
        G.coverGraph.connectedComponentMk (v₀, b'') :=
    ConnectedComponent.sound hreach
  -- Split on `b''` to pick the corresponding candidate.
  -- `candidateLift v₀ b'' := connectedComponentMk (v₀, b'')` by definition.
  cases b'' with
  | false =>
      left
      show G.coverGraph.connectedComponentMk (w, b) = G.candidateLift v₀ false
      exact hcomp
  | true  =>
      right
      show G.coverGraph.connectedComponentMk (w, b) = G.candidateLift v₀ true
      exact hcomp

/-! ### Step 4. Characterisation of sheet-merge by balancedness.

The two candidate lifts of `v₀` are equal iff `(v₀, false)` and
`(v₀, true)` lie in the same connected component of `G̃` iff there is a
walk between them in the cover iff `C` is *un*balanced.

**Status: residual sorry (RS2) — see `actor_notes.md`.** The two
directions:

  * Unbalanced ⇒ merge. If `C` is unbalanced, every vertex 2-coloring
    `ε : V → Bool` fails on some edge of `C`: there exist adjacent
    `u, v ∈ C` with `(G.wrap {u,v}) ↔ (ε u = ε v)`. A careful induction
    on a walk `v₀ → v₀` passing through such a failure edge lifts to
    a walk in the cover flipping sheets an odd number of times, giving
    a cover-walk `(v₀, false) → (v₀, true)`.

  * Balanced ⇒ separated. If `ε` is a balanced 2-coloring of `C`, define
    `f : G̃.V → Bool` by `f (u, c) := ε u != c` on vertices above `C`
    (and anything on other vertices). Any cover-edge `(u, c) — (u', c')`
    with `u, u' ∈ C` preserves `f`: the edge equation says
    `G.wrap e ↔ c ≠ c'`, and `ε`'s coloring axiom says
    `G.wrap e ↔ ε u ≠ ε u'`, hence `ε u != c = ε u' != c'`. Thus `f` is
    constant along cover-walks inside `π^{-1}(C)`; but `f (v₀, false) =
    ε v₀` and `f (v₀, true) = !ε v₀`, contradicting equality.
-/

/-- The two candidate lifts coincide iff the underlying component is
unbalanced. This is the deep direction of the fiber-size theorem. -/
lemma sheets_merge_iff_unbalanced (v₀ : G.V) :
    G.candidateLift v₀ false = G.candidateLift v₀ true ↔
      ¬ G.isBalanced (G.graph.connectedComponentMk v₀) := by
  -- RS2: see sketch in comment block above.
  sorry

/-! ### Step 5. Fiber cardinality, assembled.

Given the three ingredients
  (A) `componentProj_candidateLift`  — both candidates are in the fiber,
  (B) `fiber_subset_candidates`       — nothing else is in the fiber,
  (C) `sheets_merge_iff_unbalanced`   — the two candidates collapse iff
                                       `C` is unbalanced,
we build an explicit equivalence between the fiber and `Bool` (balanced
case) or `Unit` (unbalanced case), and compute the cardinality.
-/

/-- **Candidate proof of the target theorem.** -/
lemma componentProj_fiber_card_candidate (C : G.graph.ConnectedComponent) :
    Fintype.card
      { D : G.coverGraph.ConnectedComponent // G.componentProj D = C } =
      (if G.isBalanced C then 2 else 1) := by
  classical
  -- Choose a representative vertex `v₀` of `C`.
  obtain ⟨v₀, hv₀⟩ :
      ∃ v₀ : G.V, G.graph.connectedComponentMk v₀ = C := Quot.exists_rep C
  subst hv₀
  -- Shorthand: membership witnesses.
  have hD₀_mem :
      G.componentProj (G.candidateLift v₀ false) =
        G.graph.connectedComponentMk v₀ :=
    G.componentProj_candidateLift v₀ false
  have hD₁_mem :
      G.componentProj (G.candidateLift v₀ true) =
        G.graph.connectedComponentMk v₀ :=
    G.componentProj_candidateLift v₀ true
  -- The function `Bool → fiber` that sends `b` to the candidate lift.
  let φ : Bool →
      { D : G.coverGraph.ConnectedComponent //
        G.componentProj D = G.graph.connectedComponentMk v₀ } :=
    fun b => ⟨G.candidateLift v₀ b, G.componentProj_candidateLift v₀ b⟩
  -- It is surjective (by `fiber_subset_candidates`).
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨D, hD⟩
    rcases G.fiber_subset_candidates _ v₀ rfl D hD with hD0 | hD1
    · exact ⟨false, by apply Subtype.ext; exact hD0.symm⟩
    · exact ⟨true,  by apply Subtype.ext; exact hD1.symm⟩
  by_cases hbal : G.isBalanced (G.graph.connectedComponentMk v₀)
  · -- Balanced: φ is also injective.
    have hne : G.candidateLift v₀ false ≠ G.candidateLift v₀ true :=
      fun heq => (G.sheets_merge_iff_unbalanced v₀).mp heq hbal
    have hφ_inj : Function.Injective φ := by
      intro b₁ b₂ h
      have hval : G.candidateLift v₀ b₁ = G.candidateLift v₀ b₂ :=
        congrArg Subtype.val h
      cases b₁ <;> cases b₂
      · rfl
      · exact (hne hval).elim
      · exact (hne hval.symm).elim
      · rfl
    -- `Fintype.card fiber = Fintype.card Bool = 2`.
    have hcard :
        Fintype.card { D : G.coverGraph.ConnectedComponent //
            G.componentProj D = G.graph.connectedComponentMk v₀ }
          = Fintype.card Bool :=
      (Fintype.card_of_bijective ⟨hφ_inj, hφ_surj⟩).symm
    rw [if_pos hbal, hcard]
    decide
  · -- Unbalanced: φ is constant (both sheets give the same component),
    -- so the fiber has exactly one element.
    have heq : G.candidateLift v₀ false = G.candidateLift v₀ true :=
      (G.sheets_merge_iff_unbalanced v₀).mpr hbal
    -- Every element of the fiber equals φ false.
    have hall_eq :
        ∀ x : { D : G.coverGraph.ConnectedComponent //
              G.componentProj D = G.graph.connectedComponentMk v₀ },
          x = φ false := by
      intro x
      obtain ⟨b, hb⟩ := hφ_surj x
      rw [← hb]
      cases b
      · rfl
      · -- φ true = φ false because candidateLifts coincide.
        apply Subtype.ext
        show G.candidateLift v₀ true = G.candidateLift v₀ false
        exact heq.symm
    -- Hence the fiber is a Unique type (subsingleton + inhabited), card = 1.
    haveI : Subsingleton { D : G.coverGraph.ConnectedComponent //
              G.componentProj D = G.graph.connectedComponentMk v₀ } :=
      ⟨fun a b => (hall_eq a).trans (hall_eq b).symm⟩
    haveI : Inhabited { D : G.coverGraph.ConnectedComponent //
              G.componentProj D = G.graph.connectedComponentMk v₀ } :=
      ⟨φ false⟩
    haveI : Unique { D : G.coverGraph.ConnectedComponent //
              G.componentProj D = G.graph.connectedComponentMk v₀ } :=
      Unique.mk' _
    rw [if_neg hbal]
    exact Fintype.card_unique

end ConnGraph
end ConnectionLaplacian
