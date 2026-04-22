/-
ConnectionLaplacian/L12_WalkH1.lean

**Stratum L12 — Walk-sum H¹ detector.**

A connected component `C` of a connection graph `G` is balanced iff every
closed walk within `C` traverses an even number of wrap edges.

Proof structure:
* (⇒) Project a base walk `p : u ⇝ v` to an identity on ε: for every step
      `{u, x}`, the balance axiom gives `wrap ↔ ε u ≠ ε x`. Induction on `p`
      shows `xor (ε u) (ε v) = parity(walkWrapCount p)`. A closed walk at v
      has `xor = false`, i.e. even wrap count.
* (⇐) Project any cover walk `(v₀, false) ⇝ (v₀, true)` down to a closed
      walk in the base. The sheet XOR of the cover walk's endpoints equals
      the wrap parity of the projected walk (because each cover edge flips
      sheet iff it lies over a wrap edge). Sheet XOR = true ⇒ projected
      walk is odd. If every closed walk is even, no such cover walk
      exists, so the two candidate lifts are distinct, and
      `L6.componentProj_fiber_card` concludes.

Because `balanced_of_sheets_separated` is `private` in L6, we re-prove a
thin shim through its public sibling `componentProj_fiber_card`.
-/

import ConnectionLaplacian.L6_Cohomology

namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L12.1 — The walk wrap-count predicate -/

/-- Edge-level predicate (Bool-valued): `e` is a wrap edge of `G`. -/
def wrapEdgeBool (e : Sym2 G.V) : Bool :=
  decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩)

private lemma wrapEdgeBool_iff_wrap {u v : G.V} (h : G.graph.Adj u v) :
    G.wrapEdgeBool s(u, v) = true ↔
      G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ := by
  unfold wrapEdgeBool
  rw [decide_eq_true_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, hw⟩; exact hw
  · intro hw; exact ⟨_, hw⟩

/-- Wrap count of a walk: the number of wrap edges it traverses
(with multiplicity). -/
noncomputable def walkWrapCount {u v : G.V} (p : G.graph.Walk u v) : ℕ :=
  p.edges.countP G.wrapEdgeBool

@[simp] lemma walkWrapCount_nil (u : G.V) :
    G.walkWrapCount (SimpleGraph.Walk.nil : G.graph.Walk u u) = 0 := by
  simp [walkWrapCount]

@[simp] lemma walkWrapCount_cons {u v w : G.V} (h : G.graph.Adj u v)
    (p : G.graph.Walk v w) :
    G.walkWrapCount (SimpleGraph.Walk.cons h p) =
      (if G.wrapEdgeBool s(u, v) then 1 else 0) + G.walkWrapCount p := by
  simp only [walkWrapCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
  ring

/-- Parity of a Nat as a Bool (uses `Nat.bodd`). -/
private def natParity (n : ℕ) : Bool := n.bodd

private lemma natParity_zero : natParity 0 = false := rfl

private lemma natParity_add (m n : ℕ) :
    natParity (m + n) = xor (natParity m) (natParity n) := by
  unfold natParity; rw [Nat.bodd_add]

private lemma natParity_one : natParity 1 = true := rfl

private lemma even_iff_natParity_false (n : ℕ) :
    Even n ↔ natParity n = false := by
  unfold natParity
  rw [Nat.even_iff]
  constructor
  · intro h
    have key : n.bodd = (n % 2).bodd := by
      conv_lhs => rw [← Nat.mod_add_div n 2]
      rw [Nat.bodd_add]
      simp [Nat.bodd_mul]
    rw [key, h]; rfl
  · intro h
    have : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
    rcases this with heq | heq
    · exact heq
    · exfalso
      have htrue : n.bodd = true := by
        have key : n.bodd = (n % 2).bodd := by
          conv_lhs => rw [← Nat.mod_add_div n 2]
          rw [Nat.bodd_add]; simp [Nat.bodd_mul]
        rw [key, heq]; rfl
      rw [htrue] at h
      exact absurd h (by decide)

/-! ### L12.2 — Project a cover walk, track wrap parity -/

/-- Project a cover walk to a base walk (drop sheet coordinates). -/
noncomputable def projectCoverWalk :
    ∀ {x y : G.CoverV}, G.coverGraph.Walk x y → G.graph.Walk x.1 y.1
  | _, _, SimpleGraph.Walk.nil => SimpleGraph.Walk.nil
  | (u, b), _, SimpleGraph.Walk.cons (v := w) h p =>
      have hadj_base : G.graph.Adj u w.1 := by
        have hxw' : G.coverAdj (u, b) w := h
        by_contra hna
        have hfalse : G.coverAdj (u, b) w ↔ False := by
          show (if h' : G.graph.Adj u w.1 then _ else False) ↔ _
          rw [dif_neg hna]
        exact (hfalse.mp hxw').elim
      SimpleGraph.Walk.cons hadj_base (projectCoverWalk p)

/-- The wrap count parity of the projected walk equals the sheet-XOR of the
cover walk's endpoints. -/
lemma projectCoverWalk_wrap_parity :
    ∀ {x y : G.CoverV} (q : G.coverGraph.Walk x y),
      natParity (G.walkWrapCount (G.projectCoverWalk q)) = xor x.2 y.2
  | (u, b), (_, _), SimpleGraph.Walk.nil => by
      show natParity (G.walkWrapCount (G.projectCoverWalk
        (SimpleGraph.Walk.nil : G.coverGraph.Walk (u, b) (u, b)))) = _
      show natParity (G.walkWrapCount (SimpleGraph.Walk.nil)) = xor b b
      rw [G.walkWrapCount_nil, natParity_zero, Bool.xor_self]
  | (u, b), (v, c), SimpleGraph.Walk.cons (v := w) h p => by
      have hadj_base : G.graph.Adj u w.1 := by
        have hxw' : G.coverAdj (u, b) w := h
        by_contra hna
        have hfalse : G.coverAdj (u, b) w ↔ False := by
          show (if h' : G.graph.Adj u w.1 then _ else False) ↔ _
          rw [dif_neg hna]
        exact (hfalse.mp hxw').elim
      have hunfold : G.coverAdj (u, b) w ↔
          (G.wrap ⟨s(u, w.1), (SimpleGraph.mem_edgeSet G.graph).mpr hadj_base⟩ ↔
            b ≠ w.2) := by
        show (if h' : G.graph.Adj u w.1 then _ else False) ↔ _
        rw [dif_pos hadj_base]
      have hwrap_iff :
          G.wrap ⟨s(u, w.1), (SimpleGraph.mem_edgeSet G.graph).mpr hadj_base⟩ ↔
            b ≠ w.2 := hunfold.mp h
      have hwb_iff : G.wrapEdgeBool s(u, w.1) = true ↔ b ≠ w.2 := by
        rw [G.wrapEdgeBool_iff_wrap hadj_base]; exact hwrap_iff
      have hproj_cons :
          G.projectCoverWalk (SimpleGraph.Walk.cons h p) =
            SimpleGraph.Walk.cons hadj_base (G.projectCoverWalk p) := rfl
      show natParity (G.walkWrapCount (G.projectCoverWalk
        (SimpleGraph.Walk.cons h p))) = xor b c
      rw [hproj_cons]
      rw [show G.walkWrapCount (SimpleGraph.Walk.cons hadj_base (G.projectCoverWalk p)) =
            (if G.wrapEdgeBool s(u, w.1) then 1 else 0) +
            G.walkWrapCount (G.projectCoverWalk p) from
          G.walkWrapCount_cons hadj_base (G.projectCoverWalk p)]
      rw [natParity_add]
      have hrec : natParity (G.walkWrapCount (G.projectCoverWalk p)) = xor w.2 c :=
        projectCoverWalk_wrap_parity p
      rw [hrec]
      by_cases hw : G.wrapEdgeBool s(u, w.1) = true
      · have hne : b ≠ w.2 := hwb_iff.mp hw
        have hb : b = !w.2 := by
          cases hbv : b <;> cases hwv : w.2 <;>
            first | rfl | (exfalso; apply hne; rw [hbv, hwv])
        simp only [hw, if_true, natParity_one]
        rw [hb]
        cases w.2 <;> cases c <;> decide
      · have heq : b = w.2 := by
          by_contra hne_bw
          exact hw (hwb_iff.mpr hne_bw)
        have hwb_false : G.wrapEdgeBool s(u, w.1) = false := by
          cases hv : G.wrapEdgeBool s(u, w.1)
          · rfl
          · exact absurd hv hw
        simp only [hwb_false, if_false, natParity_zero]
        rw [heq]
        cases w.2 <;> cases c <;> decide

/-! ### L12.3 — (⇒): Balanced implies even wrap on every closed walk -/

private lemma walkWrapCount_xor_of_balance {v₀ : G.V} (ε : G.V → Bool)
    (hε : ∀ (u v : G.V), ∀ (h : G.graph.Adj u v),
        G.graph.connectedComponentMk u = G.graph.connectedComponentMk v₀ →
        (G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ ↔ ε u ≠ ε v)) :
    ∀ {u v : G.V} (p : G.graph.Walk u v),
      G.graph.connectedComponentMk u = G.graph.connectedComponentMk v₀ →
      xor (ε u) (ε v) = natParity (G.walkWrapCount p) := by
  intro u v p
  induction p with
  | nil =>
      intro _
      rw [G.walkWrapCount_nil, natParity_zero, Bool.xor_self]
  | @cons u x v hux p ih =>
      intro huC
      have hxC : G.graph.connectedComponentMk x = G.graph.connectedComponentMk v₀ := by
        have hmk := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hux
        rw [← hmk]; exact huC
      have hε_iff := hε u x hux huC
      have hwrap_edge_iff :
          G.wrapEdgeBool s(u, x) = true ↔ ε u ≠ ε x := by
        rw [G.wrapEdgeBool_iff_wrap hux]; exact hε_iff
      have hrec := ih hxC
      rw [G.walkWrapCount_cons hux p, natParity_add]
      have hxor_step : xor (ε u) (ε v) =
          xor (xor (ε u) (ε x)) (xor (ε x) (ε v)) := by
        cases ε u <;> cases ε x <;> cases ε v <;> decide
      rw [hxor_step, hrec]
      by_cases hw : G.wrapEdgeBool s(u, x) = true
      · have hne := hwrap_edge_iff.mp hw
        have hux_xor : xor (ε u) (ε x) = true := by
          cases hu : ε u <;> cases hx : ε x <;>
            first | rfl | (exfalso; apply hne; rw [hu, hx])
        simp only [hw, if_true, natParity_one]
        rw [hux_xor]
      · have heq : ε u = ε x := by
          by_contra hne
          exact hw (hwrap_edge_iff.mpr hne)
        have hwb_false : G.wrapEdgeBool s(u, x) = false := by
          cases hv : G.wrapEdgeBool s(u, x)
          · rfl
          · exact absurd hv hw
        simp only [hwb_false, if_false, natParity_zero]
        have hux_xor : xor (ε u) (ε x) = false := by
          rw [heq, Bool.xor_self]
        rw [hux_xor]

private lemma closedWalk_wrapCount_even_of_balanced
    {C : G.graph.ConnectedComponent}
    (hbal : G.isBalanced C)
    (v : G.V) (p : G.graph.Walk v v)
    (hvC : G.graph.connectedComponentMk v = C) :
    Even (G.walkWrapCount p) := by
  obtain ⟨ε, hε⟩ := hbal
  have hε' : ∀ (u w : G.V), ∀ (h : G.graph.Adj u w),
      G.graph.connectedComponentMk u = G.graph.connectedComponentMk v →
      (G.wrap ⟨s(u, w), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ ↔ ε u ≠ ε w) := by
    intro u w h huv
    exact hε u w h (huv.trans hvC)
  have hxor := walkWrapCount_xor_of_balance (G := G) (v₀ := v) ε hε' p rfl
  have hparity_false : natParity (G.walkWrapCount p) = false := by
    rw [← hxor, Bool.xor_self]
  exact (even_iff_natParity_false _).mpr hparity_false

/-! ### L12.4 — (⇐): Even wrap on closed walks implies balanced -/

/-- The public hook we need from L6: given sheet separation above `v₀`, we
have balance of `[v₀]`. We reconstruct this via `componentProj_fiber_card`:
the fiber over `[v₀]` has two distinct elements, so its cardinality is ≥ 2;
but the fiber-card formula gives 1 (unbalanced) or 2 (balanced). So it's 2,
i.e. balanced. -/
private lemma balanced_of_candidate_sheets_ne (v₀ : G.V)
    (hne : G.candidateLift v₀ false ≠ G.candidateLift v₀ true) :
    G.isBalanced (G.graph.connectedComponentMk v₀) := by
  classical
  by_contra hbal
  have hcard := G.componentProj_fiber_card (G.graph.connectedComponentMk v₀)
  rw [if_neg hbal] at hcard
  have hC₀ : G.componentProj (G.candidateLift v₀ false) =
      G.graph.connectedComponentMk v₀ := by
    show ((G.coverGraph.connectedComponentMk (v₀, false)).map G.coverProj) = _
    rw [SimpleGraph.ConnectedComponent.map_mk]; rfl
  have hC₁ : G.componentProj (G.candidateLift v₀ true) =
      G.graph.connectedComponentMk v₀ := by
    show ((G.coverGraph.connectedComponentMk (v₀, true)).map G.coverProj) = _
    rw [SimpleGraph.ConnectedComponent.map_mk]; rfl
  let a : { D : G.coverGraph.ConnectedComponent //
      G.componentProj D = G.graph.connectedComponentMk v₀ } :=
    ⟨G.candidateLift v₀ false, hC₀⟩
  let b : { D : G.coverGraph.ConnectedComponent //
      G.componentProj D = G.graph.connectedComponentMk v₀ } :=
    ⟨G.candidateLift v₀ true, hC₁⟩
  have hab : a ≠ b := by
    intro hab
    apply hne
    exact congrArg Subtype.val hab
  have h2le : 2 ≤ Fintype.card { D : G.coverGraph.ConnectedComponent //
      G.componentProj D = G.graph.connectedComponentMk v₀ } :=
    Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  omega

private lemma sheets_ne_of_closedWalk_wrap_even (v₀ : G.V)
    (hclosed : ∀ (p : G.graph.Walk v₀ v₀), Even (G.walkWrapCount p)) :
    G.candidateLift v₀ false ≠ G.candidateLift v₀ true := by
  intro hcollapse
  have hreach : G.coverGraph.Reachable (v₀, false) (v₀, true) :=
    SimpleGraph.ConnectedComponent.exact hcollapse
  obtain ⟨q⟩ := hreach
  let p : G.graph.Walk v₀ v₀ := G.projectCoverWalk q
  have hparity : natParity (G.walkWrapCount p) = xor false true :=
    G.projectCoverWalk_wrap_parity q
  have hparity_true : natParity (G.walkWrapCount p) = true := by
    rw [hparity]; decide
  have heven := hclosed p
  have hparity_false : natParity (G.walkWrapCount p) = false :=
    (even_iff_natParity_false _).mp heven
  rw [hparity_false] at hparity_true
  exact absurd hparity_true (by decide)

/-! ### L12.5 — Main iff theorem -/

/-- **Walk-sum H¹ detector (T4).** A connected component is balanced iff
every closed walk within it has an even number of wrap edges. -/
theorem isBalanced_iff_closedWalk_wrap_even
    (C : G.graph.ConnectedComponent) : G.isBalanced C ↔
      ∀ (v : G.V) (p : G.graph.Walk v v),
        G.graph.connectedComponentMk v = C →
        Even (p.edges.countP
                (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))) := by
  constructor
  · intro hbal v p hvC
    exact G.closedWalk_wrapCount_even_of_balanced hbal v p hvC
  · intro hclosed
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : G.V, G.graph.connectedComponentMk v₀ = C :=
      Quot.exists_rep C
    subst hv₀
    have hsep : G.candidateLift v₀ false ≠ G.candidateLift v₀ true :=
      G.sheets_ne_of_closedWalk_wrap_even v₀ (fun p => hclosed v₀ p rfl)
    exact G.balanced_of_candidate_sheets_ne v₀ hsep

end ConnGraph

end ConnectionLaplacian
