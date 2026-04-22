/-
ConnectionLaplacian/L11_Trees.lean

**Stratum L11 — Tree-balanced theorem.**

On a tree every connected component (there's only one) is balanced, for
every choice of wrap. Proof via cover: suppose the two sheets over some
vertex `v₀` are in the same cover component — then there's a cover walk
`(v₀, false) → (v₀, true)`. Projecting to the base gives a walk
`v₀ → v₀` whose `walkWrapParity` is `true`. But in an acyclic graph,
every walk `u → v` has `walkWrapParity` determined by its endpoints
(via path-uniqueness), and the unique path `v₀ → v₀` is `nil`, with
parity `false`. Contradiction; hence sheets separate and the component
is balanced by `balanced_of_sheets_separated`.

Corollaries:
- `numBalancedComponents_of_isTree` : `#balanced = 1`
- `connectionLaplacian_kernel_dim_tree_mobius` : Möbius kernel dim = 2
- `tree_kernel_gap_zero` : on trees, flat and Möbius kernels have the
  same dimension (no "kernel drop").

Mathlib infrastructure used:
- `SimpleGraph.IsTree` (Combinatorics/SimpleGraph/Acyclic.lean:54)
- `IsAcyclic.path_unique` (:82)
- `Preconnected.subsingleton_connectedComponent` (Path.lean:853)
- `Walk.bypass`, `bypass_isPath`, `takeUntil`, `IsPath.takeUntil`
-/

import ConnectionLaplacian.L8_Recognition
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace ConnectionLaplacian

open Matrix BigOperators FiniteDimensional

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L11.1 — Walk wrap-parity -/

/-- Number of wrap edges on a walk, mod 2, as a `Bool`.
Defined via `List.countP` on `Walk.edges` to avoid pattern-match issues. -/
noncomputable def walkWrapParity {u v : G.V} (p : G.graph.Walk u v) : Bool :=
  decide ((p.edges.countP
    (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))) % 2 = 1)

/-- The `countP` predicate, applied to an edge `s(u,v)` of known adjacency,
reduces to `decide (wrap ⟨s(u,v), _⟩)`. -/
private lemma wrap_decide_pred {u v : G.V} (h : G.graph.Adj u v) :
    decide (∃ hh : s(u, v) ∈ G.graph.edgeSet, G.wrap ⟨s(u, v), hh⟩) =
      decide (G.wrap ⟨s(u, v),
        (SimpleGraph.mem_edgeSet G.graph).mpr h⟩) := by
  have hin : s(u, v) ∈ G.graph.edgeSet := (SimpleGraph.mem_edgeSet G.graph).mpr h
  by_cases hw : G.wrap ⟨s(u, v), hin⟩
  · rw [decide_eq_true hw, decide_eq_true ⟨hin, hw⟩]
  · rw [decide_eq_false hw, decide_eq_false ?_]
    rintro ⟨_, hw'⟩; exact hw hw'

@[simp] lemma walkWrapParity_nil (u : G.V) :
    G.walkWrapParity (SimpleGraph.Walk.nil : G.graph.Walk u u) = false := by
  unfold walkWrapParity; simp

@[simp] lemma walkWrapParity_cons {u v w : G.V} (h : G.graph.Adj u v)
    (p : G.graph.Walk v w) :
    G.walkWrapParity (SimpleGraph.Walk.cons h p) =
      xor (decide (G.wrap ⟨s(u, v),
        (SimpleGraph.mem_edgeSet G.graph).mpr h⟩)) (G.walkWrapParity p) := by
  unfold walkWrapParity
  rw [SimpleGraph.Walk.edges_cons, List.countP_cons]
  rw [G.wrap_decide_pred h]
  set c := p.edges.countP
      (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))
  set b := decide (G.wrap ⟨s(u, v),
      (SimpleGraph.mem_edgeSet G.graph).mpr h⟩)
  -- Goal: decide ((c + if b = true then 1 else 0) % 2 = 1) = xor b (decide (c % 2 = 1))
  cases b with
  | false =>
      simp only [if_false, Nat.add_zero, Bool.false_xor]
  | true =>
      simp only [if_true, Bool.true_xor]
      by_cases hc : c % 2 = 1
      · have hmod : (c + 1) % 2 = 0 := by omega
        rw [hmod, decide_eq_true hc]; decide
      · have hc' : c % 2 = 0 := by omega
        have hmod : (c + 1) % 2 = 1 := by omega
        rw [hmod, decide_eq_false hc]; decide

/-- Walk wrap-parity distributes over `append` (XOR). -/
lemma walkWrapParity_append :
    ∀ {u v w : G.V} (p : G.graph.Walk u v) (q : G.graph.Walk v w),
      G.walkWrapParity (p.append q) = xor (G.walkWrapParity p) (G.walkWrapParity q) := by
  intro u v w p q
  induction p with
  | nil => simp
  | @cons u a v h p ih =>
      show G.walkWrapParity (SimpleGraph.Walk.cons h (p.append q)) = _
      rw [walkWrapParity_cons, ih, walkWrapParity_cons]
      cases (decide (G.wrap ⟨s(u, a),
        (SimpleGraph.mem_edgeSet G.graph).mpr h⟩) : Bool) <;>
        cases G.walkWrapParity p <;>
        cases G.walkWrapParity q <;> rfl

/-! ### L11.2 — Relating walk-parity to the cover lift -/

/-- The sheet `nextSheet h b` equals `xor (decide wrap_h) b`. -/
private lemma nextSheet_eq_xor {u v : G.V} (h : G.graph.Adj u v) (b : Bool) :
    G.nextSheet h b =
      xor (decide (G.wrap ⟨s(u, v),
        (SimpleGraph.mem_edgeSet G.graph).mpr h⟩)) b := by
  unfold nextSheet
  by_cases hw : G.wrap ⟨s(u, v),
      (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
  · rw [if_pos hw, decide_eq_true hw]
    cases b <;> rfl
  · rw [if_neg hw, decide_eq_false hw]
    cases b <;> rfl

/-! ### L11.3 — Acyclic graphs: walk-parity is path-independent -/

/-- On an acyclic graph, walk-wrap-parity is invariant under bypass. -/
private lemma walkWrapParity_bypass (hacyc : G.graph.IsAcyclic) :
    ∀ {u v : G.V} (p : G.graph.Walk u v),
      G.walkWrapParity p = G.walkWrapParity p.bypass := by
  classical
  intro u v p
  induction p with
  | nil => rfl
  | @cons u w v h p ih =>
      -- bypass splits on whether u ∈ p.bypass.support.
      by_cases hu : u ∈ p.bypass.support
      · -- Case A: bypass = p.bypass.dropUntil u hu.
        have hbyp :
            (SimpleGraph.Walk.cons h p).bypass =
              p.bypass.dropUntil u hu := by
          show (dite _ _ _) = _; rw [dif_pos hu]
        have hsplit := p.bypass.take_spec hu
        -- T : Walk w u, D : Walk u v.
        -- hTpath : takeUntil is a path (subwalk of a path).
        have hTpath : (p.bypass.takeUntil u hu).IsPath :=
          p.bypass_isPath.takeUntil hu
        -- Also, cons h.symm nil : Walk w u is a path (single edge).
        have hedge_path :
            (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil :
                G.graph.Walk w u).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
          exact h.symm.ne
        -- By path-uniqueness, takeUntil = cons h.symm nil.
        have hTeq : p.bypass.takeUntil u hu =
            SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil := by
          have hpu :=
            hacyc.path_unique ⟨p.bypass.takeUntil u hu, hTpath⟩
              ⟨SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil, hedge_path⟩
          exact Subtype.ext_iff.mp hpu
        -- Parity of takeUntil:
        have hparityT :
            G.walkWrapParity (p.bypass.takeUntil u hu) =
              decide (G.wrap ⟨s(u, w),
                (SimpleGraph.mem_edgeSet G.graph).mpr h⟩) := by
          rw [hTeq, walkWrapParity_cons, walkWrapParity_nil]
          -- Edge {w,u} = {u,w} via Sym2 symmetry.
          have hedge_eq :
              (⟨s(w, u), (SimpleGraph.mem_edgeSet G.graph).mpr h.symm⟩ :
                    G.graph.edgeSet) =
                ⟨s(u, w), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ := by
            apply Subtype.ext; exact Sym2.eq_swap
          rw [hedge_eq]
          cases (decide (G.wrap ⟨s(u, w),
            (SimpleGraph.mem_edgeSet G.graph).mpr h⟩) : Bool) <;> rfl
        -- walkWrapParity p.bypass = xor wrap (walkWrapParity D).
        have hpByp_eq : G.walkWrapParity p.bypass =
            xor (decide (G.wrap ⟨s(u, w),
              (SimpleGraph.mem_edgeSet G.graph).mpr h⟩))
                (G.walkWrapParity (p.bypass.dropUntil u hu)) := by
          conv_lhs => rw [← hsplit]
          rw [G.walkWrapParity_append, hparityT]
        -- Now finalize.
        rw [walkWrapParity_cons, ih, hbyp, hpByp_eq]
        -- Goal: xor wrap (xor wrap (walkWrapParity D)) = walkWrapParity D.
        set b := decide (G.wrap ⟨s(u, w),
          (SimpleGraph.mem_edgeSet G.graph).mpr h⟩)
        set d := G.walkWrapParity (p.bypass.dropUntil u hu)
        cases b <;> cases d <;> rfl
      · -- Case B: bypass = cons h p.bypass.
        have hbyp :
            (SimpleGraph.Walk.cons h p).bypass =
              SimpleGraph.Walk.cons h p.bypass := by
          show (dite _ _ _) = _; rw [dif_neg hu]
        rw [hbyp, walkWrapParity_cons, walkWrapParity_cons, ih]

/-- On an acyclic graph, walk-wrap-parity depends only on endpoints. -/
lemma walkWrapParity_acyclic_endpoints (hacyc : G.graph.IsAcyclic)
    {u v : G.V} (p q : G.graph.Walk u v) :
    G.walkWrapParity p = G.walkWrapParity q := by
  classical
  rw [G.walkWrapParity_bypass hacyc p, G.walkWrapParity_bypass hacyc q]
  have hpq : p.bypass = q.bypass := by
    have := hacyc.path_unique ⟨p.bypass, p.bypass_isPath⟩
                              ⟨q.bypass, q.bypass_isPath⟩
    exact Subtype.ext_iff.mp this
  rw [hpq]

/-! ### L11.4 — Sheets separate on trees -/

/-- **Key fact.** On a tree, for every vertex `v₀`, the two sheets
`(v₀, false)` and `(v₀, true)` are in distinct components of the
orientation double cover. -/
lemma candidateLift_ne_of_isTree (hT : G.graph.IsTree) (v₀ : G.V) :
    G.candidateLift v₀ false ≠ G.candidateLift v₀ true := by
  intro hcollapse
  -- There's a cover walk (v₀, false) → (v₀, true).
  have hreach : G.coverGraph.Reachable (v₀, false) (v₀, true) :=
    SimpleGraph.ConnectedComponent.exact hcollapse
  obtain ⟨q⟩ := hreach
  -- Lemma: for any cover walk qc : (x, b) → (y, c), the projected base
  -- walk has walkWrapParity = xor b c.
  have hparity : ∀ {x y : G.CoverV} (qc : G.coverGraph.Walk x y),
      G.walkWrapParity (qc.map G.coverProj) = xor x.2 y.2 := by
    intro x y qc
    induction qc with
    | nil => simp
    | @cons x w y hxw qc' ih =>
        have hxw' : G.coverAdj x w := hxw
        have hadj_base : G.graph.Adj x.1 w.1 := by
          by_contra hna
          have hfalse : G.coverAdj x w ↔ False := by
            show (if h : G.graph.Adj x.1 w.1 then _ else False) ↔ _
            rw [dif_neg hna]
          exact (hfalse.mp hxw').elim
        have hwrap_iff : G.wrap ⟨s(x.1, w.1),
              (SimpleGraph.mem_edgeSet G.graph).mpr hadj_base⟩ ↔
            x.2 ≠ w.2 := by
          have hunfold : G.coverAdj x w ↔
              (G.wrap ⟨s(x.1, w.1),
                  (SimpleGraph.mem_edgeSet G.graph).mpr hadj_base⟩ ↔
                x.2 ≠ w.2) := by
            show (if h : G.graph.Adj x.1 w.1 then _ else False) ↔ _
            rw [dif_pos hadj_base]
          exact hunfold.mp hxw'
        have hmapcons :
            (SimpleGraph.Walk.cons hxw qc').map G.coverProj =
              SimpleGraph.Walk.cons
                (G.coverProj.map_adj hxw) (qc'.map G.coverProj) :=
          SimpleGraph.Walk.map_cons _ _ _
        rw [hmapcons, walkWrapParity_cons, ih]
        -- coverProj x = x.1 by the def of coverProj.toFun = Prod.fst.
        have hproj_x : G.coverProj x = x.1 := rfl
        have hproj_w : G.coverProj w = w.1 := rfl
        have hdec :
            decide (G.wrap ⟨s(G.coverProj x, G.coverProj w),
                (SimpleGraph.mem_edgeSet G.graph).mpr
                  (G.coverProj.map_adj hxw)⟩) =
            decide (x.2 ≠ w.2) := by
          have hedge_eq :
              (⟨s(G.coverProj x, G.coverProj w),
                    (SimpleGraph.mem_edgeSet G.graph).mpr
                      (G.coverProj.map_adj hxw)⟩ : G.graph.edgeSet) =
                 ⟨s(x.1, w.1),
                    (SimpleGraph.mem_edgeSet G.graph).mpr hadj_base⟩ := by
            apply Subtype.ext
            show s(G.coverProj x, G.coverProj w) = s(x.1, w.1)
            rw [hproj_x, hproj_w]
          rw [hedge_eq]
          by_cases hw : G.wrap ⟨s(x.1, w.1),
                (SimpleGraph.mem_edgeSet G.graph).mpr hadj_base⟩
          · rw [decide_eq_true hw, decide_eq_true (hwrap_iff.mp hw)]
          · rw [decide_eq_false hw, decide_eq_false (fun hne => hw (hwrap_iff.mpr hne))]
        rw [hdec]
        cases x.2 <;> cases w.2 <;> cases y.2 <;> decide
  -- Apply with qc = q.
  have hparq := hparity q
  -- hparq : walkWrapParity (q.map coverProj) = xor false true = true.
  simp at hparq
  -- q.map coverProj : Walk v₀ v₀ in base.
  have hnil :
      G.walkWrapParity (q.map G.coverProj) =
      G.walkWrapParity (SimpleGraph.Walk.nil : G.graph.Walk v₀ v₀) :=
    G.walkWrapParity_acyclic_endpoints hT.IsAcyclic _ _
  rw [walkWrapParity_nil] at hnil
  rw [hnil] at hparq
  exact Bool.noConfusion hparq

/-! ### L11.5 — Main theorem -/

/-- **Theorem (tree ⇒ every component balanced).** If the underlying
graph is a tree, then every connected component (there is only one) is
balanced, for every choice of wrap. -/
theorem tree_isBalanced_of_isTree
    (hT : G.graph.IsTree) (C : G.graph.ConnectedComponent) : G.isBalanced C := by
  obtain ⟨v₀, hv₀⟩ :
      ∃ v₀ : G.V, G.graph.connectedComponentMk v₀ = C := Quot.exists_rep C
  subst hv₀
  exact G.balanced_of_sheets_separated v₀ (G.candidateLift_ne_of_isTree hT v₀)

/-! ### L11.6 — Corollaries -/

/-- The number of connected components of a tree is 1. -/
theorem numComponents_of_isTree (hT : G.graph.IsTree) :
    G.numComponents = 1 := by
  unfold numComponents
  have hconn : G.graph.Connected := hT.isConnected
  haveI : Subsingleton G.graph.ConnectedComponent :=
    hconn.preconnected.subsingleton_connectedComponent
  obtain ⟨v⟩ := hconn.nonempty
  haveI : Inhabited G.graph.ConnectedComponent :=
    ⟨G.graph.connectedComponentMk v⟩
  haveI : Unique G.graph.ConnectedComponent := Unique.mk' _
  exact Fintype.card_unique

/-- On a tree, `numBalancedComponents = 1`. -/
theorem numBalancedComponents_of_isTree (hT : G.graph.IsTree) :
    G.numBalancedComponents = 1 := by
  unfold numBalancedComponents
  have hall : ∀ C : G.graph.ConnectedComponent, G.isBalanced C :=
    G.tree_isBalanced_of_isTree hT
  have heq : Fintype.card { C : G.graph.ConnectedComponent // G.isBalanced C }
            = Fintype.card G.graph.ConnectedComponent := by
    classical
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨C, _⟩ => C
      invFun := fun C => ⟨C, hall C⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl
    }
  rw [heq]
  have hconn : G.graph.Connected := hT.isConnected
  haveI : Subsingleton G.graph.ConnectedComponent :=
    hconn.preconnected.subsingleton_connectedComponent
  obtain ⟨v⟩ := hconn.nonempty
  haveI : Inhabited G.graph.ConnectedComponent :=
    ⟨G.graph.connectedComponentMk v⟩
  haveI : Unique G.graph.ConnectedComponent := Unique.mk' _
  exact Fintype.card_unique

/-- **Möbius kernel dimension on trees equals 2.** -/
theorem connectionLaplacian_kernel_dim_tree_mobius (hT : G.graph.IsTree) :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian true))) = 2 := by
  rw [G.connectionLaplacian_kernel_dim_general true]
  rw [if_pos rfl]
  rw [G.numComponents_of_isTree hT, G.numBalancedComponents_of_isTree hT]

/-- **Flat kernel dimension on trees equals 2.** -/
theorem connectionLaplacian_kernel_dim_tree_flat (hT : G.graph.IsTree) :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian false))) = 2 := by
  rw [G.connectionLaplacian_kernel_dim_general false]
  rw [if_neg (by decide : (false : Bool) ≠ true)]
  rw [G.numComponents_of_isTree hT]

/-- **Tree kernel-gap vanishes.** On a tree, flat and Möbius
Laplacians have the same kernel dimension. -/
theorem tree_kernel_gap_zero (hT : G.graph.IsTree) :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian true))) =
      FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian false))) := by
  rw [G.connectionLaplacian_kernel_dim_tree_mobius hT,
      G.connectionLaplacian_kernel_dim_tree_flat hT]

end ConnGraph

end ConnectionLaplacian
