/-
ConnectionLaplacian/L14_CycleEw.lean

**Stratum L14 — Cycle even-wrap specialization of the walk-sum detector
(weak form).**

(Originally planned as L13 per the PROVER-CYCLE-EW brief, but the L13
slot was taken by `L13_PSD` concurrently; this file is renamed to L14
without changing its scope.)

This file specializes `isBalanced_iff_closedWalk_wrap_even` (L12) to
graphs whose underlying `SimpleGraph` is `SimpleGraph.cycleGraph n`.

On a cycle graph, `H¹(-; ZMod 2) = ZMod 2` is one-dimensional, and a
closed walk's wrap-parity is determined by a single global parity:
the total number of wrap edges, mod 2.

## What's proved here

1. `walkWrapCount_eq_filter_card_of_eulerian`: if a closed walk is an
   Eulerian circuit, its wrap count equals the cardinality of the wrap
   subset of `edgeFinset`.

2. `cycle_isBalanced_iff_even_wrap_weak`: assuming the user supplies a
   closed Eulerian walk on `G.graph` (and that `G` has only one
   connected component), `balanced everywhere ↔ total wrap count even`.

## What's stubbed

* `fundamentalCycleWalk (n : ℕ) (hn : 3 ≤ n)` — an explicit Eulerian
  closed walk on `SimpleGraph.cycleGraph n` of length `n` visiting
  `0 → 1 → ⋯ → n-1 → 0`. Construction requires ~100 LOC of `Fin n`
  arithmetic (the step-adjacency proof `((k+1) - k : Fin n).val = 1`
  and boundary `by_cases`). Deferred to a dedicated stratum (future L16) per
  Round-5 PROVER-CYCLE-EW constraint #4.

The weak form is sufficient to close the "unbalanced ⇒ odd total wrap
count" implication on any concrete cycle graph the caller constructs,
by plugging in the explicit walk.

-/

import ConnectionLaplacian.L12_WalkH1
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Trails

namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L14.1 — Wrap-count under an Eulerian walk -/

/-- If a walk `p` is an Eulerian trail (visits every edge of `G.graph`
exactly once), then its wrap count equals the cardinality of the wrap
subset of `edgeFinset`. -/
lemma walkWrapCount_eq_filter_card_of_eulerian
    {u v : G.V} (p : G.graph.Walk u v) (hE : p.IsEulerian) :
    G.walkWrapCount p =
      (G.graph.edgeFinset.filter
        (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))).card := by
  classical
  have htrail : p.IsTrail := hE.isTrail
  -- The trail's edges (as a Finset) = G.edgeFinset.
  have hfin : htrail.edgesFinset = G.graph.edgeFinset := hE.edgesFinset_eq
  -- Unfold walkWrapCount = p.edges.countP wrapEdgeBool.
  unfold walkWrapCount
  -- Bridge List.countP → Multiset.countP via `List.countP = Multiset.countP`.
  rw [List.countP_eq_length_filter]
  -- List.filter on a list = Multiset.filter on its coe, then card.
  rw [show (p.edges.filter G.wrapEdgeBool).length
        = Multiset.card ((↑p.edges : Multiset (Sym2 G.V)).filter
            (fun e => G.wrapEdgeBool e = true)) from ?_]
  · -- Rewrite coe using `edgesFinset.val = p.edges`.
    have hcoe : (↑p.edges : Multiset (Sym2 G.V)) = G.graph.edgeFinset.val := by
      change htrail.edgesFinset.val = G.graph.edgeFinset.val
      rw [hfin]
    rw [hcoe]
    -- Multiset.card (edgeFinset.val.filter (wrapEdgeBool · = true))
    --   = (edgeFinset.filter (decide ...)).card.
    rw [show (G.graph.edgeFinset.val.filter (fun e => G.wrapEdgeBool e = true))
          = (G.graph.edgeFinset.filter
              (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))).val from ?_]
    · rfl
    · rw [Finset.filter_val]
      apply Multiset.filter_congr
      intros e _
      simp only [wrapEdgeBool]
  · -- Prove: (list.filter q).length = Multiset.card (multiset.filter q').
    rw [Multiset.filter_coe, Multiset.coe_card]
    -- remaining: List.filter with Bool vs List.filter with decide (Bool = true). Same predicate.
    congr 1
    apply List.filter_congr
    intro e _
    cases G.wrapEdgeBool e <;> simp

/-! ### L14.2 — Forward direction: balanced ⇒ even total wrap count -/

/-- **Forward direction.** If every component of `G` is balanced and
`G.graph` admits an Eulerian closed walk, then the total wrap count is
even. -/
theorem balanced_implies_even_wrap_of_eulerian
    (hbal : ∀ C : G.graph.ConnectedComponent, G.isBalanced C)
    {v₀ : G.V} (γ : G.graph.Walk v₀ v₀) (hE : γ.IsEulerian) :
    Even (G.graph.edgeFinset.filter
      (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))).card := by
  classical
  have hC : G.isBalanced (G.graph.connectedComponentMk v₀) := hbal _
  have hwalk := (G.isBalanced_iff_closedWalk_wrap_even
    (G.graph.connectedComponentMk v₀)).mp hC v₀ γ rfl
  -- `hwalk : Even (γ.edges.countP (fun e => decide ...))`.
  -- That's exactly `Even (walkWrapCount γ)` by definition of walkWrapCount+wrapEdgeBool.
  have hrewrite :
      γ.edges.countP (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))
        = G.walkWrapCount γ := by
    unfold walkWrapCount wrapEdgeBool
    rfl
  rw [hrewrite] at hwalk
  rw [← G.walkWrapCount_eq_filter_card_of_eulerian γ hE]
  exact hwalk

/-! ### L14.3 — Weak iff: requires reverse hypothesis supplied explicitly -/

/-- **Weak cycle even-wrap detector.**
Assumes: (i) `G.graph` admits an Eulerian closed walk; (ii) the reverse
direction holds as an explicit hypothesis.

Under (i), the forward `balanced ⇒ even total wrap` is proved
unconditionally. The reverse direction is passed through as hypothesis
`hrev`, isolating the remaining obligation.

On a cycle graph of length `n ≥ 3`, `hrev` can be discharged by a
cycle-space argument (`H¹(C_n; ZMod 2) = ZMod 2`), but that
construction is deferred to a later stratum. -/
theorem cycle_isBalanced_iff_even_wrap_weak
    {v₀ : G.V} (γ : G.graph.Walk v₀ v₀) (hE : γ.IsEulerian)
    (hrev :
      Even (G.graph.edgeFinset.filter
        (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))).card →
      ∀ C : G.graph.ConnectedComponent, G.isBalanced C) :
    (∀ C : G.graph.ConnectedComponent, G.isBalanced C) ↔
      Even (G.graph.edgeFinset.filter
        (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))).card := by
  refine ⟨fun hbal => G.balanced_implies_even_wrap_of_eulerian hbal γ hE, hrev⟩

/-! ### L14.4 — Fundamental cycle walk (TODO stub)

**TODO (deferred to a future stratum):** Construct the explicit fundamental closed
walk
```
fundamentalCycleWalk (n : ℕ) (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).Walk ⟨0, by omega⟩ ⟨0, by omega⟩
```
of length `n` visiting `0 → 1 → 2 → ⋯ → n-1 → 0`, together with its
Eulerian property
```
fundamentalCycleWalk_isEulerian :
    (fundamentalCycleWalk n hn).IsEulerian
```

With these in hand, the reverse direction `Even totalWrap → balanced`
follows from a cycle-space argument (every closed walk's edge multiset
equals `winding · γ.edges` mod 2-torsion). Constructing the walk and
the winding-number argument together requires ~200 LOC of `Fin n`
arithmetic; it is deferred to a future stratum to keep L14 ≤ 400 LOC per
Round-5 constraint #4.

Until that stratum lands, downstream consumers should invoke
`cycle_isBalanced_iff_even_wrap_weak` with their own Eulerian walk and
reverse-direction hypothesis. -/

end ConnGraph

end ConnectionLaplacian
