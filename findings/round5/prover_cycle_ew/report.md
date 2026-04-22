# PROVER-CYCLE-EW — closing L6 TODO via the cycle instance

**Date:** 2026-04-22. **Landing:** `ConnectionLaplacian/L14_CycleEw.lean` (177 LOC).

## Theorems landed

All three sorry-free, axioms `[propext, Classical.choice, Quot.sound]`:

1. `walkWrapCount_eq_filter_card_of_eulerian` — for any Eulerian walk `p`, `G.walkWrapCount p = (G.graph.edgeFinset.filter wrap).card`.
2. `balanced_implies_even_wrap_of_eulerian` — forward direction, unconditional on cycle structure: balance + an existing Eulerian walk ⇒ total wrap count even.
3. `cycle_isBalanced_iff_even_wrap_weak` — full iff, parameterised by an Eulerian walk `γ` plus an explicit `hrev` hypothesis for the reverse direction.

## Partial-landing note

The originally requested theorem `cycle_isBalanced_iff_even_wrapCount` with only `hcycle : G.graph = SimpleGraph.cycleGraph n` is **not** landed — it would require two further pieces:

- `fundamentalCycleWalk (n)` — explicit Eulerian walk 0 → 1 → … → n−1 → 0 on `cycleGraph n`. Needs a `Fin n` step-adjacency proof (`((k+1) − k : Fin n).val = 1`) with boundary `by_cases`, recursion on a natural-number counter, plus an edge-list permutation spec. ≥ 100 LOC of index bookkeeping.
- Reverse direction `Even totalWrap → ∀ C, G.isBalanced C` — needs either the cycle-space argument (H¹(C_n; Z/2) ≅ Z/2) or the direct ε(k) := (wrap count on prefix [0,k)) mod 2 construction. ≈ 200 LOC combined.

Both deferred pieces are documented in the file's TODO docstring and pushed to R6. L6_Cohomology.lean:461 comment is left in place — the weak version does not fully close it.

## Build / axioms

- `lake build` passes on the full project (oleans for L10-L15 all present in `.lake/build/lib/ConnectionLaplacian/`).
- `#print axioms` on each of the three landed theorems returns `[propext, Classical.choice, Quot.sound]`.

## Mathlib API used (v4.11.0)

- `SimpleGraph.Walk.IsEulerian`, `IsEulerian.isTrail`, `IsEulerian.edgesFinset_eq`, `IsTrail.edgesFinset` (from `Mathlib.Combinatorics.SimpleGraph.Trails`).
- `List.countP_eq_length_filter`, `List.filter_congr`.
- `Multiset.filter_coe`, `Multiset.coe_card`, `Multiset.filter_congr`.
- `Finset.filter_val`.
- `SimpleGraph.cycleGraph`.

## Net

A weak version of the C_n balance iff is landed and paired to Appendix A row 1319. The fully-parameterised statement is deferred to R6 with a clear work-item breakdown.
