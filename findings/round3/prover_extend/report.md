# PROVER-EXTEND - Round 3 Discovery Report

## Context recap

Already sorry-free in the project (confirmed file/line-level):
- `ConnGraph.scalarLaplacian_kernel_dim` at `KernelDimension.lean:476` — `finrank ker L_scalar = numComponents`.
- `ConnGraph.signedLaplacian_kernel_dim_general` at `L8_Recognition.lean:53` — `finrank ker L_signed = numBalancedComponents`.
- `ConnGraph.connectionLaplacian_kernel_dim_general` at `L8_Recognition.lean:120` — Möbius: `#π₀ + #balanced`; flat: `2·#π₀`.
- `ConnGraph.componentProj_fiber_card` at `L6_Cohomology.lean:344` — fiber is 2 (balanced) / 1 (unbalanced).
- `flat_cycle_spectrum` / `mobius_cycle_spectrum` at `CycleSpectrum.lean:659` / `:679`.

`isBalanced C` (defined `L6_Cohomology.lean:52`) asks for a Z/2 vertex 2-coloring `ε` with `wrap e ↔ ε(u) ≠ ε(v)` on every edge of `C`.

## Mathlib v4.11.0 infrastructure (verified in `.lake/packages/mathlib`)

- `Combinatorics/SimpleGraph/Acyclic.lean:54` — `structure IsTree`; `:50` `def IsAcyclic`.
- `Acyclic.lean:82` — `IsAcyclic.path_unique`; `:125` — `isTree_iff_existsUnique_path`; `:150` — `IsTree.card_edgeFinset : |E| + 1 = |V|`.
- `SimpleGraph/Path.lean:853` — `Preconnected.subsingleton_connectedComponent`; `:1049` — `IsBridge`.
- `SimpleGraph/Hasse.lean:94` — `pathGraph`; `:105` — `pathGraph_connected`.
- `SimpleGraph/Circulant.lean:59` — `cycleGraph`; `:92` — `cycleGraph_adj'`; `:133` — `cycleGraph_connected`.
- `SimpleGraph/Basic.lean:144` — `completeGraph`; `:153` — `completeBipartiteGraph (V ⊕ W)`.
- `SimpleGraph/Coloring.lean:395` — `CompleteBipartiteGraph.bicoloring`.
- **Missing in Mathlib:** `wheelGraph`, `starGraph`, `IsBipartite` as a named predicate (derivable via `Colorable 2` or `completeBipartiteGraph`). Also missing: spanning-tree / fundamental-cycle basis for H¹, walk-sum H¹ detector.

---

## Proposed theorems (10)

### T1 — Tree balanced-always (CORE)

Tree ⇒ every component balanced for every wrap choice.
Sketch: root r; define ε v := (#wrap-edges on unique path r⇝v) mod 2 via `IsAcyclic.path_unique`.
Signature:
```lean
theorem ConnGraph.tree_isBalanced_of_isTree
    (hT : G.graph.IsTree) (C : G.graph.ConnectedComponent) : G.isBalanced C
```
Corollaries: `numBalancedComponents = 1`, `ker L_signed = 1`, `ker L_möb = 2`.
Difficulty: medium, 30-60 lines.

### T2 — Acyclic forest generalization
Componentwise T1 via `ConnectedComponent.ind`. ≤15 lines given T1.

### T3 — Path graph P_n
`pathGraph (n+1)` is a tree; needs local ~30-line `pathGraph_isAcyclic`.

### T4 — Walk-sum H¹ detector (ENABLING)
`C` balanced iff every closed walk in `C` has even wrap count. ~50 lines.

### T5 — K_{m,n} with a single wrap edge
Explicit 4-cycle through the wrap edge unbalances it. Needs T4.

### T6 — K_n: balanced iff wrap is a vertex-cut
Presentational rename of `isBalanced` for connected graphs. ~25 lines.

### T7 — Star graph K_{1,n}
Trivial corollary of T1.

### T8 — Wheel graph W_n
BLOCKED on missing spanning-tree infrastructure in Mathlib v4.11.0.

### T9 — Tree flat/Möbius gap vanishes
`ker L_möb = ker L_flat = 2` on trees. ≤5 lines given T1.

### T10 — Cycle: balanced iff even total wrap count (FILLS TODO)
Closes `L6_Cohomology.lean:461` TODO and recovers original `numOddWrapComponents` formulation.

---

## Recommended landing order

| Rank | Theorem | Value | Cost |
|-----:|---------|-------|------|
| 1 | T1 tree-balanced | high | medium |
| 2 | T9 tree gap-zero | medium | trivial |
| 3 | T6 K_n cut-iff | high | easy |
| 4 | T4 walk-sum detector | high | medium |
| 5 | T10 cycle even-wrap | high | medium |
| 6 | T2 acyclic forest | medium | easy |
| 7 | T3 path graph | medium | easy |
| 8 | T7 star graph | low-medium | easy |
| 9 | T5 K_{m,n} one-wrap | medium | medium |
| 10 | T8 wheel W_n | medium | hard (DEFER) |

Suggested commits: new files `L9_Trees.lean` (T1,T9,T2,T3,T7), `L10_Cliques.lean` (T6), `L11_H1_WalkSum.lean` (T4); append T10 to `L6_Cohomology.lean`; T5 later.

All signatures are target shapes (not executed). `wheelGraph`, `starGraph`, `IsBipartite` must be introduced locally — absent from Mathlib v4.11.0.
