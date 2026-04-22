# PROVER-C1-NONBRIDGE — bridge-monotonicity of β

**Date:** 2026-04-22. **Landing:** `ConnectionLaplacian/L15_BridgeMonotone.lean` (293 LOC).

## Sharpening of R4 fuzzy claim C1

R4 fuzzy-negator C1 was: "`β(G−e) ≥ β(G)` for non-wrap `e`", τ = 0.89. Every failure was a bridge, so the R5 refinement adds the hypothesis "e non-bridge".

Deeper finding: once the **non-bridge** hypothesis is in place, the **non-wrap** hypothesis is unused — the β-monotonicity under edge deletion is bridge-status-sensitive but wrap-status-insensitive. The landed Lean statement accepts `_hnonwrap` as an unused hypothesis to match the fuzzy-scoreboard wording; a cleaner variant drops it entirely.

## Python sanity check (n ≤ 5)

Exhaustive across all ConnGraphs with wrap subsets of non-bridge non-wrap edges:

- **Refined claim** `β(G) ≤ β(G−e)` for non-wrap non-bridge e: **13,100 / 13,100 pass (τ = 1.0000)**.
- **Unrefined C1** (no non-bridge hypothesis): **1,481 / 13,543 fail** — every failure is a bridge edge.

Artifacts: `sanity_c1_nonbridge.py`, `results.json`.

## Theorems landed

- `numBalancedComponents_monotone_remove_nonwrap_nonbridge` — full generality.
- Primed variant `'` matching the exact `Sym2` signature the task requested.
- Supporting API:
  - `ConnGraph.eraseEdge` (non-bridge edge removal with balance data).
  - `eraseEdge_componentMap` (bijection on CC when e is non-bridge).
  - `reachable_iff_reachable_eraseEdge`.
  - `isBalanced_eraseEdge_of_isBalanced`.

## Build / axioms

- Full project `lake env lean ConnectionLaplacian.lean` exits 0.
- `#print axioms numBalancedComponents_monotone_remove_nonwrap_nonbridge` → `[propext, Classical.choice, Quot.sound]`.

## Proof sketch

Non-bridge `e = s(a,b)` gives (via Mathlib `isBridge_iff_adj_and_forall_walk_mem_edges`) an avoiding walk `pAB : a ⇝ b` in `G`. An inductive `rerouteWalk` splices `pAB` (or its reverse) in place of each occurrence of the forbidden edge inside any `G`-walk, producing a walk in `G.eraseEdge ⟨s(a,b), _⟩`. Reachability is preserved in both directions, so the component partition is preserved. The induced component map `G'.CC → G.CC` is a bijection. Balance transfers back along it because the wrap predicate on surviving edges is definitionally the `G`-wrap — the same coloring `ε` witnesses balance in `G.eraseEdge e`. Counting via `Fintype.card_le_of_injective`.

## Artifacts

- `sanity_c1_nonbridge.py` — Python exhaustive check.
- `results.json` — full sweep output.
- `axiom_check.lean` — single-file axiom audit (builds clean).

## Net

A fuzzy τ = 0.89 claim has been promoted to an exact Lean theorem with a crisper hypothesis. One unused hypothesis surfaced: wrap-status is irrelevant — bridge-status alone controls β-monotonicity under edge deletion.
