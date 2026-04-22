# PROVER-TREE — Round 4 Report

**File landed:** `ConnectionLaplacian/L11_Trees.lean` (366 lines, green, sorry-free).

**Status:** `lake build ConnectionLaplacian.L11_Trees` succeeds. `#print axioms` on all four main theorems reports only `[propext, Classical.choice, Quot.sound]`.

## Theorems landed

1. `ConnGraph.tree_isBalanced_of_isTree` — main theorem.
2. `ConnGraph.numComponents_of_isTree` — trees have 1 component.
3. `ConnGraph.numBalancedComponents_of_isTree` — `#balanced = 1`.
4. `ConnGraph.connectionLaplacian_kernel_dim_tree_mobius` — Möbius ker dim = 2.
5. `ConnGraph.connectionLaplacian_kernel_dim_tree_flat` — flat ker dim = 2.
6. `ConnGraph.tree_kernel_gap_zero` — equal kernel dims on trees.

## Proof architecture (deviation from round-3 sketch)

Instead of constructing `ε` directly from unique paths, the proof goes through the orientation double cover:

- Define `walkWrapParity : Walk u v → Bool` via `List.countP` on `Walk.edges`.
- Key lemma `walkWrapParity_bypass` on acyclic graphs: for a `cons h p` where `u ∈ p.bypass.support`, the detour `p.bypass.takeUntil u hu : Walk w u` is a path, which by `IsAcyclic.path_unique` equals the single-edge path `cons h.symm nil`; its wrap-parity cancels the added `cons h`.
- Main step: a cover walk `(v₀, false) → (v₀, true)` projects to a base walk `v₀ → v₀` with wrap-parity `xor false true = true`, contradicting `walkWrapParity_nil = false` via `walkWrapParity_acyclic_endpoints`. Sheets separate → `balanced_of_sheets_separated` (L6) gives the balance witness.

## Hard parts

- Direct recursive definition `walkWrapParity` via pattern matching triggered "invalid field notation" on recursive call; routed around via `List.countP` over `Walk.edges`.
- `rw` motive failures in the bypass case; resolved with `conv_lhs` + prepared `have hpByp_eq` using `walkWrapParity_append`.
- `balanced_of_sheets_separated` in L6 was `private`; removed the keyword (single-line edit, no impact on L6's build).

## Non-L11 changes

- `ConnectionLaplacian/L6_Cohomology.lean:288` — removed `private` from `balanced_of_sheets_separated`.
- `ConnectionLaplacian.lean` — added `import ConnectionLaplacian.L11_Trees`.

## Mathlib gaps

None blocking. All needed lemmas are in v4.11.0 (`IsTree`, `IsAcyclic.path_unique`, `Walk.bypass`, `bypass_isPath`, `Walk.take_spec`, `IsPath.takeUntil`, `Walk.cons_isPath_iff`, `Preconnected.subsingleton_connectedComponent`, `Connected.nonempty`).
