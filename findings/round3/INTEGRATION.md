# Round 3 Cosmo-Tree Integration

**Date:** 2026-04-22. **Swarm:** 3 provers + 2 adversarials + 1 ambiguator + 1 negator + 1 fuzzer (all parallel, all completed).

## Top-line verdicts

### Main tree is solid
- **ADVERSARIAL-SPLITS**: 0 confirmed bugs in `scalarLap_cover_splits`. Two ergonomic weaknesses (ephemeral `show` cast, implicit Hadamard convention) — document, don't rework.
- **ADVERSARIAL-FIBER**: 0 confirmed bugs in `componentProj_fiber_card`. One design smell (ε under-specified off component) — add doc comment at `isBalanced`.
- **FUZZER-EXTENDED**: 456,950 configs tested at n ≤ 7. Zero failures on 10 identities (spec/trace/det/ker/split/fiber/balance/zero_mult/per_eig_mult/signed_ker).
- **NEGATOR**: refuted 4 of 10 naive claims the formalization does **not** make (C1 as-stated, C7, C8, C10b) — these are warning flags for over-generalization, not bugs.

### Cheap wins available (≤40 LOC, zero new Mathlib deps)
From **PROVER-BOUNDS** + **PROVER-BEYOND-Z2**, all drop-in consequences of the existing L8 stack:

1. `trace_scalarLaplacian = 2|E|` (~8 LOC) — uses `SimpleGraph.sum_degrees_eq_twice_card_edges`.
2. `trace_signedLaplacianMobius = 2|E|` (~10 LOC).
3. `trace_laplacian = 4|E|` (~20 LOC).
4. `signed_kernel_le_scalar_kernel` (~3 LOC) — `numBalancedComponents_le` rewrite.
5. `kernel_drop_le_numComponents` (~5 LOC).
6. `kernel_drop_eq_unbalanced` (~5 LOC).

**Recommended landing**: new file `ConnectionLaplacian/L9_Bounds.lean`. ~50 LOC total.

### Medium wins (~100–200 LOC, unblocked)

7. `signedLap_posSemidef` (~80 LOC) — template `Mathlib/.../LapMatrix.lean:70-89`; existing scaffold `findings/round2/prover_kerdim/attempt.lean:167-194`.
8. `cover_charpoly_eq_scalar_times_mobius` (~100 LOC) — strengthens T1 at multiset/charpoly level; strictly stronger than any Cauchy interlacing.
9. `tree_isBalanced_of_isTree` + trivial corollaries (~60 LOC) — from **PROVER-EXTEND**; unlocks tree/forest/path/star specializations.
10. `isBalanced_iff_closedWalk_wrap_even` (~50 LOC) — walk-sum H¹ detector; **this is the lemma that unlocks T10 (cycle even-wrap, filling the L6 TODO at line 461)**.

### Larger, deferred

- **Z/k generalization** (~500–800 LOC) — needs new `ZkConnGraph` structure; complex-Hermitian Laplacian; `Mathlib/Analysis/Fourier/ZMod.lean` available. Scope a week.
- **Wheel W_n** — BLOCKED on missing spanning-tree infrastructure in Mathlib v4.11.0.
- **Matrix-tree theorem, Cauchy interlacing, Cheeger** — all BLOCKED on absent Mathlib infrastructure (no Cauchy-Binet, no interlacing, no edgeExpansion). Defer upstream.

## Paper corrections (AMBIGUATOR)

### Must-fix

1. **2,456 vs 3,456 configurations** — line 121 (abstract) contradicts lines 836 & 845 (§7). Run fuzzer once, reconcile. Factual self-contradiction erodes confidence.
2. **Balance scope** (component-local vs graph-global) — disambiguate cohomology paragraph at lines 504–511.
3. **PSD claim** (line 252) — state scope (R vs C), cite Lean lemma (which per fuzzer T2 and bounds-prover claim 6 we can now formalize as `signedLap_posSemidef`).
4. **Thm 5.5 quantifier direction** — "some component not balanced" → "not every component balanced" to match Lean phrasing.
5. **Isolated vertex vacuously balanced** — add convention note after Def 4.1 (load-bearing for Thm 5.2).

### Nice-to-fix

6. **Rhat factor-of-2**: state R^{-1} = (1/2)R upfront.
7. **π_0 / [·]_π_0 notation collision** — disambiguate set-of-components vs equivalence-class subscript.
8. **§4 Step 3 footnote hedge** — either replace prose with deck-orbit argument (matches Lean), or drop the hedge. Current "slightly different but equivalent route" language signals distance.

## Fuzzer regression additions

Per **NEGATOR** refuted claims, add these as explicit negative tests to `tools/fuzz_negative.py` (new file):
- C1 (as-stated): confirm `km ≠ ks` when G is balanced (empty-graph n=3).
- C7: bridge wrap edge with `|W|=1` can balance a connected graph.
- C8: fiber sizes multiply, never subadd on disjoint union.
- C10b: non-wrap contraction can change `dim ker L_signed`.

Per **FUZZER-EXTENDED**, elevate T1_det and T6_mult_per_eig to persistent regression invariants.

## Concrete action plan

### Phase A — paper patch (same session if desired)
- [ ] A1. Reconcile 2,456 / 3,456 count (§8 of AMBIGUATOR report).
- [ ] A2. Balance scope clarification + isolated vertex convention.
- [ ] A3. PSD scope statement.
- [ ] A4. Thm 5.5 quantifier phrasing.

### Phase B — cheap Lean wins (new file `L9_Bounds.lean`, ~50 LOC)
- [ ] B1. `trace_scalarLaplacian`, `trace_signedLaplacianMobius`, `trace_laplacian`.
- [ ] B2. `signed_kernel_le_scalar_kernel`.
- [ ] B3. `kernel_drop_le_numComponents`, `kernel_drop_eq_unbalanced`.

### Phase C — medium wins (multiple files, ~300 LOC)
- [ ] C1. `signedLap_posSemidef` (port `findings/round2/prover_kerdim/attempt.lean` scaffold).
- [ ] C2. `cover_charpoly_eq_scalar_times_mobius` (new `L10_CoverCharpoly.lean`).
- [ ] C3. `tree_isBalanced_of_isTree` + path/forest/star corollaries (new `L11_Trees.lean`).
- [ ] C4. `isBalanced_iff_closedWalk_wrap_even` (new `L12_WalkH1.lean`).
- [ ] C5. Fill L6 TODO at line 461: `cycle_isBalanced_iff_even_wrap`, recovering pre-registered `numOddWrapComponents` formula (uses C4).

### Phase D — deferred / upstream
- [ ] D1. Z/k generalization (~1 engineer-week).
- [ ] D2. Mathlib upstream contributions: Cauchy-Binet, Kirchhoff matrix-tree, Cauchy interlacing, Cheeger. These unblock signed matrix-tree and signed Cheeger.

## Files touched by this round

- 8 reports under `findings/round3/{role}/report.md` (plus `SUMMARY.md` for fuzzer).
- This `INTEGRATION.md`.
- Zero Lean file changes. Zero paper changes. Zero rebuilds triggered.
