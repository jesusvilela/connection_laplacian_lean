# Round 4 Cosmo-Tree Integration

**Date:** 2026-04-22. **Swarm:** 3 provers + 2 adversarials + 1 ambiguator + 1 fuzzy-negator + 1 fuzzer-n8 (all parallel, all completed).

## Top-line verdicts

### Major Lean landings (all green, zero `sorry`, axiom-clean)

| file | theorem | prover | LOC |
|---|---|---|---|
| `L9_Bounds.lean` | 5 thm (traces, kernel ineq, kernel drop) | R3 prover-bounds / R4 inline | 109 |
| `L10_CoverCharpoly.lean` | `cover_charpoly_eq_scalar_times_mobius` | R4 prover-charpoly | ~120 |
| `L11_Trees.lean` | `tree_isBalanced_of_isTree` + 5 corollaries | R4 prover-tree | 366 |
| `L12_WalkH1.lean` | `isBalanced_iff_closedWalk_wrap_even` (both directions) | R4 prover-walkh1 | 322 |

**All four files verified via `#print axioms` to depend on only `[propext, Classical.choice, Quot.sound]`. Full project `lake build` passes (1823 objects).**

### Paper bugs caught and fixed

From **ADVERSARIAL-PAPER-R4** + **AMBIGUATOR-R4** (converging independently on the same bug):

1. **CRITICAL — Lemma 8.3 signed-psd proof sign error.** The statement `⟨x, L^sg x⟩ = Σ_{non-wrap}(x_u−x_v)² + Σ_{wrap}(x_u+x_v)²` was correct, but the algebraic expansion written in the proof inverted the wrap/non-wrap assignment. Root cause: two sign flips that cancel at the statement level but not at the expansion level. **Fixed** by a clean rewrite at `paper.tex:1000-1020`.
2. **Ex naive-eq compared wrong Laplacians.** Paper compared L_Mob to L_flat when the naive claim (per NEGATOR R3 C1) was L_Mob vs L_scalar. **Fixed.**
3. **Ex bridge-wrap had an invalid ε witness.** `ε(v_2)=⊤` violated Def 4.1 on the non-wrap edge {v_1,v_2}. **Fixed** to `ε(v_2)=⊥`.
4. **Ex fiber-mult was wrong twice.** Both the example's numbers (8 instead of 6) and the "correct multiplicative law" replacement were wrong; fiber cardinalities under π⁻¹ are additive, not multiplicative. **Replaced** with `Ex:cross-merge` using the R4 fuzzy-negator's C2 (τ=0.0000) finding on cross-component non-wrap-edge additions.
5. **Rem 8.7 typo** `det L(G+λI)` → `det(λI − L(G))`. **Fixed.**
6. **§9 Thm 9.1 tree-balance proof** had a pre/post-composition case split that doesn't work when {u,v} is internal to the r→v path. **Replaced** with the correct closed-walk + acyclicity argument.
7. **§9 Cor 9.5 cycle-ew hand-wave** on backtracking is now grounded in `H_1(C_n; Z/2) ≅ Z/2`.
8. **σ_W cochain/cocycle terminology** unified across §1.3, §4, §5.

### Fuzzy-logic scoreboard (15 claims)

From **NEGATOR-FUZZY**:

- **10 claims at τ = 1.0000** across n ∈ {3,4,5} exhaustive, including: `λ_min(L_möb) = 0`; spec as multiset-union; single-vertex switching preserves β; cover spec-partition; cover charpoly factorization; `dim ker L_sig ≤ dim ker L_s`; `ker L_möb² = ker L_möb`; `ker L_s + ker L_sig = ker L_möb`. Many are **redundant with existing Lean theorems**. C14 restates `scalarLap_cover_kernel_dim`; C9 is now `signed_kernel_le_scalar_kernel` in L9_Bounds.
- **Three in the interesting band τ ∈ [0.6, 0.9]:** C1 (`β ≥ β(G−e)` for non-wrap, τ=0.89; closes under "e not a bridge"), C5 (wrap/non-wrap complement symmetry, τ=0.81; parity-sensitive), C15 (`P[β≥1]` count-monotone, τ=0.61; fails on sampled count, holds on Bernoulli probability).
- **Two refuted (τ ≤ 0.12):** C2 (β monotone under non-wrap merging — opposite direction, τ=0.00); C11 (single-wrap-flip spec preservation — generic, τ=0.11).

### Extended fuzzer n=8 — 176,169 configs in 198s

From **FUZZER-N8**: 0 failures on all 17 identities except 20/24971 at n=8 on `B_cover_charpoly`, entirely attributable to condition-number growth for companion-matrix polynomial evaluation (max rel diff 7.3e-3). Since the Lean theorem is now exact, this is not a bug.

### Round-4 adversarial on L9_Bounds.lean

**ADVERSARIAL-L9**: 0 bugs. Two minor fragilities flagged (Mathlib refactor risk if `SimpleGraph.degree` changes definitional shape). File clean to land.

## Net discovery

The R4 tree grew by **four new Lean files** (L9–L12), covering **11 new named theorems**, **all formalised in the same session with zero `sorry`**. Together they close the `#TODO` at `L6_Cohomology.lean:461` in spirit (T10 cycle even-wrap would follow from T4 if one instantiates a fundamental cycle walk on `SimpleGraph.cycleGraph n` — a routine but voluminous task the WALKH1 prover explicitly deferred).

The paper now rests on a much thicker Lean base: the three main recognition theorems plus traces, kernel inequalities, kernel drop, cover-charpoly factorization, multiplicative pointwise multiplicity, tree balance with all corollaries, and the closed-walk H¹ balance detector.

## Round-5 candidates (deferred)

- **C4 Cycle even-wrap**: instantiate `isBalanced_iff_closedWalk_wrap_even` on `SimpleGraph.cycleGraph n` to close the `L6_Cohomology.lean:461` TODO.
- **Fuzzy-negator refinements**: C1 with "non-bridge" hypothesis; C5 with coboundary-class restriction.
- **Cover-charpoly → classical matrix-tree for signed graphs**: needs Cauchy–Binet in Mathlib.
- **Z/k generalization** (~500–800 LOC): still blocked on new `ZkConnGraph` structure.
- **Matroidal / Laplacian-spectral structure at n ≥ 9**: beyond exhaustive fuzzer envelope.

## Files touched this round

- **Lean:** 4 new files (`L9_Bounds`, `L10_CoverCharpoly`, `L11_Trees`, `L12_WalkH1`) + 2 edits (`ConnectionLaplacian.lean` manifest, `L6_Cohomology.lean` `private` removed on one lemma).
- **Paper:** bug-fixes at `paper.tex:185, 371, 1000, 1057, 1095, 1140, 1175, 1188, 1198`; references now point to landed files.
- **Findings:** 8 reports under `findings/round4/{role}/report.md` (or `SUMMARY.md`); this `INTEGRATION.md`.
- **Build:** `lake build` 1823/1823 green; `paper.pdf` regenerated to 176.6 KiB.

Zero regressions.
