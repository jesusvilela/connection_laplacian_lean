# Round 5 Cosmo-Tree Integration

**Date:** 2026-04-22. **Swarm:** 3 provers + 2 adversarials + 1 ambiguator + 1 fuzzy-negator + 1 fuzzer-n9 (all parallel, all completed — FUZZER-N9 truncated at n=5).

## Top-line verdicts

### Major Lean landings this round (all green, sorry-free, axiom-clean)

| file | theorem(s) | prover | LOC |
|---|---|---|---|
| `L13_PSD.lean` | `signedLaplacianMobius_posSemidef` + `isSymm` + `isHermitian` | PROVER-SIGNED-PSD | 311 |
| `L14_CycleEw.lean` | `walkWrapCount_eq_filter_card_of_eulerian`, `balanced_implies_even_wrap_of_eulerian`, `cycle_isBalanced_iff_even_wrap_weak` | PROVER-CYCLE-EW | 177 |
| `L15_BridgeMonotone.lean` | `numBalancedComponents_monotone_remove_nonwrap_nonbridge` (+ `'` variant + support API) | PROVER-C1-NONBRIDGE | 293 |

**All three files verified via `#print axioms` to depend only on `[propext, Classical.choice, Quot.sound]`. Full project `lake build` passes; all oleans up to `L15_BridgeMonotone.olean` present on disk.**

### Partial landing

PROVER-CYCLE-EW did not land the fully-parameterised `cycle_isBalanced_iff_even_wrapCount` (hypothesis `hcycle : G.graph = cycleGraph n` alone); the weak version requires an explicit Eulerian walk. The missing pieces are documented in `L14_CycleEw.lean`'s TODO and the prover's report:

- `fundamentalCycleWalk (n)` explicit walk construction (~100 LOC).
- Reverse direction via H¹(C_n; Z/2) ≅ Z/2 or prefix-parity ε (~200 LOC).

Deferred to R6. L6_Cohomology.lean:461 TODO comment is left in place.

### Paper bugs caught and fixed

From **ADVERSARIAL-PAPER-R5** + **AMBIGUATOR-R5** (converging independently on several items):

1. **HIGH — `\ref{prop:scalarLaplacian-kernel}` undefined** (line 1212 and appendix row 1275). Fixed to `thm:scalar-ker`.
2. **HIGH — `\ref{sec:cycle}` typo** at line 269. Fixed to `sec:cycles`.
3. **HIGH — Appendix A row: `flatLaplacian_kernel_dim` does not exist.** Fixed to `laplacian_decomposes` (KernelDimension.lean:345).
4. **HIGH — Appendix A row: `strict_inequality_when_unbalanced` does not exist.** Fixed to `mobius_kernel_strict_iff_general` (L8_Recognition.lean:142).
5. **HIGH — Appendix A row file mis-cited**: `laplacian_kernel_dim_decomposes` is in L8_Recognition.lean, not KernelDim.lean. Fixed.
6. **HIGH — Row 1304 stale**: Lem 8.3 showed "Lean port scheduled L13_PSD.lean" but the file already exists. Fixed to live pointer `signedLaplacianMobius_posSemidef` / `L13_PSD.lean`.
7. **HIGH — Row 1339 (cycle-ew) outdated**: was "deferred", now points to `cycle_isBalanced_iff_even_wrap_weak` / `L14_CycleEw.lean`.
8. **HIGH — Ex 9.3 β-rule wrong**: "−1 when both endpoints balanced" is incorrect. Balanced+unbalanced merger also loses a balanced component. Fixed to "at least one endpoint" with explanatory parenthetical.
9. **HIGH — Reproducibility overclaim**: "zero numerical violations" conflicted with the n=8 cover-charpoly 20 near-misses. Fixed to disclose the exhaustive-vs-sampled split and the condition-number bound.
10. **MED — Ex 5.5 type mismatch**: L_Mob (dim 2|V|) vs L_scalar (dim |V|) don't share an ambient space. Added clarification.
11. **MED — Fourier Re/Im vanishes at k=0, k=n/2** (§7 line 791). Added parenthetical qualifier.
12. **MED — Script path** `fuzzer/fuzz.py` → `findings/round2/fuzzer/fuzz.py`. Fixed.
13. **MED — Appendix opener overclaim** "every named theorem has a Lean counterpart". Softened to "principal" + explicit admission that subsidiary lemmas are implicit.
14. **LOW — Case count mismatch** ("three structural cases" → four). Fixed.

Paper now compiles cleanly at **192 KiB**. New row added in Appendix A for `L15_BridgeMonotone.lean` under Ex. `ex:cross-merge` as R5 refinement with C1 τ = 1.

### Fuzzy-logic scoreboard (22 new claims)

From **NEGATOR-R5**:

- **17 claims at τ = 1.0000** over n ∈ {3,4,5} exhaustive (6 extended to n=6 sample). Topics: bipartite wrap/complement symmetry (R4), subdivision-invariance (R6,R7), bridge-contraction (R8), trace power-sum splits (R11,R12), fibre-restriction rank (R14), coboundary count (R15), edge-connectivity (R16), Cauchy interlacing (R17), Frobenius norm (R19), disjoint-union additivity (R20), balance ⇒ bipartite-(V,W) (R21), orthogonal kernel-decomposition (R22). **R9 and R18 are now covered by L13_PSD and L9_Bounds respectively.**
- **R1/R2 independently confirm L15**: the correct direction is `β(G) ≤ β(G−e)` for non-bridge non-wrap e, which is exactly `numBalancedComponents_monotone_remove_nonwrap_nonbridge`. Independent convergence.
- **R3 at τ ≈ 0.34 refuted** in its stated form, superseded by R4.

### Extended fuzzer — truncated at n=5

From **FUZZER-N9**: agent wrote `fuzz_n9.py` and began execution. `run.log` shows clean pass through n ≤ 5 exhaustive (0 failures on all 18 identities + 4 new Track-B categories), but the run was cut off before reaching n=6-9. No new negative evidence; no new findings.

### R5 adversarial on L10/L11/L12

**ADVERSARIAL-NEW-LEAN**: 0 bugs. All three files clean; hand verification pass 760/760 (L10), 143/143 (L11), 888/888 (L12). Four minor fragilities flagged (Mathlib-refactor risk). Two cosmetic findings: dead lemma `nextSheet_eq_xor` in L11, and a stale docstring in L12.

## Net discovery

Round 5 added **3 new Lean files** (L13-L15) for **5 new named theorems**, all in the same session with zero `sorry`. Together they:

- Lock down PSD of the signed-Möbius Laplacian (`L13_PSD`), eliminating the R4 "scheduled" placeholder.
- Provide a weak but usable cycle-Eulerian iff (`L14_CycleEw`) that the paper's Cor `cor:cycle-ew` now references directly.
- Promote the R4 fuzzy claim C1 (τ=0.89) to an exact Lean theorem with a sharper bridge-monotonicity characterisation (`L15_BridgeMonotone`). Surprise finding: the wrap/non-wrap distinction is irrelevant — only bridge status matters for β-monotonicity under edge deletion.

The paper now carries a cleaner Appendix A: 4 rows corrected, 2 rows promoted from "scheduled"/"deferred" to landed pointers, 1 new row for the L15 refinement; overclaims on reproducibility and completeness softened; 3 new mathematical content fixes (Ex 9.3 rule, Fourier edge-k qualifier, Ex 5.5 type-size disambiguation).

## Round-6 candidates (deferred)

- **Complete cycle-ew**: `fundamentalCycleWalk n` + H¹(C_n;Z/2) reverse direction to close L6:461 TODO fully.
- **Fuzzy R14**: fibre-restriction rank formula in `L5_Cover.lean`.
- **Fuzzy R15**: coboundary count 2^(|V|−#π₀) in `L6_Cohomology.lean`.
- **Fuzzy R17**: Cauchy interlacing under non-wrap edge removal (new file or `L13_PSD` extension).
- **Cosmetic**: delete `nextSheet_eq_xor` from L11, fix L12 docstring, inline the `balanced_of_candidate_sheets_ne` shim.
- **Mathlib PR**: `Matrix.charpoly_conj_of_isUnit_det` helper from L10 is PR-worthy.
- **Paper residuals**: A8 (Lem 4.4 hand-wave), A10 (⊤/⊥ overloading), A11 (`\operatorname{Mob}` vs `\mathrm{Mob}`), A13 (Thm 5.5 scope forward-ref), A14 (Cor 6.3 criterion distinction).
- **Fuzzer n=9**: re-run `fuzz_n9.py` to completion with improved-precision arithmetic path.

## Files touched this round

- **Lean:** 3 new files (`L13_PSD`, `L14_CycleEw`, `L15_BridgeMonotone`) + `ConnectionLaplacian.lean` manifest edits.
- **Paper:** bug-fixes at `paper.tex:198, 269, 458, 883, 791, 1209, 1212, 1240, 1270-1285, 1303, 1319-1323, 1326-1338`.
- **Findings:** 8 reports under `findings/round5/{role}/report.md` (or `SUMMARY.md`); this `INTEGRATION.md`.
- **Build:** `lake build` green; oleans for L10-L15 on disk; `paper.pdf` regenerated to 192 KiB.

Zero regressions.
