# ADVERSARIAL-A R6 Stage 4 — Red-team of L16 M6/M7 landing

**Date:** 2026-04-22. **Target:** `ConnectionLaplacian/L16_SpectrumUnion.lean` (Stage-3 landing). **Method:** scratch `adv_probe*.lean` in project root (deleted after), `#print axioms`, numpy cross-check against `sheaf_beta/fuzz.py`.

## Verdict: **ACCEPTED** (no caveats)

Every attack failed. Sign convention in Lean matches the fuzzer byte-for-byte. Degenerate cases (V=∅, E=∅, W=∅, W=E) all type-check. Axiom footprint is minimal. Stage-2 fuzz (3727/3727 at 9.7e-15) is faithfully captured by the committed Lean statement.

## A. Definition drift — NO LOOPHOLE

- **A.1 Matrix vs LinearMap.** `#check @ConnGraph.laplacian` returns `(G : ConnGraph) → Bool → Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ`. Flat real matrix, not a LinearMap abstraction. Same object as the fuzzer's `L_mob`.
- **A.2 Sign convention.** Fuzzer at `sheaf_beta/fuzz.py:230`: off-diag = −1 for non-wrap, +1 for wrap. Lean's `signedLaplacianMobius` (`KernelDimension.lean:195`): `if G.wrap e then 1 else -1`. **Lean matches the fuzzer byte-for-byte.**
- **A.3 Fibre indexing.** Lean's `(u,i)(v,j)` entries produce the same 2n×2n matrix as the fuzzer's `L[2u:2u+2, 2v:2v+2]` slicing. The `Matrix.reindex` to `V ⊕ V` is absorbed by `charpoly_reindex`.

## B. Vacuous / degenerate cases — DEGENERATE BUT CORRECT

- **B.1 V=∅.** Compiled `ConnGraph` with `V := Empty` and derived M7 via the committed theorems. 0×0 charpoly = 1, and `1 = 1·1`. Works.
- **B.2 Edgeless Fin 3.** Both Laplacians are zero; charpoly `X^3` factors as `X^3 · X^3`. Compiled.
- **B.3 W=∅.** Proved `K3NoWrap.signedLaplacianMobius = K3NoWrap.scalarLaplacian` by `ext` + case-split. M7(true) and M7(false) agree up to definitional unfolding. No drift.
- **B.4 W=E on K₃ (unbalanced).** Compiled Lean example for K₂-all-wrap; numpy on K₃-all-wrap: `L_s=[0,3,3]`, `L_sig=[1,1,4]`, `L_möb=[0,1,1,3,3,4]`, union-diff **1.1e-15**. M6 holds on unbalanced signed Laplacians.

## C. Proof-dependency audit — NO LOOPHOLE

- **C.1 `fromBlocks` square.** Both diagonal blocks are `Matrix G.V G.V ℝ`, same square index type. Preconditions satisfied.
- **C.2 `charpoly_conj_of_isUnit_det`.** `laplacian_decomposes` yields `P.det ≠ 0`; over ℝ `Ne.isUnit` gives `IsUnit`.
- **C.3 `Matrix.charpoly_monic`.** Needs `[Nontrivial R]`, not nontriviality of index. ℝ is nontrivial; works even for `n = Empty` (charpoly = 1, still monic).
- **C.4 Axioms.** `#print axioms` on all five landed theorems returned exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`. No custom axioms.

## D. Surface / maintainability — NO LOOPHOLE

- `p.roots` is genuine `Multiset ℝ` (confirmed by type ascription).
- All arguments explicit; style matches `laplacian_decomposes`, `signedLaplacianMobius_isSymm`.
- No brittle `rfl` / `decide` in L16. Only `rw`, `simpa`, and a compositional `mul_ne_zero` discharge.

## E. Flat-case — NO LOOPHOLE

Numpy on n=4 with edges {(0,1),(1,2),(2,3),(0,2)}: charpoly coefficients of `L_flat = L_s ⊗ I₂` vs `(charpoly L_s)²` via `np.convolve` agreed to **9.66e-13**. `flat_charpoly_eq_scalar_sq` is correct.

## Recommended follow-ups (nice-to-have, non-blocking)

1. **Smoke-test file** exercising `mobius_charpoly_eq_scalar_times_signed` on `emptyConn`, P_3, and K₃-all-wrap — catches future regressions in definitional unfolding.
2. **Docstring cite** `Matrix.charpoly_monic` (Mathlib `LinearAlgebra/Matrix/Charpoly/Coeff`) in `mobius_charpoly_roots_eq_union` for discoverability.
3. **Future-work note.** L16 docstring already flags that `charpoly.roots` ≠ eigenvalue multiset unless the charpoly splits. For real-symmetric matrices it does, but that plumbing isn't invoked here — worth an explicit future-work note for the follow-on B1/B6/B17 corollaries.

## Prompt-hygiene note (self-drift caught)

The Stage-4 task prompt mis-stated the fuzzer sign convention as "−1 on wraps". Reality is `+1 on wraps, −1 on non-wraps`. Lean is correct; only the prompt drifted. Worth tightening downstream stage prompts to pull convention direct from the Lean source rather than paraphrasing.

## Artifacts

- Report: this file.
- Scratch probe files (`adv_probe.lean`, `adv_probe2.lean`) were created in project root, exercised against `lake env lean`, and deleted. No persistent changes.
