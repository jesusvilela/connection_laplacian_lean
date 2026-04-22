# ADVERSARIAL-B R6 Stage 8 — red-team of L17 bundle

**Date:** 2026-04-22. **Target:** `ConnectionLaplacian/L17_TracesAndLipschitz.lean` (218 LOC). **Overall verdict: ACCEPTED-WITH-CAVEATS.**

All five theorems are provably correct, axiom-clean (`[propext, Classical.choice, Quot.sound]`), no `sorry` / `native_decide` / `admit`, `lake build` green (1833/1833), and edge-case-stable. One scope caveat on S2 — documentation boundary, not a logic bug.

## Per-attack verdicts

| attack | verdict |
|--------|---------|
| A.1–A.4 (scalar-coercion / type drift) | CLEAN |
| B.1–B.3 (reindex / similarity) | CLEAN |
| C (S2 polarisation vs combinatorial C10 shape) | **CAVEAT** |
| D (numerical cross-check, 5 graphs × 5 identities) | CLEAN |
| E (Empty and Fin 1 `ConnGraph` instances) | CLEAN |

## A. Scalar-coercion / type drift — CLEAN

- **A.1** S1 statement is type-explicit: `α • (1 : Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ)`. `α • 1` unambiguously means `α · I`. Numerics match for α ∈ {0, 0.5, 1, 2, −1.3} on K₃, K₃+W, P₄+W, C₅+W, empty — all within rel diff ≤ 2·10⁻¹⁵.
- **A.2** S5 is literally `(G.laplacian true).trace = (4 * G.graph.edgeFinset.card : ℝ)` — literal 4 · |E|, not the 2·handshake intermediate. Closes via `sum_degrees_eq_twice_card_edges` + `ring`.
- **A.3** File uses `M * M` explicitly (not `HPow.hPow`), sidestepping any unfolding issue.
- **A.4** S4 is stated in elementary `(Lᵀ · L).trace` form, not a Mathlib `‖·‖_F²` norm. Defeq-clean. Closes via `IsSymm` + S3.

## B. Reindex / similarity — CLEAN

- **B.1** `trace_reindex` helper uses `reindex e e` (same equiv both sides) — genuine trace invariance.
- **B.2** `laplacian_decomposes` (`KernelDimension.lean:345–354`) uses `reindex G.prodFinTwoEquivSum G.prodFinTwoEquivSum` on both row and column sides. The specific `P` happens to be involutive (Hadamard-like `R = [[1,1],[1,−1]]/√2`) but the L17 proof does NOT rely on this — it only invokes `Matrix.nonsing_inv_mul` with `hPdet ≠ 0`.
- **B.3** `fromBlocks_multiply` usage (line 173) correctly produces the block-diagonal square; zero-block simp clears cross-terms.

## C. S2 direction — CAVEAT

The landed theorem `trace_mul_scalar_signed_eq` states:
  `2 · tr(L_s · L_sig) = tr((L_s + L_sig)²) − tr(L_s²) − tr(L_sig²)`

This is **pure polarisation** — true for any two matrices of matching shape. It is **strictly weaker** than the Stage-5/6 fuzzer's combinatorial C10:
  `tr(L_s · L_sig) = tr(L_s²) − 4 · |W|`

The L17 docstring and PROVER-B report correctly label the shape as "polarisation form". Downstream consumers expecting the combinatorial form need a ≤ 20 LOC bridge lemma.

**Recommended R7 follow-up (non-blocking):** add
```
trace_mul_scalar_signed_combinatorial :
  (G.scalarLaplacian * G.signedLaplacianMobius).trace
  = (G.scalarLaplacian * G.scalarLaplacian).trace - 4 * (wrap edge count : ℝ)
```
≤ 20 LOC via direct expansion of `(L_s · L_sig)_{vv}` summing over wrap vs non-wrap neighbours. Does **not** block the M7-based C1 / C2 / C4 trace-power / heat / resolvent corollaries.

## D. Numerical cross-check — CLEAN

Built `L_möb` on `V × Fin 2` directly (`A ⊗ I₂` on flat edges, `A ⊗ σₓ` on wrap edges, `D ⊗ I₂` on diag) and verified S1 (five α values), S3, S4, S5, S2 polarisation, **and** C10 combinatorial, on K₃, K₃+W={(0,1)}, P₄+W={(1,2)}, C₅+W={(0,1),(2,3)}, n=1 empty. All match to machine precision. Attack-D target K₃+W={(0,1)}: `tr(L_s · L_sig) = 14 = 18 − 4 · 1` ✓.

## E. Edge-case `ConnGraph` instances — CLEAN

Constructed `emptyG` (V = Empty) and `oneVertexG` (V = Fin 1, E = ∅) and specialised all relevant theorems. `lake env lean` on scratch witness returns silent (no errors). S1 reduces to `1 = 1 · 1` on empty-V and `α² = α · α` on n=1.

## Scratch files

Created and deleted: `adv_B_check_axioms.lean`, `adv_B_probe.py`, `adv_B_edgecase.lean`. No artefacts remain in project root.

## Summary for Stage-11 integrator

- **L17 bundle accepted.** Zero logic loopholes.
- **One R7 carry-over:** add `trace_mul_scalar_signed_combinatorial` bridge lemma (≤ 20 LOC) to recover the combinatorial form of C10 that the fuzzer pinned.
