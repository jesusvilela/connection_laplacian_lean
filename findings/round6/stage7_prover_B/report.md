# PROVER-B R6 Stage 7 — L17 trace / Frobenius / shifted-det bundle

**Date:** 2026-04-22. **Outcome:** Tier A 5/5 landed. Tier B (S6–S9 β-Lipschitz) deferred to R7. **File:** `ConnectionLaplacian/L17_TracesAndLipschitz.lean` (218 LOC). **Build:** green. **Axioms:** clean.

## Landed theorems (all in namespace `ConnectionLaplacian.ConnGraph`)

| id | theorem name | line | body LOC | strategy |
|----|--------------|-----:|---------:|----------|
| **S1** | `shiftedDet_factorises` | 62 | 12 | evaluate M7 at α; helper `charpoly_eval_eq_det_sub` via `eval_det` + `matPolyEquiv_charmatrix` |
| **S5** | `trace_laplacian_mobius` | 79 | 25 | diagonal of `laplacianBlock` = `deg v • I₂`; sum over `V × Fin 2` = 2 · handshake |
| **S3** | `trace_sq_laplacian_decomposes` | 131 | 45 | `laplacian_decomposes` + similarity-invariance, helpers `trace_reindex`, `trace_fromBlocks_diag`, `fromBlocks_multiply` |
| **S4** | `frobenius_laplacian_decomposes` | 181 | 17 | `tr(Mᵀ · M) = tr(M · M)` via `IsSymm`; reduce to S3 |
| **S2** | `trace_mul_scalar_signed_eq` | 203 | 11 | polarisation: `2 · tr(L_s · L_sig) = tr((L_s + L_sig)²) − tr(L_s²) − tr(L_sig²)` via `trace_mul_comm` |

**Sum:** 110 body LOC for the five theorems (plus ~108 LOC preamble + docstrings + helpers).

## Axiom verification

All five theorems depend only on `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`, no custom axioms. Verified via `#print axioms` on each theorem against a freshly compiled `check_axioms.lean` (now deleted).

## Files touched

- **new:** `ConnectionLaplacian/L17_TracesAndLipschitz.lean` (218 LOC).
- **wire-up:** `ConnectionLaplacian.lean` gains `import ConnectionLaplacian.L17_TracesAndLipschitz`.
- **no other modifications** to Lean source or paper.

## Tier B deferred — rationale

The β-Lipschitz bundle (S6–S9) blocks on missing API, not on mathematical difficulty.

**S6 contraction-Lipschitz, S7 vertex-deletion**
Require constructors `G.contract e` and `G.deleteVertex v` on `ConnGraph`. Currently only `eraseEdge` exists (L15). Building these plus:
- wrap-quotient bookkeeping (how does `W` transport across contraction?),
- Weyl-level `finrank`-interlacing across distinct vertex types (the contracted graph has `V \ {u}` as its vertex set),

would exceed the 50-LOC-per-theorem budget. **Recommend R7 first adds `contract` and `deleteVertex` to `Basic.lean` with their wrap-transport rules; then S6/S7 land as corollaries of L15's machinery.**

**S8 bridge-wrap-flip preserves β, S9 non-bridge wrap-flip Lipschitz**
Require `flipWrapAt : ConnGraph → edgeSet → ConnGraph` plus switching-equivalence of balance structure under endpoint flip. Not in current API. Same R7 prerequisite: add `flipWrap` constructor to `Basic.lean`, then S8 follows from M2 (switching-invariance of β) in ~5 LOC and S9 from the rank-2 perturbation argument in ~20 LOC.

## Corollaries unlocked

S1 (`shiftedDet_factorises`) with M6/M7 now provides a **one-line path** to:

- C2_t{0.1, 0.5, 1, 2} heat-trace additivity `tr(e^{−t L_möb}) = tr(e^{−t L_s}) + tr(e^{−t L_sig})` — sum over M6 multiset roots.
- C4_a{0.5, 1, 2} resolvent-trace additivity — sum over M6 multiset roots.
- C1_k ∈ {1..10} trace-power identities — Newton's identities on the charpoly factorisation give these; S3 already nails k=2 directly.

These corollaries are not in L17 but are **ready to land** in ~3 LOC each if needed.

## Constraints honoured

- NO `sorry`. NO new axioms. NO `native_decide`.
- NO modification of existing Lean files except the single import line in `ConnectionLaplacian.lean`.
- NO paper edits.
- 218 LOC ≤ 250 budget.
- `lake build` green on full project (1833/1833).
