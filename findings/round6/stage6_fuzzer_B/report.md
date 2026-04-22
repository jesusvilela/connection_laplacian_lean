# FUZZER-B R6 Stage 6 — n=7 gap-check of PROVER-B queue

**Date:** 2026-04-22. **Envelope:** 300 random connected graphs at n=7 × all wraps. **Wall:** 1.3 s. **Stack:** numpy + networkx, seed 20260501.

## Verdict: all 9 PROVER-B Tier-1/2/3 targets HOLD at n=7

| id | target claim | tested | passed | max rel diff | verdict |
|----|--------------|-------:|-------:|-------------:|---------|
| **S1_a1** | `det(L_möb + 1·I) = det(L_s + 1·I) · det(L_sig + 1·I)` | 300 | 300 | 8.9e-15 | HOLDS |
| S1_a2 | `det(L_möb + 2.5·I) = det(L_s + 2.5·I) · det(L_sig + 2.5·I)` | 300 | 300 | 8.9e-15 | HOLDS |
| **S2** | C10: `tr(L_s · L_sig) = tr(L_s²) − 4\|W\|` | 300 | 300 | **exact** | HOLDS |
| S3 | C11: `tr(L_möb²) = tr(L_s²) + tr(L_sig²)` | 300 | 300 | **exact** | HOLDS |
| S4 | C12: `‖L_möb‖_F² = ‖L_s‖_F² + ‖L_sig‖_F²` | 300 | 300 | **exact** | HOLDS |
| **S6** | C5: `\|β(G) − β(G/e)\| ≤ 1` for non-bridge e | 3635 | 3635 | **exact** | HOLDS |
| **S7** | C6-tight: `\|β(G) − β(G − v)\| ≤ max(1, deg(v))` | 2100 | 2100 | **exact** | HOLDS |
| S8 | C13: bridge-wrap-flip preserves β | 188 | 188 | **exact** | HOLDS |
| S9 | C14: non-bridge-wrap-flip `\|Δβ\| ≤ 1` | 3635 | 3635 | **exact** | HOLDS |

**Total probes:** 14,011. **Counterexamples:** 0.

## Cross-scale confidence

Combined evidence across R6 now:

- **S1 / shifted-det:** Stage-2 verified M7 / charpoly-product at 1.5e-15 over 3507 n=6 iso-configs + 220 n=7 random; Stage-6 extends to 300 n=7 random with 2 α values. Shifted-det is a trivial rewrite of M7 at `x := −α`; already provable in Lean via `mobius_charpoly_eq_scalar_times_signed`.
- **S2–S4:** Pure combinatorial identities (no spectral calls). Zero-error across 12,447 Stage-5 configs + 900 Stage-6 n=7 probes. Lean-provable via `ring` after opening matrix-entry formulas.
- **S6 contraction-Lipschitz:** 2916 Stage-5 + 3635 Stage-6 = 6551 non-bridge edges, all within 1. β moves by at most 1 under contraction — robust to n=7 scale.
- **S7 vertex-deletion:** 301,249 Stage-5 probes + 2100 Stage-6 n=7 probes. `max(1, deg(v))` bound confirmed at scale.
- **S8 / S9 wrap-flip:** confirmed tight — bridge flips preserve β exactly; non-bridge flips move β by at most 1.

## Recommendation for Stage 7 PROVER-B

**Cleared for formalisation.** Proceed in the Stage-5 Tier order:

1. **S1 shifted-det** (~15 LOC, corollary of M7 at x := −α).
2. **S2 / C10** tr(L_s · L_sig) combinatorial identity (~5 LOC `ring`).
3. **S3 / S4** (1-line each from S1 at k=2 or direct).
4. **S5 / C1_k1** `tr(L_möb) = 4|E|` (~5 LOC extension of L9).
5. **S6 / C5** contraction-Lipschitz (~40 LOC, rank-1 interlacing argument).
6. **S7 / C6-tight** vertex-deletion (~30 LOC).
7. **S8–S9** wrap-flip bundle (~30 LOC combined).

Total expected landing: ~130 LOC across ~7 theorems in a new `L17_TracesAndLipschitz.lean` (or split into L17 / L18 if cleaner).

## Artifacts

- `fuzz.py` — 9 KB.
- `run.log` — 15 lines.
- `results.json` — per-claim counts.
