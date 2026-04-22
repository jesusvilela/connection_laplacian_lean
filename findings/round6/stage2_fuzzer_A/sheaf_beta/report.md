# FUZZER-A R6 Stage 2 — Sheaf-section β (spectral masters at scale)

**Date:** 2026-04-22. **Envelope:** n=6 exhaustive over all 156 iso-classes (WL hash + brute-perm iso confirmation), 24-wrap-cap per class → 3,507 configs; plus n=7 random sample of 220 configs across densities {0.20, 0.35, 0.50, 0.65, 0.85}. Plus 6 mpmath prec=50 spot-checks on M6.

**Stack:** numpy + mpmath (prec=50), no networkx. Seed 20260428. ~5.7 s n=6 + ~0.6 s n=7.

## Summary — all nine claims HOLD

| claim | tested | passed | max rel diff | verdict |
|-------|-------:|-------:|-------------:|---------|
| **M6** spec-union `spec(L_möb) = spec(L_s) ⊎ spec(L_sig)` | 3727 | 3727 | **1.55e-15** | HOLDS |
| **M7** charpoly product `p_{L_möb} = p_{L_s} · p_{L_sig}` | 3727 | 3727 | **9.70e-15** | HOLDS |
| **B2** mixed trace `tr(L_s L_sig) = Σdeg² + 2m − 4|W|` | 3727 | 3727 | **0 exact** | HOLDS |
| **B14** single-flip Weyl stability (≤ 2) | 29745 | 29745 | bound tight at 2.0 | HOLDS |
| **B15** multi-edge interlacing (k ≤ 3) | 46990 | 46990 | 0 | HOLDS |
| **B16** G conn ∧ β=0 ⇒ λ_min(L_sig) > 0 | 2308 | 2308 | — | HOLDS |
| G15 `dim ker L_sig = β` (landed; sanity) | 3727 | 3727 | 0 | HOLDS |
| B9 `dim ker L_möb = #comp + β` (landed; sanity) | 3727 | 3727 | 0 | HOLDS |
| B21 `Σ sign(eig L_sig) = n − β` (landed; sanity) | 3727 | 3727 | 0 | HOLDS |

mpmath prec=50 six spot-checks on n=6 (various (m, |W|)): M6 max multiset diff 1.5e-14 → 5.0e-14. Round-off floor only, far inside 1e-10 target. Conclusion: **no precision-masked near-misses.**

## Surprises

**None.** Zero counterexamples across 3727 base configs and 76,735 derived probes (the B14/B15 columns accumulate per-edge and per-subset expansions). The already-landed Lean theorems G15/B9/B21 each pass exactly (0 diff).

**Sharpness observation:** B14 saturates. Max |Δλ_i| under single wrap-flip is **exactly** 2.0, so the rank-2 Weyl bound is tight; any Lean proof must allow equality.

## Stage-3 PROVER-A recommendation

1. **M6 spec-union — top target.** Proof strategy: explicit orthogonal `U ∈ O(2n)` given by fibre-wise Hadamard rotation `(e_u ⊗ e_0 ± e_u ⊗ e_1)/√2`, with case split on wrap vs non-wrap edges. Yields `U^T L_möb U = L_s ⊕ L_sig` (block-diagonal). Landing this collapses B1, B6, B12, B13, B17, B19, B20 from the Stage-1 sheaf-β report into one-line corollaries.
2. **M7 charpoly product** falls out as `det(xI − L_möb) = det(xI − L_s) · det(xI − L_sig)` once M6 is in hand; alternatively provable independently via `Matrix.charpoly_blockDiagonal` if the orthogonal change-of-basis is algebraically expensive in Lean.
3. **B2 mixed trace** — cleanest combinatorial identity, no spectrum at all. ~5 Lean lines if the `L_s`, `L_sig` matrix-entry lemmas already exist in `L4_Laplacians.lean`.
4. **B14/B15** Weyl/interlacing bundle — natural follow-on once M6 is in and standard perturbation lemmas are available.
5. **B16** — corollary of PSD (L13) + G15 (kernel-dim) after rearrangement.

## Artifacts on disk

- `fuzz.py` — 24.8 KB, numpy+mpmath fuzzer.
- `results.json` — structured per-claim counts + spot-check record.
- `run.log` — full verdict table & progress trace (~2 KB).

No Lean files touched. No paper edits.
