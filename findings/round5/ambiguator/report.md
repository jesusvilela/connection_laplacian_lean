# AMBIGUATOR-R5 — paper rescan

**Date:** 2026-04-22. **Target:** `paper/paper.tex` (1384 lines, post-R4).

## A. New priority-ordered ambiguities

### [HIGH] A1 — Reproducibility numbers inconsistent; "zero failures" overclaim

Three sweep counts in different places:
- Abstract: 3,456 (n ≤ 5 exhaustive) and 456,950 (n ≤ 7).
- Appendix A: 176,169 (n ≤ 8).

The n ≤ 8 pass is **not** exhaustive (random-graph sampling on n=7,8; wrap caps), and reports **20 `B_cover_charpoly` failures** at n=8 which Appendix A nonetheless called "zero numerical violations". Also line 198 overclaims "exhaustive numerical verification".
**FIX APPLIED (R5)**: Reproducibility paragraph now explicitly distinguishes exhaustive (n ≤ 5) vs sampled (n ∈ {6,7,8}) slices, and discloses the 20 condition-number near-misses with their bound (7.3 × 10⁻³) and their non-impact on the exact Lean identity.

### [HIGH] A2 — Dangling `\ref{prop:scalarLaplacian-kernel}` (lines 1212, 1275)

No matching `\label` exists. Target is `thm:scalar-ker` (Theorem 5.1, line 697).
**FIX APPLIED (R5)**.

### [MED] A3 — Dangling `\S\ref{sec:cycle}` (line 269)

Actual label is `sec:cycles` (line 784).
**FIX APPLIED (R5)**.

### [HIGH] A4 — Appendix A table has wrong Lean identifiers + overblown opener

Verified by grep in `ConnectionLaplacian/*.lean`:
- Line 1278: `flatLaplacian_kernel_dim` does not exist → `laplacian_decomposes`.
- Line 1292: `strict_inequality_when_unbalanced` does not exist → `mobius_kernel_strict_iff_general`.
- Line 1276: `scalarLaplacian_kernel_dim` lives in `KernelDimension.lean`; paper says `KernelDim.lean` (explained by opener's abbreviation note).
- Line 1280: `laplacian_kernel_dim_decomposes` lives in `L8_Recognition.lean:87`, not `KernelDim.lean`.
- Line 1304: "Lean port scheduled L13_PSD.lean" — outdated; file exists with full proof.
- Line 1319: cycle-ew "deferred" — outdated; `L14_CycleEw.lean:135` holds `cycle_isBalanced_iff_even_wrap_weak`.
- Opener overclaims "Every named theorem … has a corresponding Lean 4 declaration"; at least 10 named items are absent from the table.

**FIX APPLIED (R5)**: all rows corrected, row 1319 now points to `L14_CycleEw.lean`, opener rewritten to admit that subsidiary lemmas are implicit.

### [MED] A5 — Script path wrong (line 879)

`fuzzer/fuzz.py` → actual is `findings/round2/fuzzer/fuzz.py`.
**FIX APPLIED (R5)**.

### [HIGH] A6 — Example 9.3 β-change rule wrong (lines 1237-1240)

Paper stated: "−1 when both endpoints lie in balanced components and 0 otherwise". Case analysis:
- balanced + balanced → merged balanced → −1.
- balanced + unbalanced → merged unbalanced → the balanced component is *lost* → −1.
- unbalanced + unbalanced → 0.

Correct rule: "−1 when **at least one** endpoint lies in a balanced component".
**FIX APPLIED (R5)** — with an explanatory parenthetical on the mixed case.

### [MED] A7 — Example 5.5 compares kernel dimensions of differently-sized matrices

L_Mob acts on C^{2V}, L_scalar on C^V. Dimensions 6 vs 3 cannot be directly compared.
**FIX APPLIED (R5)**: example now spells out that the kernels sit in different ambient spaces, so the putative identity already fails on dimensional grounds.

### [MED] A8 — Hand-wave in proof of Lemma 4.4 (`lem:merge-if-unbalanced`, lines 653-664)

"ε₀ constructed as characteristic function of the D_⊥-fibre witnesses balance" asserted but never verified on edges of C. Lemma 4.3 invoked in reverse direction without argument. The Lean proof uses a different (deck-transformation) route. **NOT YET PATCHED** — flagged for R6.

### [LOW] A9 — Case-count mismatch (line 458)

"Split B_{u,v} into three structural cases" but (a)-(d) are four.
**FIX APPLIED (R5)**.

### [LOW] A10 — `\top`/`\bot` overloaded

Used for both matrix transpose (lines 220-221) and Boolean sheet index (line 420+). **NOT YET PATCHED**; cosmetic.

### [LOW] A11 — `\operatorname{Mob}` vs `\mathrm{Mob}` inconsistency

Sections 1-3 vs 5+ differ. **NOT YET PATCHED**; cosmetic.

### [LOW] A13 — Thm 5.5 vacuous-balance scope

Empty-graph strict-inequality failure deserves a forward reference to Remark 4.2(b). **NOT YET PATCHED**.

### [LOW] A14 — Cor 6.3 conflates two criteria on C_n

"n odd" (spectral) and "|W| odd" (homological) happen to coincide on C_n with single wrap. **NOT YET PATCHED**.

## B. Status of R3/R4 residuals

- **B4 (cocycle / cochain unification):** RESOLVED — all four mentions read "1-cochain … automatically a 1-cocycle".
- **B5 (Fourier Re/Im at k=0, k=n/2):** Lines 791-792 claimed real-valued eigenvectors are `Re(e_k)` and `Im(e_k)`; at k=0 and (for even n) k=n/2, `Im` vanishes.
  **FIX APPLIED (R5)**: parenthetical qualifies that those two indices each contribute only a single real eigenvector.

## Net

4 HIGH + 3 MED bugs found; all HIGH patched plus A5/A7/A9 and B5. A8, A10, A11, A13, A14 deferred (cosmetic or needing deeper rewrite). Paper recompiles cleanly at 192 KiB.
