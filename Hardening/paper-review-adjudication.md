# Adjudication: paperreview.ai review vs. the current manuscript and formalization

**Date:** 2026-10-15. **Input:** two AI-generated reviews of
`paper/paper.tex` (a NeurIPS-style summary review and a detailed line-by-line
review). Per the review site's own warning, "reviews are AI generated and may
contain errors." Every substantive claim below was adjudicated against three
independent evidence sources: (a) the current `paper.tex` text, (b) numerical
computation with the independent paper-only implementation
(`findings/round8/independent_impl.py`), and (c) the Lean sources. Verdicts:
**CONFIRMED** (real issue, act on it), **REFUTED** (claim is false for the
current manuscript), **STALE** (true of an older draft, already fixed),
**PARTIAL** (mixed), **EDITORIAL** (cosmetic).

## Mathematical claims

### 1. "Corollary 7.3 wrongly says the Möbius kernel drops iff n is odd" — **STALE / REFUTED for the current manuscript**

The current `paper.tex` Section 7 (lines 857–870) states the corollary as:
*"Let G = C_n with n ≥ 3 and W = {{0,1}} … Then Ker L^sg(C_n) = 0,
equivalently β(C_n) = 0, and hence dim Ker L_Mob = 1 < 2 … for every n ≥ 3"*
— the **correct universal statement** — followed by a remark that the
parity-in-n behaviour belongs to the **all-edges-wrap** pattern W = E(C_n).
Numerical adjudication with the independent implementation (n = 3..14):

| W | ker L^sg | pattern |
|---|---|---|
| {0,1} (single wrap) | 0 for **every** n = 3..14 | drops always, β = parity of #W |
| E(C_n) (all wraps) | 1 iff n even, 0 iff n odd | "iff n odd" lives here |

The reviewer's *mathematics* is right (2k+1 odd can never equal 2mn even), and
it agrees with the current text; the alleged quote "strictly drops iff n is
odd" does not appear in the current manuscript. Either the review targeted a
pre-revision draft or it hallucinated the quote.

### 2. Theorem 7.2 proof sketch: "both commute with the Z/n-action" — **CONFIRMED (wording), EDITORIAL-to-MINOR**

The sketch's opening sentence overclaims: L^sg(C_n) with a single wrap edge is
not circulant pre-gauge (the reviewer's twisted-shift analysis is correct).
The sketch itself immediately applies the gauge transformation that repairs
this, and the paper's own Remark notes the Lean proof "carries out the Fourier
algebra without appealing to gauge equivalence" — and indeed
`CycleSpectrum.lean` proves `scalarCycle_eigenvalue` / `signedCycle_eigenvalue`
(hypotheses `3 ≤ n`) directly, per-k, by explicit eigen-equation verification.
Recommended fix: one sentence ("prior to the gauge transformation L^sg is not
circulant; the twisted shift S_sg with S_sg^n = −I diagonalises it").

### 3. Missing n ≥ 3 hypothesis — **PARTIAL**

Theorem 7.1/7.2 statements in the text do not carry an explicit n ≥ 3 (the
corollary does; C_2 degenerates as the reviewer notes). The Lean side is
already correct: both eigenvalue theorems are stated with `hn : 3 ≤ n`.
Add "n ≥ 3" to the theorem statements.

### 4. Remark 6.5: Betti off-by-one and bridge-in-W counterexample — **CONFIRMED (two real errors)**

Current text: "(★) … fails as soon as dim H¹(G;Z/2) > 1, i.e. as soon as
|E| > |V| − #comp(G)."

- **Off-by-one confirmed:** dim H¹ = |E| − |V| + #π₀, so "dim H¹ > 1" ⇔
  |E| > |V| − #π₀ + 1. The paper's inequality describes dim H¹ ≥ 1.
- **Bridge-in-W confirmed numerically** (independent implementation): on
  P₄ with a single wrapped middle edge (a bridge), #W = 1 is odd, so (★)
  predicts ker = 0, but ker L^sg = β = 1. Same for all three edges wrapped.
  Trees have dim H¹ = 0, so the "fails only when dim H¹ > 1" scope claim is
  false. (The paper's own Theorem 10.1 implies this — the remark's scope just
  was never reconciled with it.)
- Suggested corrected scope: (★) holds on a component iff the component is
  unicyclic-or-tree **and** no bridge of it lies in W; equivalently per the
  reviewer, "every component carrying wrap edges is a simple cycle."

### 5. Kronecker factor ordering in eq. (1) — **CONFIRMED (third independent confirmation)**

`Φ(e) ⊗ 1_e` is fibre-major while `D ⊗ I₂` is vertex-major. Found
independently by our round-8 paper-only implementer (who had to resolve it to
make the implementation type-check) and now by the reviewer. Erratum: write
`Σ_e 1_e ⊗ Φ(e)`.

## New finding surfaced during adjudication (not in the reviews)

**`CycleSpectrum.lean` contains two vacuous public "spectrum" theorems.**
`flat_cycle_spectrum` (line 659) asserts, for every k, the existence of two
linearly independent sheet-indicator vectors — true for trivial reasons,
no Laplacian involved — and `mobius_cycle_spectrum` (line 679) asserts
`∃ v, v ≠ 0 ∧ True` twice, proved by `(1 : ℕ).ne_zero`: vacuous. These names
invite a reader to mistake them for the formalized Theorems 7.1/7.2. The
paper (Remark `rem:cycle-spectrum-lean`) is honest that only the per-k
eigenvalue identities are formalized (`scalarCycle_eigenvalue`,
`signedCycle_eigenvalue` — real, public, `3 ≤ n`) and that the multiset
assembly is not a named Lean theorem; the two vacuous declarations are dead
weight that should be deleted or renamed. Severity: MEDIUM (misleading
naming), no mathematical content affected.

## Editorial / provenance claims

| Claim | Verdict | Evidence |
|---|---|---|
| Fuzzer-count discrepancies (456,950 vs 176,169 vs 3,456) | **STALE/REFUTED** | none of these numbers appear anywhere in the current `paper.tex`; the abstract contains no configuration counts |
| No public code URL / DOI in the manuscript | **CONFIRMED** | `paper.tex` has no URL/DOI; the repo README carries Zenodo DOI 10.5281/zenodo.19695396 — add it to the paper |
| Section 8 dependency graph omits L9–L17; Appendix omits CycleSpectrum entries | **CONFIRMED** | Section 8 still shows the old linear spine Basic→…→L8 + lateral CycleSpectrum; Appendix A table lacks `flat/mobius_cycle_spectrum`-family rows (see also the vacuous-theorem item above) |
| Undefined swarm shorthand (C1, C2, τ, R5, NEGATOR) | **CONFIRMED** | used at lines 1337/1379/1480/1535 without definition |
| Tree vs forest terminology (Thm 10.1/Cor 10.2) | **CONFIRMED (minor)** | Thm 10.1 titled "Tree balance" but proves the forest statement; Lean side is precise (`IsTree` hypotheses on the L11 main theorems, component-wise conclusions) |
| Möbius/Mobius umlaut inconsistency | **CONFIRMED** | mixed throughout prose |
| Appendix table column overflows (two rows) | plausible, not re-verified in PDF render | — |
| Example 11.1 uses ℂ^{2V} vs ℝ elsewhere; `L_scalar` subscript | **CONFIRMED** | consistent with text inspection; immaterial for real symmetric matrices but worth aligning |
| Known-result attribution gaps (Zaslavsky, Bilu–Linial, Singer, signed-Laplacian literature) | **legitimate scholarly feedback** | out of scope for this adjudication (no mechanical verdict); the NeurIPS-style review's related-work suggestions are reasonable |

## Bottom line

The two reviews contained **two genuinely correct mathematical findings**
(Remark 6.5 off-by-one + bridge scope; the gauge-sketch wording), **one
third-party confirmation** of our round-8 Kronecker-ordering finding, several
**correct editorial items**, and — importantly — **one headline mathematical
accusation that does not apply to the current manuscript** (the cycle
corollary was already corrected in the text, and the numerics plus the Lean
`3 ≤ n` eigenvalue theorems side with the current version). Adjudication also
surfaced one new internal item: the two vacuous cycle "spectrum" theorems in
`CycleSpectrum.lean` that should be removed or renamed.

Suggested errata list (for the paper): eq. (1) factor order; Remark 6.5
inequality (+1) and bridge scope; n ≥ 3 on Thms 7.1/7.2; gauge-sketch
sentence; Section 8 module list; Appendix index rows; define swarm shorthand;
add DOI/URL; unify Möbius spelling. For the Lean repo: delete/rename the two
vacuous theorems.
