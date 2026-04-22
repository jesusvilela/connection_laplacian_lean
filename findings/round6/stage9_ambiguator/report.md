# AMBIGUATOR R6 Stage 9 — paper ambiguity / citation audit

**Date:** 2026-04-22
**Target:** `H:\NP Completeness Bunny UTAI study\connection_laplacian_lean\paper\paper.tex` (1416 lines, read-only)
**Verdict:** No blocking defects. 5 HIGH / 6 MID / 5 LOW findings across 16 items. The paper compiles cleanly and every `\ref{...}` resolves. The dominant class of issues is **missing citation opportunities** for L16/L17 landings. There is **no deprecated "future work" prose** — Category E is empty, which means R6 additions are purely additive.

---

## Category A — Ambiguity / typo / notation (4)

### A1 [MID]  `\operatorname{Spec}\Lscalar(C_n) = {...}` followed by "each eigenvalue e_k an eigenvector"
- **Line 804:** `each eigenvalue $\mathbf{e}_k$ an eigenvector.`
- **Issue:** `e_k` is the Fourier *vector*, not the eigenvalue; and the sentence is missing a verb ("is"/"being").
- **Suggest:** `with eigenvector $\mathbf{e}_k$ for eigenvalue $2-2\cos(2\pi k/n)$.`

### A2 [MID]  Abstract vs. Reproducibility fuzzer totals disagree
- **Lines 121–124** (abstract): `fuzzer sweep at orders $n\le 7$ ($456{,}950$ configurations, also zero disagreements)`
- **Lines 1355–1359** (reproducibility): `Continuous fuzz-sweeps over a total of $176{,}169$ connection-graph configurations — exhaustive on simple graphs for $n\le 5$, with wrap-subset and random-graph sampling on $n\in\{6,7,8\}$`
- **Issue:** Two different totals (456,950 vs 176,169) for what the reader sees as the same artefact. If these are different sweeps (e.g., wrap-subset exhaustive vs. random), label them so.
- **Suggest:** Reconcile explicitly. Likely abstract pre-dates the n=8 extension, or 456,950 is per-claim and 176,169 is configurations.

### A3 [LOW]  Matrix-product notation inconsistency
- **Line 224:** `$\widehat R\,\widehat R = 2\,\II_2$` (thin-space juxtaposition).
- **Line 311:** `$P\cdot P = ...$` (explicit `\cdot`).
- **Suggest:** Unify. Either juxtaposition throughout (with `\,`) or `\cdot` throughout.

### A4 [LOW]  `\II` (identity matrix) vs `\mathbf{1}_{...}` (indicator) overload never flagged at first use
- `\II_k` first appears line 139; `\mathbf{1}_{e\in W}` first appears line 155. Both typographically resemble "1".
- **Suggest:** One-line notation paragraph in §2 explicitly: "$\II_k$ denotes the $k\times k$ identity matrix; $\mathbf{1}_{P}$ the 0/1 indicator of proposition $P$."

---

## Category B — Missing R6 landings / claims now upgraded (5)

### B1 [HIGH]  Thm 7.5 (`thm:cover-charpoly`) now has a direct-bundle counterpart in L16
- **Lines 1037–1049.** Paper states: `det(λI − L̃) = det(λI − L_sc) · det(λI − L_sg)` (through the cover).
- **R6 upgrade:** `mobius_charpoly_eq_scalar_times_signed` in `L16_SpectrumUnion.lean` gives the same factorisation *directly* for $L_{\mathrm{Mob}}$ without needing $\tG$.
- **Suggest:** One-paragraph remark after Thm 7.5: "Equivalently, the Möbius connection-Laplacian charpoly itself factors: $\det(\lambda\II - L_{\mathrm{Mob}}) = \det(\lambda\II - \Lscalar)\cdot\det(\lambda\II - \Lsigned)$ (Lean: `mobius_charpoly_eq_scalar_times_signed`, `L16_SpectrumUnion.lean`)."

### B2 [HIGH]  Cor 7.6 (pointwise multiplicity) is now machine-formalised, but Appendix A marks it as only a corollary
- **Lines 1074–1080** + **line 1328** (`corollary of cover_charpoly_eq_scalar_times_mobius`).
- **R6 upgrade:** `mobius_charpoly_roots_eq_union` (M6 in `L16_SpectrumUnion.lean`) is the direct multiset-union identity; Cor 7.6 is its specialisation at a single root.
- **Suggest:** Replace the multicolumn `corollary of ...` row with `mobius_charpoly_roots_eq_union, L16_SpectrumUnion.lean`.

### B3 [HIGH]  §9 "Trace formulas" prop does NOT include new L17 trace identities
- **Lines 956–978** (Prop 9.1) states only first-order `tr(L_•) = 2|E|` or `4|E|`.
- **R6 upgrade:** L17 provides four additional identities: `trace_laplacian_mobius` (redundant with 9.1), `trace_sq_laplacian_decomposes` (S4), `frobenius_laplacian_decomposes` (S5), `trace_mul_scalar_signed_eq` (S2, polarisation form).
- **Suggest:** Add Proposition 9.2 "Quadratic trace identities":
  - $\tr(L_{\mathrm{Mob}}^2) = \tr(\Lscalar^2) + \tr(\Lsigned^2)$
  - Frobenius-norm corollary $\|L_{\mathrm{Mob}}\|_F^2 = \|\Lscalar\|_F^2 + \|\Lsigned\|_F^2$
  - Cross-term `trace_mul_scalar_signed_eq` *in polarisation form* (see D1).

### B4 [HIGH]  `shiftedDet_factorises` (S3, L17) is new and uncited
- **R6 upgrade:** $\det(L_{\mathrm{Mob}} + \alpha \II) = \det(\Lscalar + \alpha\II)\cdot\det(\Lsigned + \alpha\II)$ for any $\alpha\in\RR$.
- **Issue:** Strictly more general than Thm 7.5 (which factorises only the charpoly evaluated at $\lambda\II$); useful for PSD perturbation / regulariser readers.
- **Suggest:** Corollary immediately after Thm 7.5 citing `shiftedDet_factorises` in `L17_TracesAndLipschitz.lean`.

### B5 [MID]  Thm 7.5 multiset statement (line 1046–1048) should include direct-bundle form
- Currently only $\operatorname{Spec}(\tL) = \operatorname{Spec}(\Lscalar)\uplus\operatorname{Spec}(\Lsigned)$ via cover.
- **R6 upgrade:** Same identity holds directly for $L_{\mathrm{Mob}}$ (M6).
- **Suggest:** State both variants — they are equivalent under Thm 3.1 but paper readers who skip §4 benefit from the direct form.

---

## Category C — New-theorem citation opportunities (5)

### C1 [HIGH]  Appendix A table (lines 1291–1344) needs 7 new rows for L16/L17
- Currently table ends at L15 bridge monotonicity (line 1342).
- **Suggest:** Append rows:
  - `mobius_charpoly_eq_scalar_times_signed → L16_SpectrumUnion.lean` (paper: new Remark/Thm after 7.5)
  - `mobius_charpoly_roots_eq_union → L16_SpectrumUnion.lean` (paper: Cor 7.6)
  - `connectionLaplacian_charpoly_decomposes → L16_SpectrumUnion.lean` (unified form)
  - `shiftedDet_factorises → L17_TracesAndLipschitz.lean` (paper: new Cor under 7.5)
  - `trace_sq_laplacian_decomposes → L17_TracesAndLipschitz.lean` (paper: new Prop 9.2)
  - `frobenius_laplacian_decomposes → L17_TracesAndLipschitz.lean` (paper: new Prop 9.2)
  - `trace_mul_scalar_signed_eq → L17_TracesAndLipschitz.lean` (with polarisation-form note, see D1)

### C2 [MID]  §8 formalisation summary enumerates only §3–§6 theorems, omits §9–§10
- **Lines 860–877** list decomp / cover-splits / fiber-card / signed-kernel / connection-ker / strict / cycle-spectra, but not `cover-charpoly`, `signed-psd`, `tree-balanced`, `walk-sum`, `cycle-ew`, `cross-merge` R5 refinement.
- **Suggest:** Either extend the itemised list or add a one-liner "Further theorems of §9–§10 are tabulated in Appendix A."

### C3 [MID]  §Reproducibility (lines 1348–1369) does not mention R6 artefacts
- Lists `findings/round{3,4}/fuzzer*/`. R6 Stage-2 and Stage-6 fuzzer outputs live under `findings/round6/stage{2,6}_fuzzer_{A,B}/` and cover the new trace/spectrum identities.
- **Suggest:** Extend the path glob to `findings/round{3,4,6}/` or list explicitly.

### C4 [MID]  `thm:cover-charpoly` label is becoming a misnomer after B1
- Once direct-bundle version is stated, the label `cover-charpoly` no longer reflects strongest form.
- **Suggest:** Keep label for continuity, add a second `\label{thm:charpoly-factorises}` on the same theorem, or rename.

### C5 [LOW]  `flat_charpoly_eq_scalar_sq` (L16) deserves a passing mention
- Specialises to: flat-bundle connection-Laplacian charpoly is $p_{\Lscalar}(x)^2$. One-line corollary under Thm 5.3 (line 725) or Thm 7.5.

---

## Category D — Caveats the paper should acknowledge (2)

### D1 [LOW]  Polarisation caveat from Stage-8 ADVERSARIAL-B
- **Context:** Stage-8 flagged that `trace_mul_scalar_signed_eq` in L17 is stated in **polarisation form** `2·tr(L_sc · L_sg) = tr((L_sc+L_sg)²) − tr(L_sc²) − tr(L_sg²)` (pure algebra, true for any matrices), NOT the combinatorial form `tr(L_sc · L_sg) = tr(L_sc²) − 4|W|` that the Stage-5/6 fuzzer pinned.
- **Status in current paper:** neither form appears; the paper is *safe today*.
- **Risk for Stage 11 INTEGRATOR:** If they inline C1/B3 they MUST either (i) write the polarisation form explicitly and label it as such, or (ii) if they want the combinatorial form they should present it as "empirically verified (Stage-6 fuzzer sweep, $n\le 8$, zero violations) with a Lean bridge lemma tracked as R7 carry-over."
- **Suggest:** Pre-register this guard as a footnote in the draft expansion of Prop 9.2 to prevent accidental over-claim.

### D2 [LOW]  Memory-level record of `(⋆)` falsification is not cited
- **Lines 763–781** — the "Pre-registered plan vs correct statement" remark.
- The project memory has `signed_kernel_dim_false.md`; a parenthetical cross-ref would aid reproducibility but is cosmetic.

---

## Category E — Deprecated / overtaken prose (0)

**Empty.** Keyword grep for `future work | to be formalised | conjecture | open question | not yet | empirically` on `paper.tex` returned no matches. The paper carefully avoided pre-announcing L16/L17 content. R6 additions are **purely additive**.

---

## Ranked integrator shortlist (Stage 11)

**MUST LAND (HIGH):** B1, B3, B4, C1 (plus B2, which is a one-row table edit).
**SHOULD LAND (MID):** A2, B5, C2, C3, C4, A1.
**COSMETIC (LOW):** A3, A4, C5, D1, D2.

## Top-3 HIGH recommendations

1. **B3 + C1** — Add Proposition 9.2 "Quadratic trace identities" (tr(L²) decomposition and Frobenius-norm decomposition) and seven corresponding rows to the Appendix-A Lean-name table. This is where the L17 landing has no citation home *at all* right now.
2. **B1 + B4** — Add a one-paragraph remark + shifted-det corollary after Thm 7.5 citing `mobius_charpoly_eq_scalar_times_signed` and `shiftedDet_factorises`; gives readers the direct-bundle story without the cover detour.
3. **A2** — Reconcile the abstract's 456,950 fuzzer total with the reproducibility paragraph's 176,169 total; this is the only *internal contradiction* in the manuscript and the easiest to spot on a first read.

---

## Summary counts

| Category | HIGH | MID | LOW | Total |
|---|---:|---:|---:|---:|
| A (ambiguity/typo) | 0 | 2 | 2 | 4 |
| B (missing R6 landings) | 4 | 1 | 0 | 5 |
| C (citation opportunities) | 1 | 3 | 1 | 5 |
| D (caveats) | 0 | 0 | 2 | 2 |
| E (deprecated prose) | 0 | 0 | 0 | 0 |
| **TOTAL** | **5** | **6** | **5** | **16** |

---

## Notes

- All `\ref{}` targets resolve to declared `\label{}`s (verified by grep-matching). No dangling cross-refs.
- No figures or floating tables — the only non-inline object is the Appendix-A tabular (line 1291–1344), which has no float-placement issues.
- Sign conventions ($\Phi(e) = \sigma_x$ on wrap, $\II_2$ on non-wrap; $\Lsigned$ off-diagonal $+1$ on wrap, $-1$ on non-wrap) are stated at first use (lines 139, 252–253). No drift.
- No abandoned or overtaken prose was found — this is a clean additive-only upgrade target for INTEGRATOR.
