# ADVERSARIAL-PAPER R6 Stage 10 — paper vs Lean red-team

**Date:** 2026-04-22
**Auditor:** ADVERSARIAL-PAPER
**Scope:** `paper/paper.tex` (1416 lines) vs `ConnectionLaplacian/*.lean` through L17.

**Totals:** 16 findings — 3 CRITICAL, 5 HIGH, 5 MID, 3 LOW.

---

## CRITICAL

### C-1 — Theorems 6.1 / 6.2 cycle-spectrum Lean certificates are trivial stubs
- Paper lines **798–830** (Thm `thm:flat-cycle`, Thm `thm:mobius-cycle`) claim explicit spectra `{2 − 2cos(2πk/n)}` and `{2 − 2cos((2k+1)π/n)}`; Appendix A lines **874–876** pair these with Lean names `flat_cycle_spectrum` and `mobius_cycle_spectrum`.
- Lean (`CycleSpectrum.lean` L659, L679): both names are proved by `⟨(1:ℕ), one_ne_zero, trivial⟩` — i.e. the Lean statement is `∃ v, v ≠ 0 ∧ True`, a vacuous existence. No spectrum, no eigenvalue equation.
- The actual per-eigenvalue certificates are `scalarCycle_eigenvalue` (L265) and `signedCycle_eigenvalue` (L557) — these are real, but Appendix A points at the wrong names.
- **Fix:** swap the Appendix-A citations to `scalarCycle_eigenvalue` / `signedCycle_eigenvalue`, and reword §6 to note that the full-spectrum-as-multiset is *assembled from* the per-k eigenvalue theorem (or land a real `...spectrum_eq` theorem).

### C-2 — §3 proof of Thm 3.1 describes a unified Hadamard proof; Lean's flat branch uses P = I
- Paper lines **305–335** set `P = I_V ⊗ R̂` for *both* ε-modes, then calls flat "the special case W=∅ of the Möbius case".
- Lean (`KernelDimension.lean` L345–364, `laplacian_decomposes`): flat case is proved with `P = 1` (identity), Möbius with the Hadamard. These are two disjoint proofs, not a specialisation.
- **Fix:** add a one-sentence remark after the proof of Thm 3.1 flagging the Lean structure (flat uses P=I; Möbius uses the Hadamard).

### C-3 — Reproducibility paragraph is stale (R4-era numbers and paths)
- Paper lines **1355–1369** still cite `176{,}169` configurations and paths `findings/round{3,4}/fuzzer*/`.
- Abstract (lines **121–124**) already reflects R5's $456{,}950$-config sweep at $n\le 7$.
- R6 Stage-6 fuzzer-B additions are not disclosed at all.
- **Fix:** rewrite the §Reproducibility paragraph to cite current total, R5 `round5/` fuzzer-B, R6 `round6/stage6_fuzzer_B/`, and the exact identities fuzzed.

---

## HIGH

### H-1 — Prop 9.2 trace formulas: flat-Möbius row is not in Appendix A
- Paper **956–964** lists four trace equalities including `tr(L_flat) = 4|E|`. Appendix A (**1313–1316**) has rows only for `trace_scalarLaplacian` and `trace_signedLaplacianMobius`. The R6-landed `trace_laplacian_mobius` (L17 L79) is omitted. A flat-L analogue is not separately named in Lean.
- **Fix:** add an Appendix-A row pairing Prop 9.2 (Möbius/flat) with `trace_laplacian_mobius`; clarify the flat case by identity of diagonals.

### H-2 — Cor 10.2 (forest) is stronger than the Lean certificate
- Paper **1138–1143**: "If the underlying graph is a forest ... $\dim\Ker L_{\mathrm{Mob}} = 2\,\#\comp(G)$ for every W."
- Lean (`L11_Trees.lean`): the keyed predicate is `SimpleGraph.IsTree`, which is *connected* acyclic (`numComponents = 1`). There is no forest/`IsAcyclic` lemma in the repo; Appendix A row 1335–1336 labels Cor 10.2 a "specialisation of the tree ker-dim theorem", but disconnected forests are not covered.
- **Fix:** either weaken Cor 10.2 to connected trees, or add a small Lean lemma lifting `tree_isBalanced_of_isTree` over components via `isBalanced` per-component.

### H-3 — Cor 10.4 (cycle even-wrap) is unconditional in the paper, weak in Lean
- Paper **1165–1177** states `β(C_n) = 1 ↔ #W even` on cycles $n\ge 3$ without further hypothesis; Appendix A cites `cycle_isBalanced_iff_even_wrap_weak`.
- Lean (`L14_CycleEw.lean` L138): explicitly **weak** — requires the caller to supply (i) an Eulerian closed walk and (ii) a hypothesis `hrev` encoding the reverse direction. Comment block L149–170 defers `fundamentalCycleWalk` + winding-number to a future stratum.
- **Fix:** mention in a remark that the reverse direction is informal in the paper and an open formalisation TODO; or land `fundamentalCycleWalk` before the paper commits.

### H-4 — §2.3 misdescribes the PSD proof route
- Paper **258–268** says PSD of $\Lsigned$ "follows from the cover splitting (Thm 4.1)".
- Lean (`L13_PSD.lean` L299, `signedLaplacianMobius_posSemidef`) is proved by sum-of-squares (`sLM_quadForm_nonneg`, L198) — the paper's *second* argument (1010–1034).
- **Fix:** in §2.3 lead with the sum-of-squares proof, mention cover-splitting as an alternative.

### H-5 — Appendix A has no rows for L16/L17 theorems
- Missing: `mobius_charpoly_eq_scalar_times_signed`, `mobius_charpoly_roots_eq_union`, `shiftedDet_factorises`, `trace_laplacian_mobius`, `trace_sq_laplacian_decomposes`, `frobenius_laplacian_decomposes`, `trace_mul_scalar_signed_eq`.
- These are all R6 landings; the formalisation index should expose them.
- **Fix:** extend the table, and (optionally) add §9 paragraphs naming these identities.

---

## MID

- **M-1** (preventive): `trace_mul_scalar_signed_eq` in Lean is **polarisation-form only**. If a future paper revision adds a combinatorial C10 `tr(L_s·L_sig) = Σdeg² + 2|E| − 4|W|`, it must be flagged as fuzzer-checked, not Lean-certified.
- **M-2** (lines 673, 1305): Paper refers to `componentProj_fiber_card` as a "theorem" (Thm 5.2) but Lean declares it a `lemma` at L6_Cohomology.lean L344.
- **M-3** (line 703): Mathlib's `card_ConnectedComponent_eq_rank_ker_lapMatrix` is used via `.symm` in the Lean code (KernelDimension L480); paper wording "applied" is loose.
- **M-4** (line 323): The display `(1/2)(P L P)[(u,i),(v,j)] = …` is correct (because $P^{-1}=\tfrac12 P$) but the factor-of-2 goes unexplained until line 330; add a parenthetical connecting the $\tfrac12$ to $P^{-1}$.
- **M-5**: The abstract (121–124) and Reproducibility paragraph (1355–1369) disagree on fuzzer counts — duplicate of C-3, flagged separately.

## LOW

- **L-1** (line 1202): Example 11.3 cites internal telemetry `C2, τ=0.0000`; define or remove.
- **L-2** (line 1328): `\multicolumn{2}{l}{...}` on Cor 9.5 is fine typographically; consider naming a Lean declaration to populate the row.
- **L-3** (line 1346): Footnote "KernelDim.lean abbreviates KernelDimension.lean" — use the real filename throughout.

---

## Top-3 blockers (fix before R6 paper-update commit)

1. **C-1** — cycle-spectrum certificates: re-point Appendix A to `scalarCycle_eigenvalue`/`signedCycle_eigenvalue` (or land a real multiset-spectrum theorem), and soften §6 proof wording accordingly. This is a material overclaim; Thm 6.1/6.2 as stated are *not* Lean-proved.
2. **C-2** — flat-mode P mismatch: add a remark after Thm 3.1 noting Lean's flat branch uses $P=I$; or fold the two branches in Lean into one Hadamard proof.
3. **C-3** — rewrite the §Reproducibility paragraph to current R5/R6 counts and paths.

Top-3 blockers block the "paper matches formalisation" contract that the Appendix A table explicitly promises.
