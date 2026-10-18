# Adjudication of the 2026-10-18 external review ("Argon 4")

Input: an AI-generated "deep review" of the manuscript, supplied by the
author on 2026-10-18 and labelled a Google Argon 4 review. Its typo list
("Non-necessality", the duplicate period in Example 11.3) identifies the
reviewed text as the **v.0.0.5 manuscript** (Zenodo version 23401896),
not `main`. Every point was checked against `main` at `561ec07` and, for
Lean claims, against the sources. As with the earlier adjudications, the
review is an input to check, not an authority.

Verdicts: **STALE** (already fixed on `main` before this review),
**CONFIRMED** (holds; fixed in this pass), **PARTIAL** (part holds; that
part fixed), **NOT ADOPTED** (with the reason).

## Summary-level statements

| Review statement | Verdict | Evidence and action |
|---|---|---|
| First `sorry`-free formalization in any interactive theorem prover of signed and ℤ/2-connection Laplacians | **NOT ADOPTED** | Not checkable across all provers. The paper now states only what was checked: Mathlib's `SimpleGraph` library at the pinned revision (`20c7314`) has `lapMatrix`, its positive semidefiniteness and the kernel–component count, and no signed or connection Laplacian and no double cover. |
| The numerical cross-check is 456,950 configurations at n ≤ 7 | **STALE** | Later rounds add the n = 8 bounded-exhaustive sweep (7,246,819 configurations), the n = 9–10 structured sweep and the round-10 cycle checks. |

## Points and fixes

| # | Review point | Verdict | Evidence and action |
|---|---|---|---|
| 1 | Situate the double-cover splitting in prior work (Gremban; Li–Hou; Bilu–Linial); cite references [3]–[6] | **PARTIAL** | Bilu–Linial was already cited on `main`. Uncited bibliography items on `main` were Chung, Mathlib and Lean 4; all three are now cited. Gremban's thesis is verified (CMU, 1996, CMU-CS-96-123); Spielman–Teng (arXiv:cs/0607105, §2.2) attribute to it the reduction of SDD systems to systems of twice the dimension, so it is cited with that pointer. The suggested Li–Hou (2019) paper could not be located in three searches and is **not cited**. Added instead, after checking it: Diaz-Diaz, Devriendt and Lambiotte (arXiv:2509.14193), whose Gremban expansion (Def. 2.1) is the orientation double cover and whose Cor. 3.8 is Theorem 4.4. |
| 2 | Abstract claim (v) and Theorems 7.1–7.2 overstate per-mode eigenvalue identities; multiplicities need linear independence | **STALE** | `CycleMultiset.lean` proves both full characteristic polynomials and root multisets with multiplicities through a Vandermonde eigenbasis (PR #11). Abstract (v) is reworded to say exactly that, and Theorems 7.1–7.2 now read "as a multiset indexed by k". |
| 3 | Theorem 10.1 says "tree" but states and proves the forest version; Lean formalises only `IsTree` | **CONFIRMED** | Theorem 10.1 now states the connected-tree case that `L11_Trees.lean` formalises; forests move to Corollary 10.2, marked as not a named Lean theorem. The proof uses path uniqueness directly (the review's simplification), and the Lean route is described. |
| 4 | Corollary 10.4 is unconditional while its Lean certificate is conditional | **PARTIAL** | Remark 10.5 on `main` already stated the hypotheses. Corollary 10.4 now points to it, and the index row is annotated "weak, conditional". |
| 5 | The Lean declaration for Theorem 11.4 keeps an unused non-wrap hypothesis | **CONFIRMED** | The binder is `_hnonwrap`, unused. New theorem `numBalancedComponents_monotone_remove_nonbridge` states Theorem 11.4 exactly and is axiom-audited. The historical declaration stays byte-identical because the archived comparator challenge replays it. |
| 6 | Lemma 5.6: ε₀ (not χ) is the witness; the deck involution is used implicitly | **CONFIRMED** | Proof rewritten: ε₀ is the witness, and the deck involution with Lemma 5.4 gives the sheet-exclusion fact (†). The old second paragraph described the Lean route incorrectly ("orbits of size 2 force an even fibre"); it now names `balanced_of_sheets_separated` and `unique_sheet_above`. |
| 7 | Remark 6.5: per-component validity vs accidental global cancellation | **CONFIRMED** | Added the exact global condition: (★) holds iff #(balanced, odd wrap) = #(unbalanced, even wrap). |
| 8 | Theorem 7.2 sketch: the gauge `v_j ↦ α^j v_j` puts the branch cut on {n−1, 0}, not {0, 1} | **CONFIRMED** | The sketch now relabels so that the wrap is the closing edge, which is the Lean convention, and checks the cancellation `α^{∓(n−1)} = −α^{±1}`. It gives the `(j−1) mod n` exponent for {0, 1}. |
| 9 | Formalisation index: Thm 11.4 labelled Ex. 11.3; "§4" for Thm 4.4; "drop = β"; missing `Basic.lean`, `CycleSpectrum.lean`, flat trace; scope notes | **CONFIRMED** | Theorem 11.4 had been typeset inside Example 11.3's environment; it is now separate. The index rows are corrected or added. The flat trace had **no Lean declaration**: `trace_laplacian_flat` (L17) now proves it and is axiom-audited. Section 9's claim that everything lives in `L9_Bounds.lean` is corrected. |
| 10 | Example 11.5 relies on simple-graph contraction | **CONFIRMED** | The convention is now stated, with the multigraph contrast (an unbalanced 2-cycle, β = 0). |
| 11 | Abstract: "(★) holds only on ℤ/2-cycles" is ambiguous | **STALE** | Already rephrased on `main`. |
| 12 | Corollary 10.4: "holds exactly for cycle graphs" reads as an if-and-only-if | **STALE** | `main` had already rephrased it, but the replacement contained a broken sentence ("non-cycle graphs. as discussed in the corrected Remark above"). That is fixed, with a cross-reference. |
| 13 | "Non-necessality"; "see Remark 7.3 below"; table overflow; inline reference overflow in Theorem 11.4's proof | **STALE** | Fixed on `main` before the review (long identifiers wrap since `9694ab0`). |
| 14 | Typography: quotes in Def. 4.1; duplicate QED in Lemma 4.2; `(−1)^i` with `i ∈ Bool`; definition of `1_e`; Remark 9.3 exponent; identity subscripts in Remark 9.7; Theorem 10.3 grammar and ε outside C; `L_scalar` and ℂ ambient spaces in Example 11.1; ".)." in Example 11.3 | **CONFIRMED** | All were still present on `main`; all fixed. |

## Verification

- Lean: `lake build` and the axiom audit pass on the branch
  (run 39146756984). The audit reports 25 / 25 requested declarations and
  only `propext`, `Classical.choice` and `Quot.sound`.
- Manuscript: rebuilt with the repository's "Rebuild paper PDF" workflow,
  with no undefined references.
- References checked against primary or first-hand sources: the CMU
  Computer Science Department record of Gremban's thesis; Spielman–Teng
  arXiv:cs/0607105 §2.2; Diaz-Diaz–Devriendt–Lambiotte arXiv:2509.14193,
  Def. 2.1 and Cor. 3.8.

No theorem statement of the historical comparator seven or of the cycle
five is changed. The new declarations are axiom-audited but not
comparator-replayed.
