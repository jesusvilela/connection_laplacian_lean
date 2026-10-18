## v.0.0.6 — corrections and complete cycle spectra since v.0.0.5

Snapshot of `main` after the 16–18 October 2026 audit and correction
passes. v.0.0.5 (2026-10-15, version DOI 10.5281/zenodo.23401896) stays
archived unchanged; this release supersedes it under the same concept DOI,
10.5281/zenodo.19695396.

### Corrections to v.0.0.5

- **"Pre-registered" withdrawn.** v.0.0.5 called the total-wrap parity
  formula part of a "pre-registered plan" and said an exhaustive fuzzer
  refuted it. No timestamped preregistration has been identified. The first
  public commit (`3ebc07d`, 2026-04-22) already contains the false formula,
  the K₄ counterexample and the corrected balanced-component result, so the
  public record establishes neither which tool or person found the error
  first nor a causal order. The paper, the methods note and the Lean
  comments now say "initial written plan"; see
  `Hardening/audit-reconciliation-2026-10-16.md`.
- **Vacuous conjunct replaced.** In v.0.0.5, `mobius_more_eigenvalues`
  contained `∃ v, v ≠ 0 ∧ True`. It now exhibits an actual signed-cycle
  eigenvector (`mulVec v = lam_mob • v`) and proves that eigenvalue absent
  from the scalar-cycle spectrum.
- **L14 scope stated correctly.** The `L14_CycleEw` documentation now says
  that the converse direction needs the caller-supplied hypothesis `hrev`
  and that the file does not construct a cycle graph. Theorem statements
  are unchanged.
- **K₄ examples reconciled.** The Lean comment's adjacent-wrap example
  {a–b, a–c} and the paper's matching {12, 34} are different signings;
  both have two wraps, an unbalanced triangle and signed nullity 0
  (exact rational checks in `findings/round10/test_k4_counterexamples.py`).
- **Comparator provenance.** The historical seven-theorem comparator run
  used the existing `Hardening/Challenge.lean`. A fresh-agent
  transcription cross-checked that file but was not the comparator's input.
- **Release metadata.** The GitHub release notes of v.0.0.4 and v.0.0.5
  came from a stale v.0.0.3 template, and their attached PDF was rebuilt at
  release time rather than being the committed manuscript. Release notes
  now come from `.github/release-notes/`, the release workflow checks that
  `CITATION.cff` carries the tag, and the attached PDF is the committed
  `paper/paper.pdf`.

### Review of the v.0.0.5 manuscript (2026-10-18)

An external AI review of the v.0.0.5 manuscript was adjudicated point by
point in `Hardening/argon4-review-adjudication-2026-10-18.md`. Resulting
changes:

- Two new Lean theorems, both axiom-audited:
  - `numBalancedComponents_monotone_remove_nonbridge` states the
    bridge-deletion theorem without the unused non-wrap hypothesis. The
    historical declaration that the comparator replayed is unchanged.
  - `trace_laplacian_flat` proves `tr(L_flat) = 4|E|`, which the paper had
    listed as formalised although no Lean declaration existed.
- Theorem 10.1 now states the connected-tree case that Lean formalises.
  Forests move to Corollary 10.2, marked as not formalised.
- Lemma 5.6's proof is rewritten with the deck involution made explicit.
- Remark 6.5 gives the exact global cancellation condition for (★).
- The Theorem 7.2 sketch places the gauge branch cut correctly.
- Theorem 11.4 is no longer typeset inside Example 11.3.
- The formalisation index is corrected and completed.
- Prior work now cites the Gremban expansion (Diaz-Diaz–Devriendt–Lambiotte,
  arXiv:2509.14193) and Gremban's doubling reduction. A suggested Li–Hou
  reference could not be located and is not cited.
- Typographical fixes.

### New Lean results

- `CycleMultiset.lean`: complete real characteristic polynomials and exact
  root multisets, with multiplicities, of the scalar and one-wrap signed
  cycle Laplacians for `n ≥ 3` (`Cycle.scalarCycle_charpoly_real`,
  `Cycle.signedCycle_charpoly_real`, `Cycle.scalarCycle_roots_real`,
  `Cycle.signedCycle_roots_real`).
- `CycleGraphTransfer.lean`: five statements transferring those spectra to a
  `ConnGraph`, conditional on a supplied vertex bijection and both
  matrix-reindexing identities.
- `L10_CoverCharpoly.lean`: `cover_charpoly_roots_eq_union` and
  `cover_charpoly_root_count_eq_sum`.

### Verification

- Cycle comparator run 38863604693 (2026-10-16): five statements; the Lean
  and nanoda kernels both accept; the phase-tamper and smuggled-axiom
  controls are rejected. Logs and the exact tested commit are archived in
  `Hardening/runs/38863604693/`.
- `AxiomAudit.lean` selects 25 declarations, two of them added on
  2026-10-18, and the audit fails if any requested declaration is missing
  from the `#print axioms` output.
- Round 10: cycle Fourier bases and eigenvalue multisets for
  `n = 3, …, 64` with a wrong-basis control; exact-integer cycle/`ConnGraph`
  matrix identities with wrong-seam controls; exact K₄ checks.
- CI additionally runs the comparator-harness and archived-evidence audits,
  the exact K₄ and matrix-reindex probes, and elaborates the cycle
  comparator challenge, solution and negative controls.

### Still open

- Constructing both cycle-to-`ConnGraph` matrix identifications from a
  cycle-graph hypothesis.
- L14's reverse parity implication without the caller-supplied `hrev`.
- The combinatorial mixed-trace identity `tr(L_sc L_sg) = tr(L_sc²) − 4|W|`.
