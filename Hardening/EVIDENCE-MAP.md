# Evidence Map — ℤ/2 Connection-Laplacian kernel-dimension theory

**Date:** 2026-10-13, hardened 2026-10-14, gap-closure round 2026-10-15.
**Scope:** the seven representative end theorems of the verified Lean spine
(the same list audited by `ConnectionLaplacian/AxiomAudit.lean` in CI), plus
the core kernel-dimension statements that feed them.

Each row follows the chain

> claim → Lean theorem → axiom audit → numerical/exhaustive check →
> comparator result → remaining epistemic gap

## Legend

- **Lean** — machine-checked by the Lean 4.11.0 kernel at build time
  (`lake build`, CI-enforced, `sorry`-free by `scripts/audit_trust.py`).
- **Axiom audit** — `#print axioms` (CI) and, stronger, comparator's
  transitive `checkAxioms` walk over the exported proof terms.
- **Comparator** — `leanprover/comparator` @ master `e3dcf30` (v4.35.0):
  statement-equality against an independently transcribed challenge,
  axiom hygiene, and full kernel replay of the exported transitive closure,
  run under a real landlock sandbox with Lean + nanoda dual kernels
  (see `Hardening/REPORT.md`).
- **Numerical** — the Python cross-checks under `findings/` (empirical,
  not theorems).

## Theorem-by-theorem map

| # | Claim (informal) | Lean theorem | Axiom audit | Numerical / exhaustive evidence | Comparator | Remaining gap |
|---|------------------|--------------|-------------|--------------------------------|------------|---------------|
| 1 | charpoly of the orientation double cover's scalar Laplacian factors as (base scalar charpoly) · (signed Möbius charpoly) | `ConnGraph.cover_charpoly_eq_scalar_times_mobius` (L10) | ✓ standard 3 only | round2 T1/T2 (all 51 graphs n≤5, all wraps, 3456 configs: cover spectrum = scalar ∪ signed); round3 n≤6 multiset spectrum equality; round6 S1 det-product identities at n=7 (300 graphs × all wraps); round8 n=8 sweep (all connected e≤12 × all wraps, independent impl) | ✓ PASS (statement match + kernel replay) | Cover/similarity witness is *existence*; paper's constructive version not separately formalized |
| 2 | a component is balanced iff every closed walk in it crosses an even number of wrap edges | `ConnGraph.isBalanced_iff_closedWalk_wrap_even` (L12) | ✓ standard 3 only | round2 T3 (n≤5, all wraps); round8 n=8 sweep: fibre-by-both-routes checked on 7.25M configs incl. all graphs e≤7 | ✓ PASS | Exhaustive balance-vs-walk-parity checked only indirectly (via fibre cardinality), not walk-by-walk |
| 3 | the signed Möbius Laplacian is positive semidefinite | `ConnGraph.signedLaplacianMobius_posSemidef` (L13) | ✓ standard 3 only | round5 PROVER-SIGNED-PSD landing report; implicit in every spectrum check (negative eigenvalues would have failed T1/round3 multiset equality at n≤6) | ✓ PASS | PSD evidenced numerically only through spectrum equality, no dedicated eig-value ≥ 0 sweep |
| 4 | deleting a non-bridge (non-wrap) edge cannot decrease the number of balanced components | `ConnGraph.numBalancedComponents_monotone_remove_nonwrap_nonbridge` (L15) | ✓ standard 3 only | round5 PROVER-C1-NONBRIDGE n≤5 sanity (all graphs, all wraps, all deletions); hypothesis was *discovered* by R4 fuzzy-negator τ=0.89 failures (all bridges) | ✓ PASS | Lean keeps the (unused) `_hnonwrap` hypothesis to match the scoreboard wording — a cleaner `′` variant exists; no n≥6 exhaustive deletion sweep |
| 5 | charpoly-roots (multiset) of the Möbius connection Laplacian = scalar roots ⊎ signed roots | `ConnGraph.mobius_charpoly_roots_eq_union` (L16) | ✓ standard 3 only | round2 T1; round3 n≤6 **as multisets** (multiplicity-sensitive, not set equality); round6 S1_a* shifted-det identities n=7; round8 n=8 sweep | ✓ PASS | Multiset identity formalized (stronger than set equality); numerical side relies on same numpy eigen machinery for both sides |
| 6 | Frobenius norm² of the connection Laplacian splits as scalar part + signed part | `ConnGraph.frobenius_laplacian_decomposes` (L17) | ✓ standard 3 only | round6 S4-class trace identities at n=7 (300 graphs × all wraps, rel diff ≤ 1e-14) | ✓ PASS | Numerical check shares trace-convention assumptions with the formalization |
| 7 | polarisation: 2·tr(L_s·L_sig) = tr((L_s+L_sig)²) − tr(L_s²) − tr(L_sig²) | `ConnGraph.trace_mul_scalar_signed_eq` (L17) | ✓ standard 3 only | round6 S2-class mixed-trace identities at n=7 | ✓ PASS | Same shared-machinery caveat |

Core statements that feed the spine (not in the comparator seven, audited by
CI only):

| Claim | Lean theorem | Numerical evidence |
|---|---|---|
| dim ker L̃ = dim ker L_scalar + dim ker L_signed | `scalarLap_cover_kernel_dim` (L5) | round2 T2: 0/3456 failures, SVD kernel dims |
| per base component, cover fibre has 2 sheets iff balanced, else 1 | fibre-cardinality theorem (L6) | round2 T3: 0/3456 failures, incl. disconnected and isolated-vertex cases |

## Hostility checklist (specification-gap classes)

| Error class | Status |
|---|---|
| Altered quantifier domains | Challenge transcription is statement-compared by comparator (control 1 shows a one-token drift is caught) |
| Hidden finiteness assumptions | `ConnGraph` carries a `Fintype V`/`DecidableEq V` bundle in `Basic.lean`; finiteness is explicit in the definition, not hidden in the theorem |
| Graph-simplicity assumptions leaking | Simple-graph assumption is definitional (`SimpleGraph`), hence visible in every statement via `G.graph` |
| Connected vs disconnected cases | round2 spot-checks include `K_3 ⊔ {v}` and isolated vertices; Lean proofs are component-wise |
| Empty/singleton graph edge cases | n=2..5 exhaustive + round8 n=8 band B (all graphs e≤7 includes the empty graph on 8 vertices, all wraps = single config); n=0,1 not separately evidenced |
| ℤ/2 sign conventions | Wrap predicate is a fixed `E → Bool` in `ConnGraph`; both wrap parities exhaustively swept in every round |
| Multiplicity vs set equality of spectra | Formal statement is **multiset** equality; round3 checked multiset equality numerically |
| Kernel dimension vs nullity over intended field | Statements are `finrank ℂ`-free: dimension statements are over the base field fixed in `KernelDimension.lean`; round2 T2 counts SVD kernel dims consistently |
| Accidental strengthening/weakening in translation | Comparator challenge/solution equality + negative control 1 attack exactly this |
| True-for-wrong-reason proofs | Kernel replay guarantees *some* valid proof exists; mathematical *reason* is not certified (see gaps column) |
| Test generators sharing formalization assumptions | Largely closed (round 8): the sweep and battery run on an implementation written from the paper only, and Lean verifies its matrices against the formalization's definitions on 74 instances; residual: same numpy eigen-machinery for both sides of each spectral identity within one config |

## The three-layer confidence structure

1. **Kernel correctness** — Lean 4.11.0 kernel accepted the spine; CI forbids
   `sorry`/`native_decide`/project axioms (`scripts/audit_trust.py`).
2. **Semantic correspondence** — comparator (Lean FRO, unmodified binary)
   verified: the spine's seven end theorems prove *exactly* the
   independently transcribed challenge statements, depend on *only*
   `propext, Quot.sound, Classical.choice`, and every constant of the
   exported transitive closure (1,320,201 NDJSON lines: 10,324 theorems,
   4,363 definitions, 469 inductives, 3 axioms, 4 quot, 16 opaques)
   re-passes the Lean kernel in comparator's replay. The authoritative run
   (2026-10-14, WSL2) executed under a real landlock sandbox (landrun) and
   **both** kernels accepted — Lean's own kernel replay and the independent
   nanoda external kernel (16,163 declarations, zero typechecker errors).
3. **Empirical falsification pressure** — `findings/round2–6`: exhaustive
   n≤5 (and n≤6 for spectra) enumeration over *all* graphs × *all* wraps,
   adversarial negators, n=7 randomized gap-checks; round 8: n=8
   bounded-exhaustive sweep (**7,246,819 configurations, zero failures**)
   computed entirely by an independent paper-only implementation, plus a
   Lean-verified convention-anchoring battery tying the formalization's
   matrices to that implementation on 74 concrete instances; and round 9:
   3,314,688 structured-adversarial configurations at n = 9–10 (every cut,
   seeded spanning trees and maximal matchings — the wrap families where
   the historical K₄ counterexample lived), zero failures.

None of the three layers alone establishes that the published mathematics is
perfect. Together they make accidental error much harder.

## Remaining epistemic gaps (honest ledger, post round 8)

Resolved on 2026-10-14: comparator replay under a real landlock sandbox
(landrun, WSL2) with the nanoda external kernel accepting alongside the Lean
kernel replay. The Windows `fake-landrun` pass remains a development path.

Resolved on 2026-10-15 (round 8, see `findings/round8/report.md`):

- **One-author transcription** — closed by dual transcription: a fresh agent
  re-transcribed all seven statements from source without seeing the
  challenge; after expanding the section variable they are token-identical,
  and the paper-pairing audit produced the four concrete findings below
  instead of vague doubt.
- **Shared convention stack** — closed at the definitional level: an
  implementation written from `paper.tex` only (selftested, 8,887 checks) now
  supplies the literal matrices that Lean itself verifies against the
  formalization's definitions (`Hardening/ConventionAnchor.lean` +
  `Hardening/ConventionBattery.lean`, 74 instances × 2 matrices).
- **n≥8 not tested at exhaustive strength** — closed bounded-exhaustively:
  all connected unlabeled n=8 graphs with 7–12 edges × *all* wraps, all n=8
  graphs with ≤7 edges × all wraps, plus dense random sampling — 7,246,819
  configurations, zero failures, all computed by the independent
  implementation.

Still open (paper↔formal boundary, from the round-8 transcription audit):

1. **T4 bridge-monotonicity is not stated in the paper body** — *resolved
   2026-10-16: the errata published on main add Theorem `thm:bridge-monotone`
   with a proof sketch crediting the Lean proof.*
2. **T3 public Lean statement was weaker than the paper's** — *resolved
   2026-10-16: `signedLaplacianMobius_quadForm_eq` (the full sum-of-squares
   identity, previously proven internally and discarded for the weaker
   `0 ≤`) is now the public statement; `signedWeight` de-privatised so the
   statement is user-writable. Axiom-clean (standard three only).*
3. **T5 roots live in ℝ (Lean) vs Spec over ℂ (paper)** — equivalent here by
   real symmetry; a convention note, not an error.
4. **T1's "Equivalently Spec ⊎ Spec" clause and Cor 5.7** have no separately
   named cover theorem in Lean (appendix lists them as unnamed).
5. **The paper's eq. (1) Kronecker formula was internally inconsistent**
   (vertex-major `D⊗I₂` vs fibre-major `Φ(e)⊗1_e`) — *resolved 2026-10-16:
   the errata reorder the second factor to `1_e ⊗ Φ(e)` with an ordering
   note.*
6. Battery anchor instances are n≤5 (conventions are instance-independent,
   but Lean-side anchoring at scale is compile-cost-bound); sweep all-wrap
   coverage stops at e≤12 with dense sampling above (K8's 2^28 wrap subsets
   are infeasible to enumerate).

Additional items from the 2026-10-15 external-review adjudication
(`Hardening/paper-review-adjudication.md`; every claim checked against the
current text, the independent implementation's numerics, and the Lean
sources):

7. **Remark 6.5 contained two confirmed errors** (H¹ threshold off by one;
   bridge-in-W breaks (★), verified numerically on P₄) — *resolved
   2026-10-16, then corrected again the same day after author review: the
   first erratum's "precise scope" (at-most-unicyclic + no wrapped bridges)
   overclaimed necessity — K₄ with W=∅ (dim H¹=3) and P₃ with both edges
   wrapped both satisfy (★). Final text: (★) is correct on a component iff
   balanced ⟺ even wrap count; dim H¹ ≤ 1 with an even number of wrapped
   bridges is sufficient, not necessary (K₄ with a wrapped triangle holds);
   both failure forms exhibited. All six examples verified numerically via
   findings/round8.*
8. **`CycleSpectrum.lean` had two vacuous public "spectrum" theorems**
   (`flat_cycle_spectrum`, `mobius_cycle_spectrum`) whose statements mention
   no Laplacian and hold trivially; the real content is the public per-k
   `scalarCycle_eigenvalue` / `signedCycle_eigenvalue` (both `3 ≤ n`), and
   the paper says exactly that. **Resolved:** the vacuous pair was removed in
   commit `0b67037`. An additional eigenvalue-separation declaration was
   subsequently strengthened to require an actual eigenpair (see audit PR).
9. **The manuscript lacked a code URL/DOI**; Section 8's dependency graph
   predates L9–L17; swarm shorthand (C1/C2/τ/R5) was undefined — *resolved
   2026-10-16 by the errata (DOI + URL added, spine list updated, shorthand
   defined at first use).*
10. The reviews' headline accusation — that the cycle corollary claims
   "kernel drops iff n odd" — is **stale**: the current text states the
   correct universal version, confirmed by numerics (ker L^sg(C_n, {01}) = 0
   for all n = 3..14; ker = 1 iff n even exactly for W = E(C_n)) and by the
   Lean `3 ≤ n` eigenvalue theorems.

## Methodological lineage note

The author reports originating the initial conjectures and designing the
adversarial research apparatus, then directing LLMs to develop proofs,
formalizations, numerical counterexample searches, and subsequent candidate
claims. This is a claim about intellectual provenance, distinct from
machine verification of the resulting statements.



The verification pipeline recorded here was not produced by treating a
language model as an authority. The originating research architecture
(NP Bunny / UTAI / Uber-UTAI sessions → conjecture generation → adversarial
and ambiguator passes → Lean formalization → CI trust boundary → fuzzers and
negators → comparator) treated the *entire generative process as untrusted*
and published only the residue that survived heterogeneous, executable
attack. That architecture — not any single proof — is the project's
methodological contribution; the same discipline later crystallized into the
Lambda SAT Solver line of work.
