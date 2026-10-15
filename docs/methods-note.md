# Treat the Generator as Untrusted: a Pipeline Epistemology for AI-Assisted Mathematics

*Methodological note on the development of this repository, 2026–10. The
mathematical content is classical signed-graph spectral theory; this note
documents how it was produced and why we believe it.*

---

## The claim

The interesting invention in this project was never "a language model wrote
some Lean." That lineage is old. The methodological contribution was an **epistemic
architecture**: treat the AI-assisted development process — subsequent conjecture proposals,
proof search, translation from informal mathematics, even the transcription
of statements — as an untrusted prover, surround it with heterogeneous,
executable critics, progressively lower every surviving claim onto a small
trusted kernel, and publish only the residue.

This note records the architecture as it actually ran, stage by stage, so
that the methodology is auditable the same way the mathematics is.

## Where it came from

The pipeline did not start as a verification project. It started as an
experimental research ecology — the NP Bunny / UTAI / Uber-UTAI sessions —
in which the human researcher originated the initial mathematical
conjectures and designed the research and adversarial apparatus. The models
were tasked with developing the conjectures, proposing subsequent
intermediate statements, exploring proofs, formalising results, and
implementing computational critics. The human researcher retained responsibility
for choosing research questions, evaluating failures, and adjudicating
mathematical claims. This division of labour is the author's account; the
repository's source history and experimental artifacts document outputs and
checks, not a complete transcript of every contribution.

Two early observations shaped everything that followed.

First, the AI-assisted development was *productive but unreliable in structured ways*. It
proposed true theorems, plausible-but-false theorems, and statements whose
meaning drifted under translation — and it could not reliably tell which
was which. Neither could any single critic. What worked was **heterogeneous
criticism**: fuzzers that enumerate, negators that try to falsify,
ambiguators that hunt meaning drift between the informal claim and its
formalization. Failures were feedstock, not embarrassments — the
pre-registered parity conjecture died at the hands of an exhaustive fuzzer
(a K₄ with a wrap matching), and its corpse became the correct cohomological
statement.

Second, **every layer of trust had to be earned downward**. "The model says
the proof works" was worth nothing. "The Lean kernel accepts it" was worth a
lot, but only once three other things were true: the build forbids `sorry`
and `native_decide` (CI-enforced, comment-aware source audit), the axiom
footprint is exactly Lean's three standard axioms (a named-allowlist audit
in CI), and the *statements* being proved are the ones the paper claims.
The later evolution of this discipline into Lambda SAT Solver — turning
parts of the exploratory reasoning into explicit computational machinery —
was the same instinct: get cognition out of the model and into checkable
artifacts.

## The three failure surfaces

A formal proof has at least four links:

    intended theorem → formal specification → Lean proof → kernel acceptance

The kernel gives very strong assurance about the last link. The CI trust
boundary strengthens it. But the most dangerous errors live earlier: **did
we formalize the right theorem?** The architecture attacked the
specification gap explicitly, and every attack left an artifact:

- **Adversarial passes against the paper itself** (round 5) caught real
  bugs in the manuscript — before any external reviewer saw it.
- **Dual transcription** (round 8): a fresh agent, denied access to the
  challenge, re-transcribed the seven end theorems from source and from the
  paper. Token-identity between transcriptions is weak evidence; the
  *discrepancies they didn't have* are the point — and the four they did
  find (a theorem proved in Lean but absent from the paper; a public Lean
  statement weaker than the paper's; two convention notes) became errata,
  not doubts.
- **External review adjudicated, not obeyed**: when an AI review of the
  paper arrived alleging a headline mathematical error, the review was
  itself treated as untrusted input. Numerics from an implementation that
  had read only the paper, the Lean sources, and the manuscript's actual
  text adjudicated each claim. The headline accusation was stale; two real
  errors were confirmed; one new internal finding (vacuous placeholder
  theorems) surfaced *because* the adjudication required reading the Lean
  file closely. The confirmed errors are published as corrections in
  v.0.0.4 (`Hardening/paper-review-adjudication.md`). Reviews are evidence,
  not authority.

## The judge and the last mile

The final layer was `comparator`, the Lean FRO's "trustworthy judge." The
point of using it was not ceremony: an unmodified binary verifies that the
seven end theorems prove *exactly* independently transcribed statements,
depend on *only* the three standard axioms, and that every constant in the
exported transitive closure — 10,324 theorems' worth — re-passes a kernel
replay. Running it demanded the same discipline it enforces: the exporter
had to be back-ported to the project's pinned Lean version (safe, because
the exporter is untrusted by design — anything it gets wrong dies in the
replay), the judge itself stayed byte-unmodified, and the run executed
under a real landlock sandbox with a second, independent kernel (nanoda)
accepting in parallel. Two deliberately broken controls — a one-token
statement tamper and a smuggled axiom — are rejected, which is what makes
the positive run mean something.

The remaining honest ledger, after all of it: the independently transcribed challenge statements and the paper's intended statements remain subject to shared interpretive assumptions; the numerical checks share an eigen-solver with
themselves; exhaustive strength stops where compute does. The evidence map
publishes that ledger next to the results, because a trust boundary you
can't see is a trust boundary you can't check.

## What transfers

Stripped of this project's particulars, the transferable shape is:

1. **Untrusted generation, trusted checking** — with the checking
   *heterogeneous* (enumeration, falsification, re-implementation,
   independent kernels) so the critics don't share blind spots.
2. **Artifacts over assurances** — every stage drops a file: a fuzzer
   result, a transcript, an export, a log. Claims cite files or they don't
   get made.
3. **The specification gap gets the most attention**, because the kernel
   cannot protect against proving the wrong theorem.
4. **Negative controls are part of the evidence** — a gate that has never
   rejected anything is untested.
5. **External input (reviews, prior art, the model itself) is adjudicated
   with the same machinery**, never simply accepted or rejected.
6. **The residual uncertainty is published**, theorem by theorem, as a
   ledger.

The deeper point: as models became good enough at generating mathematics,
the central question shifted from *"can it produce a proof?"* to *"what
exactly should we trust, and why?"* This project's answer — surround the
generator with hostile, executable checks; lower claims onto a kernel;
publish the surviving residue together with its gaps — is an answer any
research process can adopt, with or without a language model in the loop.

## Reading the receipts

Every claim above resolves to a file in this repository:

- Verified spine + CI trust boundary: `ConnectionLaplacian/`,
  `scripts/audit_trust.py`, `.github/workflows/`.
- The comparator run (sandboxed, dual-kernel, with negative controls):
  `Hardening/REPORT.md`, logs under `Hardening/`.
- Theorem-by-theorem evidence chain and current errata ledger:
  `Hardening/EVIDENCE-MAP.md`.
- The independent paper-only reimplementation and its Lean-verified
  convention battery: `findings/round8/`.
- Numerical falsification pressure: `findings/round2`–`round6`,
  `findings/round8` (7.25M n=8 configurations), `findings/round9`
  (3.31M structured-adversarial configurations at n = 9–10: every cut,
  seeded spanning trees and maximal matchings per graph — the wrap families
  where the historical counterexample lived).
- The review adjudication: `Hardening/paper-review-adjudication.md`;
  published corrections through the v.0.0.5 manuscript.

That is the invention we would defend: not any theorem, but the pile of
receipts.
