# Connection Laplacian (Lean 4 Formalization)

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.19695396-blue.svg)](https://doi.org/10.5281/zenodo.19695396)
[![Code License: Apache-2.0](https://img.shields.io/badge/code-Apache--2.0-blue.svg)](LICENSE)
[![Paper License: CC BY 4.0](https://img.shields.io/badge/paper-CC--BY--4.0-green.svg)](LICENSE-paper)
[![Lean 4](https://img.shields.io/badge/Lean-4.11.0-orange.svg)](lean-toolchain)

**What happens to a signal when you carry it around a loop?** It might
return unchanged. It might switch sheets. And, on a larger bundle, two
different loops might not even agree about how to carry it home.

This began with a finite graph, a handful of *wrap* edges and a ℤ/2
connection. Rather than trusting the picture, I wanted to know which parts
could be made precise — and which would survive an actual proof checker.
The submitted formalization establishes exact kernel and spectral identities
for that deliberately restricted model: scalar/signed decomposition,
orientation double cover, balanced components and their relation to the
connection Laplacian.

The natural question is what survives when the fibers and their transports
become richer. That is the **experimental `dev` programme**, separate from
the paper and its verified import spine. We keep the geometric question
alive; we don't pretend that a scalar cycle settles it.

Everything on the verified spine is machine-checked from the three standard
Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) and nothing else.
Around the spine sits an explicit verification apparatus — a comparator pass
under a real sandbox, an independent reimplementation of the paper's
definitions, and exhaustive numerical sweeps — documented theorem by theorem
in [`Hardening/EVIDENCE-MAP.md`](Hardening/EVIDENCE-MAP.md).

The accompanying paper lives under `paper/`. The author has submitted it to
HAL and is pursuing an arXiv route; **submission is not acceptance or
independent peer review**. The earlier FLoC-facing manuscript history is
preserved in the repository.

> **DOI:** <https://doi.org/10.5281/zenodo.19695396> (concept DOI). It
> resolves to the latest archived release; each archived release is a
> snapshot of this repository at its tag. v.0.0.5 (2026-10-15, version DOI
> [10.5281/zenodo.23401896](https://doi.org/10.5281/zenodo.23401896))
> predates the complete cycle-spectrum proofs and the corrections made
> after 15 October; [`.github/release-notes/`](.github/release-notes/)
> lists what each later release adds.

## What is where

| Layer | Contents | Epistemic status |
|---|---|---|
| Verified spine | everything imported by `ConnectionLaplacian.lean` | machine-checked Lean proofs, CI-enforced trust boundary |
| Hardening harness | `Hardening/` | comparator challenge/solution modules, convention-anchor battery, run logs, evidence map, review adjudication |
| Numerical cross-checks | `findings/` (rounds 2–6, 8–10; see methods note for omitted round 7) | Python; empirical evidence for the formal statements, not theorems |
| Paper + guides | `paper/`, `docs/` | manuscript (LaTeX + PDF) and reader companions |
| Experimental bundle research (`dev`) | `ConnectionLaplacian/Experimental/`, `research/covariant_observability/` | separately compiled Lean bridge lemmas, exact finite analysis, reproducible numerical tests, open geometric limits |

**On `main`**, the scope remains the ℤ/2 connection-Laplacian theory,
its verification harness, and the submitted paper. **On `dev`**, a clearly
separated research track investigates covariant incidence and richer
fiber-valued observability. The two should not be conflated.

## Beyond the first two fibers: the `dev` research track

I am not trying to make the original ℤ/2 theorem say something it doesn't.
Its edge matrices are `I₂` and the sheet swap `σx`; they **commute**. That
makes scalar-channel decomposition legitimate *there*, not a universal
description of connections.

On `dev` we test more demanding transports, including complex rank-two
`SU(2)` connections on graphs with independent cycles. The useful surprise
is not simply "noncommutativity produces a signal": it doesn't, in general.
On a wedge of two triangles, noncommuting holonomy can leave the Laplacian
spectrum unchanged. On a theta graph, a mixed closed-walk character becomes
visible. A commuting-only control can also change that theta spectrum. The
distinguishing object is **what the chosen operator and geometry can observe**.

Uniformly subdividing the theta graph gives a particularly clean problem:
fixed-degree spectral moments lose the mixed-cycle signal at sufficiently
large subdivisions, while a suitably rescaled heat observer retains it.
The explicit secular determinant, a spectral-tail bound, and a conventional
mathematical proof identify a **specific metric-graph heat-trace limit**.
This is **not a Lean theorem** and does not establish arbitrary hyperbolic
limits, hypercomplex advantages, or a complexity-theoretic result.

The latest experiment pushes past even that complex rank-two setting.
[GeneralFiberGauge.lean](ConnectionLaplacian/Experimental/GeneralFiberGauge.lean)
and [ArbitraryFiberIncidence.lean](ConnectionLaplacian/Experimental/ArbitraryFiberIncidence.lean)
allow **arbitrary finite fiber rank** and ordered, potentially noncommuting
matrix transports. We are assembling a genuinely fiber-valued incidence
operator, not rewriting another scalar cycle in grander notation.

There is a separate, more delicate branch of the geometry:
[IndefiniteFiber.lean](ConnectionLaplacian/Experimental/IndefiniteFiber.lean)
uses a split-signature **(2,2)** fiber form, `Q = diag(+1,+1,-1,-1)`.
The intended preservation law is `Uᵀ Q U = Q`, including ordered compositions.
Its [numerical controls](research/covariant_observability/test_split22.py)
compare noncommuting boosts with a commuting null and deliberately corrupt
form preservation. **No positive energy or Riesz estimate transfers into
this indefinite regime without a new theorem.** These newly added Lean
modules need their separate compilation and axiom gate; the verified count
below refers only to declarations already accepted by CI.

At the same time, the experimental Lean files connect the original
fiber-valued edge Gram blocks to the actual graph Laplacian. The `dev` CI
has checked **12 experimental declarations** against the standard Lean
axiom allowlist, independently of the original verified import spine.
The full graph-wide covariant incidence factorization remains a named
formalization target. We are not going to conceal that gap behind notation.

**Reconstruct the work:** [covariant-observability research map](research/covariant_observability/README.md)
· [metric-graph calculation](research/covariant_observability/METRIC_GRAPH_LIMIT.md)
· [heat-trace theorem and proof boundary](research/covariant_observability/HEAT_TRACE_THEOREM.md)
· [noncommuting and commuting controls](research/covariant_observability/POLYHOLONOMY.md)
· [experimental Lean modules](ConnectionLaplacian/Experimental/)
· [latest tested dev workflow](.github/workflows/dev-covariant-observability.yml).

**Research contract.** `P-Lean` means the *stated* Lean proposition was
compiled and its axioms audited; `P-math` means an explicit conventional
argument needing independent review; `M` is bounded reproducible
measurement; `H` is the open question; `R` records a superseded
interpretation. We keep the mistakes, not only the pretty plots.

## Verified development (import spine)

`ConnectionLaplacian.lean` imports exactly the spine below; every file is
maintained `sorry`-free and free of user-introduced axioms.

- `ConnectionLaplacian/Basic.lean`
- `ConnectionLaplacian/KernelDimension.lean`
- `ConnectionLaplacian/CycleSpectrum.lean`
- `ConnectionLaplacian/CycleMultiset.lean` *(complete scalar and signed cycle spectra)*
- `ConnectionLaplacian/CycleGraphTransfer.lean` *(conditional full connection-spectrum transfer)*
- `ConnectionLaplacian/L5_Cover.lean`
- `ConnectionLaplacian/L6_Cohomology.lean`
- `ConnectionLaplacian/L8_Recognition.lean`
- `ConnectionLaplacian/L9_Bounds.lean`
- `ConnectionLaplacian/L10_CoverCharpoly.lean`
- `ConnectionLaplacian/L11_Trees.lean`
- `ConnectionLaplacian/L12_WalkH1.lean`
- `ConnectionLaplacian/L13_PSD.lean`
- `ConnectionLaplacian/L14_CycleEw.lean`
- `ConnectionLaplacian/L15_BridgeMonotone.lean`
- `ConnectionLaplacian/L16_SpectrumUnion.lean`
- `ConnectionLaplacian/L17_TracesAndLipschitz.lean`

Representative end theorems (plain-language gloss in parentheses):

- `cover_charpoly_eq_scalar_times_mobius` *(the cover's characteristic
  polynomial factors as scalar × signed)*
- `isBalanced_iff_closedWalk_wrap_even` *(balanced ⟺ every closed walk
  crosses an even number of wrap edges)*
- `signedLaplacianMobius_posSemidef` *(the signed Laplacian is PSD)*
- `numBalancedComponents_monotone_remove_nonbridge` *(deleting a
  non-bridge edge cannot destroy balanced components; the historical
  `numBalancedComponents_monotone_remove_nonwrap_nonbridge`, replayed by
  the comparator, carries an extra unused non-wrap hypothesis)*
- `mobius_charpoly_roots_eq_union` *(the Möbius spectrum is the scalar ⊎
  signed multisets)*
- `frobenius_laplacian_decomposes` *(‖L‖²_F splits as scalar + signed parts)*
- `trace_mul_scalar_signed_eq` *(the polarisation identity for the mixed
  trace)*
- `Cycle.scalarCycle_charpoly_real` and `Cycle.signedCycle_charpoly_real`
  *(complete cosine characteristic-polynomial products for n ≥ 3)*
- `Cycle.scalarCycle_roots_real` and `Cycle.signedCycle_roots_real`
  *(exact root multisets, preserving every eigenvalue multiplicity)*

These cycle results concern the **specialised** scalar and one-wrap signed
matrices defined in `CycleSpectrum.lean`. Five new theorems transfer their
characteristic polynomials and exact root multisets to a `ConnGraph`
**conditional on a supplied vertex bijection and both matrix-reindexing
identities**. Constructing those identifications from an abstract cycle-graph
hypothesis remains separate, unproved work.
See [`docs/cycle-spectrum-multiset-assembly.md`](docs/cycle-spectrum-multiset-assembly.md).

## Human–AI division of labour

The author originated the initial mathematical conjectures and designed the
research apparatus. AI systems were directed to develop those conjectures,
construct formalizations, and implement adversarial tests. The resulting
claims were checked against Lean and independent computational evidence.
The process, including failures and corrections, is documented in
[the methodology note](docs/methods-note.md). This attribution reflects the
author's account; the checks themselves do not establish the originality
of the mathematical results.

## Three layers of confidence

**1. The kernel.** Lean's kernel accepts the spine; CI forbids `sorry`,
`admit`, `native_decide`, and project-local axioms via a comment-aware source
audit, and `AxiomAudit.lean` checks nine earlier selected end theorems, nine
cycle-spectrum proof declarations, five conditional graph-transfer
statements and two theorems added on 2026-10-18 against the explicit
allowlist above. The audit also requires
that every requested theorem actually appear in the Lean audit output.

**2. Independent re-checking.** The seven end theorems were re-verified with
`leanprover/comparator` (unmodified): statement equality against the
existing historical `Hardening/Challenge.lean` file, a transitive axiom
audit, and a full kernel replay of the exported proof terms — 1.32M
export lines, 10,324 theorems. Separately, a fresh agent re-transcribed
the seven statements from the Lean sources without seeing the historical
challenge. The two statement sets were token-identical after expanding
the section variable. The fresh transcription cross-checked the
historical challenge; **it was not the comparator's input**.
The authoritative run executed under a real landlock sandbox
(landrun on WSL2) with the nanoda external kernel accepting alongside Lean's
own; two deliberately broken controls (a one-token statement tamper, a
smuggled axiom) are rejected as expected. See
[`Hardening/REPORT.md`](Hardening/REPORT.md). The report covers **seven
historical theorems only**. A separate five-claim cycle-spectrum comparator
challenge **passed** on 2026-10-16 in run 38863604693, including both
Lean/nanoda acceptance and both negative rejections. The original logs
and exact tested commit are archived under `Hardening/runs/38863604693/`.
Thus the two runs cover **seven + five statements**, distinct from the
**25 declarations** selected for the current Lean axiom audit (18 before
graph transfer, 23 before the two theorems added on 2026-10-18). The cycle run records real landrun invocation but no
standalone OS denial probe. Its scope is documented separately in
[`Hardening/CYCLE-COMPARATOR.md`](Hardening/CYCLE-COMPARATOR.md).

**3. Empirical falsification pressure.** The `findings/` rounds (2–6, 8–10) attack the
theorems numerically — exhaustive enumeration of all graphs × all wrap sets at
n ≤ 5–6 (rounds 2–3), adversarial negators (rounds 3–5), randomized gap
checks at n = 7 (round 6), and round 8, which adds an implementation written
from the paper alone (no Lean sources consulted), a Lean-verified convention
battery (148 equalities tying the formalization's matrices to that
implementation on 74 concrete graphs), and a bounded-exhaustive n = 8 sweep —
7,246,819 configurations, zero failures. Round 10 independently tests both
cycle Fourier bases and full eigenvalue multisets at `n = 3,...,64`,
including a wrong-basis negative control. Another round-10 script
tests 124 canonical cycle matrix identities, 372 reindexed matrix
identities and 62 wrong-seam negative controls in exact integer
arithmetic, with no dependencies beyond Python. These scripts are
empirical evidence, not verified Lean results.

The theorem-by-theorem chain — claim → Lean theorem → axiom audit → numerical
check → comparator result → remaining gap — is tabulated in
[`Hardening/EVIDENCE-MAP.md`](Hardening/EVIDENCE-MAP.md), together with the
current errata ledger for the paper.

## Build and verification

Prerequisite: `elan` on your `PATH` (the toolchain is pinned by
`lean-toolchain`; don't run `lake update`, it would re-resolve Mathlib away
from the pinned v4.11.0).

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (optional but recommended)
lake build
```

Check one file:

```bash
lake env lean ConnectionLaplacian/L13_PSD.lean
```

The local hardening harness is outside the default target; build it
explicitly if you want it (see `Hardening/REPORT.md` for the comparator
toolchain):

```bash
lake build Hardening.Challenge Hardening.Solution Hardening.ConventionAnchor \
  Hardening.BatteryA Hardening.BatteryB Hardening.BatteryC Hardening.BatteryD
lake build Hardening.CycleChallenge Hardening.CycleSolution \
  Hardening.CycleNegative.BadChallenge Hardening.CycleNegative.BadSolution
python3 scripts/audit_cycle_comparator.py
```

Additional build guidance: `BUILD.md`.

## Guides

- `docs/thesis-guide.md` — thesis-style narrative, theorem map, reading order.
- `docs/graph-examples.md` — small graphs showing balanced vs. unbalanced
  wrap data.
- `docs/infographic.md` — one-page overview of the proof pipeline and
  kernel-dimension formulas.
- `docs/methods-note.md` — the methodology note: how the AI-assisted
  development was made trustworthy (untrusted generation, heterogeneous
  critics, kernel-verified residue, published errata ledger).
- `docs/cycle-spectrum-multiset-assembly.md` — the fully checked Fourier
  diagonalisation, real-root multisets, conditional graph transfer,
  and precise scope limits.
- `Hardening/argon4-review-adjudication-2026-10-18.md` — point-by-point
  adjudication of an external review of the v.0.0.5 manuscript, with the
  resulting fixes.
- `Hardening/CYCLE-COMPARATOR.md` — comparator challenges, negative
  controls, reproduction and an explicit verified-vs-pending evidence ledger.

## Paper

- Source: `paper/paper.tex` · PDF: `paper/paper.pdf`
- Title: *Kernel Dimension of the ℤ/2 Connection Laplacian on a Finite Simple
  Graph (A Formalisation in Lean 4 / Mathlib v4.11.0)*
- Author: Jesús Vilela Jato (Independent)
- Bibliography is embedded in `paper.tex` (no separate `.bib` file).

Build with a LaTeX engine supporting `amsart`, e.g. `tectonic paper/paper.tex`.

## Citation

Machine-readable metadata is in `CITATION.cff` (used by GitHub's **Cite this
repository** panel).

> Vilela Jato, J. *Connection Laplacian — verified spectral/balance stack
> (Lean 4 / Mathlib v4.11.0)*, 2026 (cite the release version given in
> `CITATION.cff`).  
> DOI: 10.5281/zenodo.19695396  
> https://github.com/jesusvilela/connection_laplacian_lean

## Licensing

- **Code and formalization artifacts:** Apache-2.0 (`LICENSE`)
- **Paper artifacts:** CC BY 4.0 (`LICENSE-paper`)

See `LICENSING.md` for full rationale and attribution guidance.
