# Connection Laplacian (Lean 4 Formalization)

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.19695396-blue.svg)](https://doi.org/10.5281/zenodo.19695396)
[![Code License: Apache-2.0](https://img.shields.io/badge/code-Apache--2.0-blue.svg)](LICENSE)
[![Paper License: CC BY 4.0](https://img.shields.io/badge/paper-CC--BY--4.0-green.svg)](LICENSE-paper)
[![Lean 4](https://img.shields.io/badge/Lean-4.11.0-orange.svg)](lean-toolchain)

Take a finite simple graph, mark some of its edges as *wrap* edges, and build
the ℤ/2 connection Laplacian. This repository formalizes the resulting theory
end to end in Lean 4 / Mathlib — the block decomposition into scalar and
signed Laplacians, the orientation double cover, and the headline facts that
the kernel dimension of the signed Laplacian counts the *balanced* components
and the full connection Laplacian satisfies exact kernel and spectral
identities.

Everything on the verified spine is machine-checked from the three standard
Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) and nothing else.
Around the spine sits an explicit verification apparatus — a comparator pass
under a real sandbox, an independent reimplementation of the paper's
definitions, and exhaustive numerical sweeps — documented theorem by theorem
in [`Hardening/EVIDENCE-MAP.md`](Hardening/EVIDENCE-MAP.md).

The accompanying paper lives under `paper/` and has been submitted as a
candidate to the upcoming FLoC Lisbon cycle.

> **DOI:** <https://doi.org/10.5281/zenodo.19695396>

## What is where

| Layer | Contents | Epistemic status |
|---|---|---|
| Verified spine | everything imported by `ConnectionLaplacian.lean` | machine-checked Lean proofs, CI-enforced trust boundary |
| Hardening harness | `Hardening/` | comparator challenge/solution modules, convention-anchor battery, run logs, evidence map, review adjudication |
| Numerical cross-checks | `findings/` (rounds 2–6 and 8; round 7 is kept local-only) | Python; empirical evidence for the formal statements, not theorems |
| Paper + guides | `paper/`, `docs/` | manuscript (LaTeX + PDF) and reader companions |

The repository is scoped solely to the ℤ/2 connection-Laplacian
kernel-dimension theory: the verified spine, the paper, its numerical
cross-checks, and the hardening harness around them. Nothing else is
maintained here.

## Verified development (import spine)

`ConnectionLaplacian.lean` imports exactly the spine below; every file is
maintained `sorry`-free and free of user-introduced axioms.

- `ConnectionLaplacian/Basic.lean`
- `ConnectionLaplacian/KernelDimension.lean`
- `ConnectionLaplacian/CycleSpectrum.lean`
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
- `numBalancedComponents_monotone_remove_nonwrap_nonbridge` *(deleting a
  non-bridge edge cannot destroy balanced components)*
- `mobius_charpoly_roots_eq_union` *(the Möbius spectrum is the scalar ⊎
  signed multisets)*
- `frobenius_laplacian_decomposes` *(‖L‖²_F splits as scalar + signed parts)*
- `trace_mul_scalar_signed_eq` *(the polarisation identity for the mixed
  trace)*

## Three layers of confidence

**1. The kernel.** Lean's kernel accepts the spine; CI forbids `sorry`,
`admit`, `native_decide`, and project-local axioms via a comment-aware source
audit, and `AxiomAudit.lean` checks the seven end theorems against the
explicit allowlist above.

**2. Independent re-checking.** The seven end theorems were re-verified with
`leanprover/comparator` (unmodified): statement equality against an
independently transcribed challenge, a transitive axiom audit, and a full
kernel replay of the exported proof terms — 1.32M export lines, 10,324
theorems. The authoritative run executed under a real landlock sandbox
(landrun on WSL2) with the nanoda external kernel accepting alongside Lean's
own; two deliberately broken controls (a one-token statement tamper, a
smuggled axiom) are rejected as expected. See
[`Hardening/REPORT.md`](Hardening/REPORT.md).

**3. Empirical falsification pressure.** The `findings/` rounds (2–6 and 8) attack the
theorems numerically — exhaustive enumeration of all graphs × all wrap sets at
n ≤ 5–6 (rounds 2–3), adversarial negators (rounds 3–5), randomized gap
checks at n = 7 (round 6), and round 8, which adds an implementation written
from the paper alone (no Lean sources consulted), a Lean-verified convention
battery (148 equalities tying the formalization's matrices to that
implementation on 74 concrete graphs), and a bounded-exhaustive n = 8 sweep —
7,246,819 configurations, zero failures. These scripts are empirical
evidence, not verified Lean results.

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
```

Additional build guidance: `BUILD.md`.

## Guides

- `docs/thesis-guide.md` — thesis-style narrative, theorem map, reading order.
- `docs/graph-examples.md` — small graphs showing balanced vs. unbalanced
  wrap data.
- `docs/infographic.md` — one-page overview of the proof pipeline and
  kernel-dimension formulas.

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

> Vilela Jato, J. *Connection Laplacian (Lean 4 Formalization)*, 2026.  
> DOI: 10.5281/zenodo.19695396  
> https://github.com/jesusvilela/connection_laplacian_lean

## Licensing

- **Code and formalization artifacts:** Apache-2.0 (`LICENSE`)
- **Paper artifacts:** CC BY 4.0 (`LICENSE-paper`)

See `LICENSING.md` for full rationale and attribution guidance.
