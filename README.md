# Connection Laplacian — verified spectral/balance stack

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.TBD.svg)](https://doi.org/10.5281/zenodo.TBD)
[![Code License: Apache-2.0](https://img.shields.io/badge/code-Apache--2.0-blue.svg)](LICENSE)
[![Paper License: CC BY 4.0](https://img.shields.io/badge/paper-CC--BY--4.0-green.svg)](LICENSE-paper)
[![Lean 4](https://img.shields.io/badge/Lean-4.11.0-orange.svg)](lean-toolchain)

> **DOI placeholder.** The `TBD` DOI resolves once the repo is enabled on
> Zenodo and a GitHub release is cut — see [Archival](#archival-zenodo-doi).

This directory contains the active Lean 4 formalization for the
connection-Laplacian line of the study. It began as a two-theorem seed and now
builds as a larger imported spine from `Basic` through
`L15_BridgeMonotone`.

## Current state (2026-04-22)

- `lake build` passes in this environment against
  `leanprover/lean4:v4.11.0` + Mathlib v4.11.0.
- No file imported by `ConnectionLaplacian.lean` currently contains `sorry`.
- Round 5 landed three new exact files:
  `L13_PSD.lean`, `L14_CycleEw.lean`, `L15_BridgeMonotone.lean`.
- Round 6 stage 1 produced additional alpha/beta/gamma claim candidates in
  `findings/round6/stage1_negator_A/`, but those remain empirical until they
  are formalized.

## Imported modules

- `ConnectionLaplacian/Basic.lean` — `ConnGraph`, flat/Mobius Laplacians,
  symmetric matrix infrastructure.
- `ConnectionLaplacian/KernelDimension.lean` — scalar/signed/Mobius kernel
  decomposition and counting infrastructure.
- `ConnectionLaplacian/CycleSpectrum.lean` — explicit cycle spectra.
- `ConnectionLaplacian/L5_Cover.lean` — orientation double cover and scalar
  cover splitting.
- `ConnectionLaplacian/L6_Cohomology.lean` — balance, fiber structure, and
  cohomological language.
- `ConnectionLaplacian/L8_Recognition.lean` — recognition theorems bridging
  balance and kernels.
- `ConnectionLaplacian/L9_Bounds.lean` — trace formulas and kernel
  inequalities.
- `ConnectionLaplacian/L10_CoverCharpoly.lean` — cover characteristic
  polynomial factorization.
- `ConnectionLaplacian/L11_Trees.lean` — tree balance and tree kernel
  corollaries.
- `ConnectionLaplacian/L12_WalkH1.lean` — closed-walk parity characterisation
  of balance.
- `ConnectionLaplacian/L13_PSD.lean` — positive semidefiniteness of the signed
  Mobius Laplacian.
- `ConnectionLaplacian/L14_CycleEw.lean` — Eulerian-walk cycle parity
  specialization.
- `ConnectionLaplacian/L15_BridgeMonotone.lean` — bridge-monotonicity for the
  number of balanced components.

## Exact floor

Representative exact results already in the imported build:

- `cover_charpoly_eq_scalar_times_mobius`
- `isBalanced_iff_closedWalk_wrap_even`
- `signedLaplacianMobius_posSemidef`
- `numBalancedComponents_monotone_remove_nonwrap_nonbridge`

These are machine-checkable. They are not merely narrative summaries.

## Empirical frontier

The current empirical frontier is organized sheaf-wise:

- `findings/round6/stage1_negator_A/sheaf_alpha/` — edge-operation claims
- `findings/round6/stage1_negator_A/sheaf_beta/` — spectral claims
- `findings/round6/stage1_negator_A/sheaf_gamma/` — balance/cohomology claims

High-leverage stage-1 candidates include:

- `A8` parity-matching subdivision invariance,
- `B7` spectral multiset union,
- `B9` `dim ker L_mob = #components + beta`,
- `G12` switching invariance of `beta`,
- `G15` `dim ker L_signed = beta`.

Treat these as empirical until they land in Lean.

## Build

From inside this directory:

```bash
lake build
```

To check a single file:

```bash
lake env lean ConnectionLaplacian/L13_PSD.lean
```

## Scope discipline

This directory is not the whole UTAI program.

- It does not prove the broader hyperbolic or topos manifestos.
- It does not promote round-6 candidates to theorem status automatically.
- It does not license falsified claims that already failed in the findings
  rounds.

Use it as the exact spectral/balance core that Bunny can currently defend.

## Paper

- Source: `paper/paper.tex`
- Built PDF: `paper/paper.pdf`
- Title: *Kernel Dimension of the ℤ/2 Connection Laplacian on a Finite Simple Graph (A Formalisation in Lean 4 / Mathlib v4.11.0)*
- Author: Jesús Vilela Jato (Independent)
- Bibliography is embedded in `paper.tex` (no separate `.bib`).

Compile with any LaTeX engine supporting `amsart`. Example with Tectonic:

```bash
tectonic paper/paper.tex
```

## Citation

A machine-readable citation record lives in `CITATION.cff` — GitHub renders
a "Cite this repository" button from it. Once the Zenodo DOI is minted (see
below), cite the **concept DOI** so references remain valid across future
versions.

Human-readable form:

> Vilela Jato, J. *Connection Laplacian — verified spectral/balance stack*
> (Lean 4 / Mathlib v4.11.0), 2026.
> DOI: 10.5281/zenodo.TBD — https://github.com/jesusvilela/connection_laplacian_lean

## Licensing

Split by artifact type:

- **Code** (Lean files, Python fuzzers, build configuration) — Apache-2.0.
  See `LICENSE`.
- **Paper** (`paper/paper.tex`, `paper/paper.pdf`) — CC BY 4.0.
  See `LICENSE-paper`.

Full rationale and attribution template: `LICENSING.md`.

## Archival (Zenodo DOI)

The repository is prepared for Zenodo archival. To mint the DOI after the
initial push:

1. Visit <https://zenodo.org/account/settings/github/> and sign in with GitHub.
2. Flip the toggle for `jesusvilela/connection_laplacian_lean`.
3. On GitHub: create a release — tag `v0.1.0`, release notes = paper abstract.
4. Zenodo mints two DOIs automatically: a *concept DOI* (always latest) and
   a *version DOI* for `v0.1.0`. Usually under a minute.
5. Open a follow-up commit that replaces every `10.5281/zenodo.TBD` occurrence
   across `CITATION.cff`, `README.md`, `LICENSING.md`, and `LICENSE-paper`
   with the concept DOI. Tag `v0.1.1` so Zenodo mints a matching version DOI.

Cite the **concept DOI** (not the per-version DOI) in the paper and in any
arXiv endorsement emails — future versions inherit it automatically.
