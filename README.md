# Connection Laplacian (Lean 4 Formalization)

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.19695396-blue.svg)](https://doi.org/10.5281/zenodo.19695396)
[![Code License: Apache-2.0](https://img.shields.io/badge/code-Apache--2.0-blue.svg)](LICENSE)
[![Paper License: CC BY 4.0](https://img.shields.io/badge/paper-CC--BY--4.0-green.svg)](LICENSE-paper)
[![Lean 4](https://img.shields.io/badge/Lean-4.11.0-orange.svg)](lean-toolchain)

This repository contains a Lean 4 / Mathlib formalization of core results on
the ℤ/2 connection Laplacian on finite simple graphs, including structural,
kernel-dimension, and spectral statements.

The accompanying paper is available under `paper/` and has been submitted as a
candidate to the upcoming FLoC Lisbon cycle.

> **DOI:** <https://doi.org/10.5281/zenodo.19695396>

## Project status

- This repository is scoped **solely** to the ℤ/2 connection-Laplacian
  kernel-dimension theory: the verified Lean spine, the paper, and the
  numerical cross-checks that accompany the paper.
- The master file `ConnectionLaplacian.lean` imports exactly the verified
  spine, from `Basic` through `L17_TracesAndLipschitz`; every imported file is
  maintained as `sorry`-free and free of user-introduced axioms.
- The `findings/` directory holds only the Python numerical cross-checks
  cited by the paper. They are empirical validations of the formal theorems,
  not theorems themselves.

## Verified development (import spine)

The formalized library currently imports:

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

Representative machine-checked theorems include:

- `cover_charpoly_eq_scalar_times_mobius`
- `isBalanced_iff_closedWalk_wrap_even`
- `signedLaplacianMobius_posSemidef`
- `numBalancedComponents_monotone_remove_nonwrap_nonbridge`
- `mobius_charpoly_roots_eq_union`
- `frobenius_laplacian_decomposes`
- `trace_mul_scalar_signed_eq`

## Numerical cross-checks (not theorems)

The paper's formal theorems are independently exercised by the Python fuzzers
and negators retained under `findings/`:

- `findings/round2/fuzzer/` — exhaustive sweep at orders `n ≤ 5`.
- `findings/round3/negator/`, `findings/round4/negator_fuzzy/` — adversarial
  negation searches against the kernel-dimension and fibre-cardinality claims.
- `findings/round6/stage2_fuzzer_A/`, `findings/round6/stage6_fuzzer_B/` —
  extended cross-checks.

These scripts are empirical evidence for the formal statements, not verified
Lean results.

## Build and verification

Prerequisite: `elan` on your `PATH` (toolchain pinned by `lean-toolchain`).

```bash
lake update
lake build
```

Check one file:

```bash
lake env lean ConnectionLaplacian/L13_PSD.lean
```

Additional build guidance is available in `BUILD.md`.

## Repository scope

- **Verified content:** files imported by `ConnectionLaplacian.lean`.
- **Numerical cross-checks:** `findings/` (Python fuzzers/negators cited by the
  paper).
- **Paper materials:** `paper/paper.tex` and `paper/paper.pdf`.
- **Reader guides:** `docs/` (thesis-style overview, graph examples, and a
  compact infographic for navigating the formalization).

## Thesis and manual-style guides

The following Markdown guides are intended as lightweight companions to the
paper and Lean sources:

- `docs/thesis-guide.md` — thesis-style narrative, theorem map, and reading
  order.
- `docs/graph-examples.md` — small graph examples illustrating balanced and
  unbalanced wrap data.
- `docs/infographic.md` — one-page visual overview of the proof pipeline and
  kernel-dimension formulas.

## Paper

- Source: `paper/paper.tex`
- PDF: `paper/paper.pdf`
- Title: *Kernel Dimension of the ℤ/2 Connection Laplacian on a Finite Simple
  Graph (A Formalisation in Lean 4 / Mathlib v4.11.0)*
- Author: Jesús Vilela Jato (Independent)
- Bibliography is embedded in `paper.tex` (no separate `.bib` file).

Build with a LaTeX engine supporting `amsart` (example):

```bash
tectonic paper/paper.tex
```

## Citation

Machine-readable metadata is in `CITATION.cff` (used by GitHub’s **Cite this
repository** panel).

Please cite this repository as:

> Vilela Jato, J. *Connection Laplacian (Lean 4 Formalization)*, 2026.  
> DOI: 10.5281/zenodo.19695396  
> https://github.com/jesusvilela/connection_laplacian_lean

## Licensing

- **Code and formalization artifacts:** Apache-2.0 (`LICENSE`)
- **Paper artifacts:** CC BY 4.0 (`LICENSE-paper`)

See `LICENSING.md` for full rationale and attribution guidance.
