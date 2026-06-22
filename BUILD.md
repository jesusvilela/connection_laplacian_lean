# Building locally

## Prerequisites

You need `elan` on your `PATH`. The project is pinned by `lean-toolchain` to
Lean `v4.11.0`, and `lake` will pull the matching toolchain automatically.

## Build

From inside this directory:

```bash
lake update
lake build
```

The first build is the slow one because Mathlib is large. Incremental rebuilds
are much faster.

## Current imported state

- `lake build` builds the verified spine.
- The files imported by `ConnectionLaplacian.lean` are `sorry`-free and free of
  user-introduced axioms.
- The imported spine runs from `Basic` through `L17_TracesAndLipschitz.lean`.
- The Python cross-checks under `findings/` are numerical validations cited by
  the paper, not part of the Lean build.

## Useful commands

Check one file:

```bash
lake env lean ConnectionLaplacian/L12_WalkH1.lean
```

Rebuild after edits:

```bash
lake build
```

Inspect the import spine:

```bash
type ConnectionLaplacian.lean
```

## If something breaks

Most first-order failures are one of these:

1. Toolchain mismatch.
2. Mathlib download or cache problem.
3. A local edit broke a proof term or import.

For tactic-level issues, rebuild the single file first with `lake env lean ...`
before rebuilding the full project.

## What this file no longer describes

This guide is for the live build only.

- It is no longer a "working on the sorry markers" document.
- It does not describe the project as a two-theorem seed.
- It does not treat the environment as uncompiled or hypothetical.
