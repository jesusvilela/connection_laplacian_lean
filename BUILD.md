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

As of 2026-04-22:

- `lake build` passes in this environment.
- The files imported by `ConnectionLaplacian.lean` are currently `sorry`-free.
- The imported spine runs through `L15_BridgeMonotone.lean`.
- Round-6 alpha/beta/gamma findings live under `findings/round6/`, but they
  are not part of the imported Lean build until formalized.

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
