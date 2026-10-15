# Round 9 — structured-adversarial sweep + third-kernel attempt

**Date:** 2026-10-15/16. **Result:** 3,314,688 configurations, zero
failures (48 min, 10 workers). The third-kernel attempt is
version-blocked (see below).

## Structured-adversarial sweep (`structured_sweep.py`)

The historical counterexample to the naive parity formula was K₄ with a
wrap **matching** — structured, not random, wrap data. Random wrap sampling
underweights exactly those families. This sweep runs the four checks
(kernel-dimension additivity, multiset spectrum union, fibre cardinality by
both routes + cover-component count, PSD) on:

- **every cut** of each graph (all 2^(n-1) vertex bipartitions; wrap = edges
  crossing the cut);
- **150 seeded spanning trees** per graph (wrap = tree edge set) via
  `nx.random_spanning_tree`;
- **150 seeded maximal matchings** per graph (greedy with shuffled order);
- the two extremes (∅ and E).

Graph universe (nauty `geng -c`, lists under `graphs/`):

| band | graphs |
|---|---|
| n=9, e=8..9 | 287 |
| n=9, e=10 | 797 |
| n=9, e=11 | 2075 |
| n=10, e=9 | 106 |
| n=10, e=10 | 657 |
| n=10, e=11 | 2678 |

All checks computed with the independent paper-only implementation from the
repo (`findings/round8/independent_impl.py`). Results:
`round9_structured_results.json`.

## Third-kernel attempt (lean4lean)

lean4lean (digama0) has no Lean v4.11 pin in its history (toolchain jumps
v4.10.0-rc2 → v4.12.0-rc1). Built at the 4.10.0-rc2 pin and pointed at the
project's 4.11 oleans: `failed to read file
'.lake/build/lib/ConnectionLaplacian.olean', invalid header` — olean format
mismatch, as expected. **Version-blocked, empirically confirmed.** The
independent-kernel role for this project remains covered by nanoda (dual
kernel in the comparator run); making lean4lean 4.11-compatible would be a
lean4export-scale port for marginal added assurance.

Binary archived at H:\cl-evidence-2026-10-15\lean4lean-4.10rc2-bin.
