# Round-2 Fuzzer Report

**Role:** FUZZER (numerical exhaustive search)
**Script:** `findings/round2/fuzzer/fuzz.py`
**Raw results:** `findings/round2/fuzzer/fuzz_results.json`

## Scope

Enumerated every simple graph on `n ∈ {2, 3, 4, 5}` up to isomorphism (51 graphs: 2 + 4 + 11 + 34, matches OEIS A000088) and, for each, every wrap subset `wrap : E → {T, F}` (`2^|E|` per graph).

**Total configurations tested: 3456.**

For each `(G, wrap)` the script builds `scalarLap(G)`, `signedLapMobius(G,wrap)`, `coverGraph(G,wrap)`, and `L̃ = scalarLap(coverGraph)`, then checks:

| Target | Claim | Check |
|--------|-------|-------|
| T1 (`L5_Cover.lean:176`) | `L̃` similar to `fromBlocks(scalarLap, 0, 0, signedLapMobius)` | spectrum equality via `eigvalsh`, tol `1e-7`. For real symmetric matrices of same size, this is equivalent to orthogonal conjugacy (implies existence of invertible P). |
| T2 (`L5_Cover.lean:199`) | `dim ker L̃ = dim ker scalarLap + dim ker signedLapMobius` | integer kernel dims via SVD. |
| T3 (`L6_Cohomology.lean:104`) | Per base component `C`, `#fiber = (2 if balanced else 1)` | cover components counted by projection; balance by brute-force 2-coloring. |

## Results

```
T1 failures: 0 / 3456
T2 failures: 0 / 3456
T3 failures: 0 / 3456
```

**All three targets hold on every configuration. No disagreement found.**

## Representative spot-checks

- `C_3`, no wrap → balanced, cover has 2 components (fiber=2); `ker L̃ = 2 = 1+1`.
- `C_3`, one wrap → unbalanced, cover has 1 component (fiber=1); `ker L̃ = 1 = 1+0`; `spec L̃ = {0,1,1,3,3,4}`.
- `C_4`, two adjacent wraps → balanced (even total wrap on cycle); fiber=2; `ker L̃ = 2`.
- `K_4`, single wrap edge → unbalanced; fiber=1; `ker L̃ = 1 = 1+0`.
- `K_3 ⊔ {v}`, one wrap on `K_3` → `K_3` unbalanced (fiber=1), isolated `v` vacuously balanced (fiber=2); total cover components = 3.

## Caveats

- T1 verified only through the necessary spectrum/trace/det equality. For two real symmetric matrices of the same size this is equivalent to orthogonal similarity, implying existence of invertible P.
- `n ≤ 5` only. The Lean statements depend only on isomorphism class.
- Numerical tolerances are conservative; no borderline cases observed.

## Confidence

**High confidence that all three `sorry`'d statements are mathematically true as stated.** Zero counterexamples across 3456 exhaustive configurations plus manual probes. Remaining work is Lean proof engineering, not statement repair.
