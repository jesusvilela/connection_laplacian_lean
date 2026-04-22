# NEGATOR report — L5_Cover.lean:199 kernel-dimension decomposition

**Target:** `finrank ℝ (ker (toLin' G̃.scalarLaplacian)) = finrank ℝ (ker (toLin' G.scalarLaplacian)) + finrank ℝ (ker (toLin' G.signedLaplacianMobius))`
where `G̃ = G.orientationDoubleCover`.

## Verdict
**No counterexample found.** The decomposition holds in every case tested (hundreds of graphs). The target is almost certainly TRUE.

## Sign convention (from `KernelDimension.lean:74–80`)
`signedLaplacianMobius u v` on adjacent pair = `+1 if wrap, -1 otherwise`. Zaslavsky predicts `dim ker L_σ = #balanced components`.

## Exhaustive small-graph sweep (every wrap subset)

| graph | n | m | #subsets | fails |
|-------|---|---|---|---|
| C₃ | 3 | 3 | 8 | 0 |
| C₄ | 4 | 4 | 16 | 0 |
| C₅ | 5 | 5 | 32 | 0 |
| C₆ | 6 | 6 | 64 | 0 |
| P₃ (tree) | 3 | 2 | 4 | 0 |
| K₄ | 4 | 6 | 64 | 0 |
| K₄−e (theta) | 4 | 5 | 32 | 0 |
| C₃ ⊔ C₄ | 7 | 7 | 128 | 0 |
| 2·C₃ | 6 | 6 | 64 | 0 |

All 412 (wrap-assignment, graph) combinations satisfy
`dim ker L_cov = dim ker L_scalar + dim ker L_signed`.

Representative rows (ker_cov, ker_scalar, ker_signed):
- C₃ 0 wrap: (2,1,1) — cover = 2·C₃.
- C₃ 1 wrap: (1,1,0) — cover = C₆, unbalanced cycle.
- C₃ 2 wrap: (2,1,1) — balanced.
- K₄ 1 wrap: (1,1,0).
- K₄ 0 wrap: (2,1,1).
- 2·C₃ all-wrap: (2,2,0) — both components unbalanced.
- C₆ wraps={0,2,4}: (2,1,1) — even wrap, balanced.
- C₆ wraps={0,2,3}: (1,1,0) — odd wrap, unbalanced.

## Random stress test
200 random graphs, n ∈ {3,…,12}. **0/200 failures.**

## Consistency with derived bridges
Every sample also satisfies `dim ker L_signed = #balancedComponents(G)` and `#π₀(G̃) = #π₀(G) + #balancedComponents(G)`.

## Tree special case
All tree tests give `ker_signed = ker_scalar = #components`. Consistent with "any edge signing on a tree is a coboundary".

## Bottom line
The sorry at `L5_Cover.lean:199` should be closed positively. No refutation in search envelope.
