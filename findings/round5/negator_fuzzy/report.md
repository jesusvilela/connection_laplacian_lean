# NEGATOR-FUZZY R5 — 22 new fuzzy claims

**Date:** 2026-04-22. **Envelope:** all non-iso ConnGraphs on n ∈ {3,4,5} × every wrap subset (~3,453 base configs), plus n=6 20-iso × 20-wrap slice for 6 signature claims. Total configs: ~75k.

## Summary (ranked by τ)

| # | claim | precondition | τ | supp / total |
|---|-------|--------------|---|--------------|
| R4  | β(G,W)=β(G,E\W) for bipartite G | G bipartite | **1.0000** | 245/245 |
| R5  | Pr[β≥1] non-increasing in |E| (iso-class avg) | uniform iso | **1.0000** | 19/19 |
| R6  | subdividing non-wrap edge preserves β | e∉W, new edges non-wrap | **1.0000** | 398/398 |
| R7  | subdividing wrap edge (1+1 split) preserves β | e∈W | **1.0000** | 398/398 |
| R8  | contracting bridge non-wrap edge preserves β | e bridge, e∉W | **1.0000** | 46/46 |
| R9  | λ₂(L_sig) ≥ 0 (PSD) | — | **1.0000** | 3853/3853 |
| R10 | λ_min(L_sig)=0 iff β≥1 | — | **1.0000** | 3853/3853 |
| R11 | tr(L_möb²) = tr(L_s²)+tr(L_sig²) | — | **1.0000** | 3853/3853 |
| R12 | tr(L_möb^k) = tr(L_s^k)+tr(L_sig^k), k ∈ {3,4} | — | **1.0000** | 6906/6906 |
| R13 | ker(L_sig) has ±1 basis vector per balanced comp | G conn, balanced | **1.0000** | 392/392 |
| R14 | rank(L_möb↾fibre C) = 2|C|−(1+[C balanced]) | — | **1.0000** | 4090/4090 |
| R15 | #{W : G balanced} = 2^(|V|−#comps) | — | **1.0000** | 49/49 |
| R16 | min nonzero coboundary size = edge-connectivity | G conn, n≥2 | **1.0000** | 29/29 |
| R17 | spectral interlacing under non-wrap edge removal | e∉W | **1.0000** | 13943/13943 |
| R18 | tr(L_sig) = tr(L_s) = 2|E| | — | **1.0000** | 3453/3453 |
| R19 | ‖L_möb‖_F² = 2·Σdeg² + 4|E| | — | **1.0000** | 3453/3453 |
| R20 | β(G₁⊔G₂, W₁⊔W₂) = β(G₁,W₁)+β(G₂,W₂) | disjoint union | **1.0000** | 144/144 |
| R21 | G conn + balanced ⇒ (V,W) bipartite | G conn, balanced | **1.0000** | 792/792 |
| R22 | ker(L_möb) = sym-lift(ker L_s) ⊕⊥ anti-lift(ker L_sig) | — | **1.0000** | 3453/3453 |
| R2  | β(G,W)=β(G−e,W), non-bridge non-wrap e, G conn | G conn, e non-bridge, e∉W | 0.9260 | 11782/12724 |
| R1  | β(G,W) ≥ β(G−e,W), non-bridge non-wrap e (wrong direction) | e non-bridge, e∉W | 0.9208 | 12062/13100 |
| R3  | β(G,W)=β(G,E\W) when W is a Z/2 coboundary | W=δ(S) | 0.3374 | 165/489 |

## Cross-check with PROVER-C1-NONBRIDGE

R1 as phrased here is the OLD direction `β(G) ≥ β(G−e)`, which fails (τ=0.92). The correct direction is `β(G) ≤ β(G−e)` for non-bridge non-wrap e. **This is exactly the inequality the R5 PROVER-C1-NONBRIDGE formalised as `numBalancedComponents_monotone_remove_nonwrap_nonbridge` in `L15_BridgeMonotone.lean:258`.** Independent convergence, no conflict.

## Minimal counterexamples

### R1 / R2 — K₃ rebalancing
`G = K₃`, `W = {(0,1)}`: β = 0 (odd cycle, unbalanced). Remove non-bridge non-wrap edge (0,2): remaining path is balanced ⇒ β = 1. `β(G) ≥ β(G−e)` fails (0 < 1); `β(G) ≤ β(G−e)` holds (0 ≤ 1).

### R3 — K₃ with empty coboundary
`S = ∅` ⇒ W = δ(∅) = ∅: β(G,∅)=1. E\∅ = all three edges: β(G,E)=0 on K₃. Complement is *not* a coboundary. Refinement: strengthen to "both W and E\W are coboundaries" ⇔ G bipartite (→ R4, τ=1).

## R6 prover candidates (τ=1, ≥ 50 supports)

Clean targets for future formalisation:

- **R9** `signedLaplacianMobius_posSemidef` — already landed in R5 (`L13_PSD.lean`).
- **R11/R12** trace power-sum split — extends L9 traces to higher powers.
- **R14** fibre-restriction rank formula — sharpens `s1_cover_ker_dim`.
- **R15** coboundary count 2^(|V|−#π₀) — pure H¹(G;Z/2) dim.
- **R17** Cauchy interlacing under non-wrap edge removal.
- **R18/R19** trace / Frobenius norm identities.
- **R21** balance implies bipartite-(V,W).
- **R22** explicit orthogonal decomposition of ker L_möb.

Top-3 high-novelty R6 targets (not already in Lean, high leverage):
1. **R14** rank formula — new file `L5_Cover.lean` supplement.
2. **R15** coboundary count — natural addition to `L6_Cohomology.lean`.
3. **R17** Cauchy interlacing — new file or extend `L13_PSD.lean`.

## Artifacts

- `fuzz_r5.py` — 22-claim driver.
- `extend_n6.py` — n=6 extension for top 6 claims (all passed at τ=1).
- `results.json` — base-envelope raw data.
- `results_n6.json` — n=6 extended data.

## Net

17 new τ=1 candidates plus 2 confirmations of landed theorems (R9, R18 are covered by L9_Bounds and L13_PSD). R1/R2 independently confirm the L15 inequality direction. Strong R6 pipeline for next round.
