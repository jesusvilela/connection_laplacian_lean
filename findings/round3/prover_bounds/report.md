# PROVER-BOUNDS — Round 3 discovery findings

Target: `H:/NP Completeness Bunny UTAI study/connection_laplacian_lean` (Mathlib v4.11.0)

Ground truth reused:
- `scalarLaplacian_kernel_dim = numComponents` (L4)
- `signedLaplacian_kernel_dim_general = numBalancedComponents` (L8)
- `connectionLaplacian_kernel_dim_general` (L8)
- `numBalancedComponents_le` (L6.3)

## Claim-by-claim

### 1. Kernel-drop bound — TRUE, trivial (~5 LOC)
```lean
lemma kernel_drop_le_numComponents :
    finrank ℝ (ker (toLin' (G.laplacian false)))
      - finrank ℝ (ker (toLin' (G.laplacian true))) ≤ G.numComponents
lemma kernel_drop_eq_unbalanced :
    ... = G.numComponents - G.numBalancedComponents
```
Rewrite with `connectionLaplacian_kernel_dim_general`; `omega`.

### 2. Spectral gap / Fiedler — Mathlib GAP
No `algebraicConnectivity` / Fiedler named constant in v4.11.0. Cheap substitute (~40 LOC after claim 6):
```lean
lemma signedLap_has_positive_eigenvalue_iff :
    (∃ (h : G.signedLaplacianMobius.IsHermitian) (i : G.V), 0 < h.eigenvalues i) ↔
    G.numBalancedComponents < Fintype.card G.V
```

### 3. Frustration index — SKIP
500+ LOC and adds no new information over L8's sharp formula.

### 4. Coarea bound — TRIVIAL (3 LOC)
```lean
lemma signed_kernel_le_scalar_kernel :
    finrank ℝ (ker (toLin' G.signedLaplacianMobius)) ≤
      finrank ℝ (ker (toLin' G.scalarLaplacian))
```

### 5. Monotonicity under edge addition — PARTIAL
- 5a. `numComponents` non-increasing: TRUE but ~30 LOC. Not in Mathlib cleanly.
- 5b. Non-wrap edge inside a balanced component: **NOT unconditional**. C_4 balanced (ε≡false); adding wrap diagonal (0,2) forces ε(0)≠ε(2); non-wrap path forces equality ⇒ unbalanced. Correct statement depends on witness coloring at new endpoints.
- 5c. Merging two balanced components by any single edge: TRUE; flip one component's witness. ~60 LOC.

### 6. PSD-ness of L_signed — TRUE, known (~80 LOC)
Quadratic form: `⟨x, L_sign x⟩ = Σ_{non-wrap} (x_u−x_v)² + Σ_{wrap} (x_u+x_v)²`. Template: `Mathlib/.../LapMatrix.lean:70-89`. Prior scaffold: `findings/round2/prover_kerdim/attempt.lean:167-194`.

### 7. Trace = 2|E| — TRUE, easy, novel, HIGHEST PRIORITY
Use `SimpleGraph.sum_degrees_eq_twice_card_edges`. 8/10/20 LOC each.
```lean
theorem trace_scalarLaplacian : Matrix.trace G.scalarLaplacian = 2 * G.graph.edgeFinset.card
theorem trace_signedLaplacianMobius : Matrix.trace G.signedLaplacianMobius = 2 * G.graph.edgeFinset.card
theorem trace_laplacian (mobius : Bool) : Matrix.trace (G.laplacian mobius) = 4 * G.graph.edgeFinset.card
```

### 8. `sum_wrapEdgesIn = #{e // wrap e}`
Each wrap edge in exactly one component. ~30 LOC, novel but internal-only.

## Ranking

| Rank | Claim | LOC | Grade |
|------|-------|-----|-------|
| 1 | Claim 7 — trace = 2|E| (×3) | 8-20 | A+ |
| 2 | Claim 4 — signed ≤ scalar kernel | 3 | A+ |
| 3 | Claim 1 — kernel drop bound | 5 | A |
| 4 | Claim 6 — L_signed PSD | 80 | B+ |
| 5 | Claim 2 — positive eigenvalue iff unbalanced | 40 | B |
| 6 | Claim 5c — merge balanced via any edge | 60 | B |
| 7 | Claim 5b — intra-component add | 120 | B− |
| 8 | Claim 8 — sum_wrapEdgesIn | 30 | C+ |
| 9 | Claim 3 — frustration index | 500+ | D |

## Recommended next round

`ConnectionLaplacian/L9_Bounds.lean` (~40 LOC total):
1. `trace_scalarLaplacian`
2. `trace_signedLaplacianMobius`
3. `trace_laplacian`
4. `signed_kernel_le_scalar_kernel`
5. `kernel_drop_le_numComponents`
6. `kernel_drop_eq_unbalanced`

Follow-up `L10_PosSemidef.lean`: claim 6 + claim 2 (~120 LOC).

**Headline:** claims 7, 4, 1 are drop-in consequences of L8 + one Mathlib degree-sum theorem. ~40 LOC, all novel, no new imports, closes the trace/inequality gap.
