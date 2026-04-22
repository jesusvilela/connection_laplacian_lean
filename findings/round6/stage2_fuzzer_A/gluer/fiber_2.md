# R6 Stage 2 gluer — fiber-2 manifest

**Date:** 2026-04-22. **Upstream:** Stage 2 FUZZER-A sheaves α / β / γ. **Downstream:** Stage 3 PROVER-A.

## Envelope consolidated

| sheaf | n | method | top-line |
|-------|---|--------|----------|
| α | n ≤ 5 exhaustive + n=6 sample (350 conn × 16 W); plus ineq fuzz @ n=6 random 2200 | networkx + py | 6 α τ=1 confirmed; 1 NEW τ=1 (L15-rev); 2 Stage-1 conjectures FAIL |
| β | n=6 **exhaustive iso** (156 classes × up-to-24 W = 3507) + n=7 sample 220 + 6 mpmath prec=50 spot-checks | numpy + mpmath | 6 β τ=1 confirmed including M6/M7 at 1.5e-15 rel diff; sanity-landings (G15/B9/B21) pass |
| γ | n=6 **exhaustive** (all 112 conn iso × all 2^m W); 5.17 M triples on G12 | pure-py integer | **12 γ claims PASS**, 0 CEs in 10.8 M exact integer checks |

Total Stage-2 evidence: **~6.1 M probes across 27 distinct claims**. Zero τ=1 claim regressed from Stage 1. Two Stage-1 extrapolations refuted with structural CEs. One genuinely new τ=1 discovery (L15-rev).

## τ=1 survivors — Stage-3 PROVER-A queue (ranked by (leverage × ease))

### Tier 1 — master lemmas (highest collapsing power)

| id | claim | leverage | ease | src sheaf |
|----|-------|---------:|------|-----------|
| **M6** | `spec(L_möb) = spec(L_s) ⊎ spec(L_sig)` (multiset) | collapses B1/B6/B12/B13/B17/B19/B20 | mid (explicit orthogonal Hadamard-fibre change-of-basis) | β |
| **M7** | `p_{L_möb}(x) = p_{L_s}(x) · p_{L_sig}(x)` (charpoly) | polynomial form of M6 | easy-after-M6 (or via `Matrix.charpoly_blockDiagonal`) | β |
| **A13** | β is vertex-switching invariant | unlocks α-normalisation for A2/A3/A8 | easy (Mathlib signed-group action) | α (= G12 / M2 cross-check) |

### Tier 2 — counting bundle (γ coboundary/cocycle)

| id | claim | prereq |
|----|-------|--------|
| **G14** | Euler χ: `\|V\| − \|E\| = #π₀ − β₁` | Mathlib `edgeFinset.card`, `ConnectedComponent` |
| **G13** | #coboundaries = 2^{\|V\|−#π₀} | rank-nullity on δ: (Z/2)^V → (Z/2)^E |
| **G1**  | #switching-classes = 2^{β₁(G)} | G13 + quotient arg |
| **G21** | #coboundaries · #switching-classes = 2^{\|E\|} | G1 × G13 |
| **G18** | #switching-classes = ∏ᵢ 2^{β₁(Cᵢ)} | G1 componentwise |

### Tier 3 — cycle-parity / balance (requires new Lean file `L16_CycleSpace.lean`)

| id | claim |
|----|-------|
| **G2**  | cycle-parity is switching-invariant |
| **G3**  | balanced ⇔ every fundamental cycle has even wrap-count |
| **G4**  | switching-class ↔ cycle-basis parity vector bijection |
| **G12** | β(G, W) = β(G, W △ δ(S)) (β switching-invariance full) |
| **M2**  | merge of A13 + G2 + G12 (reprove as single theorem) |
| **M5**  | balance ⇔ every Z/2-cycle-space element has even wrap-count |

### Tier 4 — α edge operations (after A13, tier 2/3)

| id | claim |
|----|-------|
| **A8** | k-subdivision with parity-matched new wraps preserves β (k ∈ {2,3}) — subsumes R5 R6/R7/A7 |
| **A2** | pendant non-wrap add preserves β |
| **A3** | pendant wrap add (= A2 ∘ A13) |
| **A10** | add-2-edges commutes for β |
| **A12** | θ-replacement of non-wrap edge preserves β (α-∩-γ proof) |

### Tier 5 — β spectral corollaries (after M6)

| id | claim | expected proof length in Lean |
|----|-------|------|
| **B2** | `tr(L_s · L_sig) = Σ deg² + 2m − 4\|W\|` | ~5 lines (no spectrum needed) |
| **B14** | single-flip Weyl stability ≤ 2 | ~20 lines via rank-2 perturbation |
| **B15** | multi-edge interlacing k ≤ 3 (and general k) | ~40 lines, Cauchy interlacing |
| **B16** | conn ∧ β=0 ⇒ λ_min(L_sig) > 0 | corollary: PSD + G15 |
| **L15-rev** | β(G−e, W) ≤ β(G, W) + 1 (NEW two-sided bound with L15) | Weyl +1 bound |
| **G5**  | #ε witnesses = 2^{#π₀} balanced, else 0 | orthogonal γ-island — split-off |

## Stage-2 sinks — claims refuted at scale

| id | τ (Stage 2) | Stage-1 hypothesis | refinement forwarded to Stage 5 |
|----|------------:|--------------------|----------------------------------|
| A5' | 0.9557 | β(G) ≤ β(G/e) for non-bridge non-wrap e | **Lipschitz** `\|β(G) − β(G/e)\| ≤ 1` |
| A6' | 0.9557 | β(G) ≤ β(G/switched(e)) | same Lipschitz bound |
| A5''(reverse) | 0.7555 | β(G/e) ≤ β(G) | FAIL — contraction has NO one-sided monotonicity |

**Minimal CE repository:**
- A5': G = K₄ − (2,3), W = star at 0, e = (1,2) → β_G=1, β_{G/e}=0.
- A5''(rev): G = K₃, W = {(0,1)}, e = (0,2) → β_G=0, β_{G/e}=1.

## Filtered (landed in Lean; Stage-2 sanity-verified only)

| claim | Lean name | spot-check at n=6 |
|-------|-----------|---|
| G15 `dim ker L_sig = β` | `signedLaplacian_kernel_dim_general` (L8:53) | 3727/3727 exact |
| G16 `rank L_sig = \|V\| − β` | rephrase of G15 | subsumed |
| B9 `dim ker L_möb = #comps + β` | `connectionLaplacian_kernel_dim_general` (L8:120) | 3727/3727 exact |
| B21 `tr sign(L_sig) = n − β` | PSD + G15 (L13) | 3727/3727 exact |
| L15 `β(G) ≤ β(G−e)` | `numBalancedComponents_monotone_remove_nonwrap_nonbridge` (L15:254–288) | 183,204/183,204 exact |

## Stage-3 PROVER-A directive

Land **M6** first (highest leverage; collapses 7 Tier-5 corollaries). Target file: `ConnectionLaplacian/L16_SpectrumUnion.lean`. Proof recipe:

1. Build the fibre-Hadamard rotation `U : (V × Fin 2) → (V × Fin 2)` with `U (v, 0) = (e_v ⊗ (e_0 + e_1)/√2)`, `U (v, 1) = (e_v ⊗ (e_0 − e_1)/√2)`.
2. Verify `U U^T = I` (Mathlib `Matrix.IsOrthogonal`).
3. Compute `U^T L_möb U` block-by-block; the (+,+) block equals `L_s`, the (−,−) block equals `L_sig`, off-diagonal blocks vanish (wrap-edge case split).
4. Conclude `spec(L_möb) = spec(L_s) ⊎ spec(L_sig)` via `Matrix.spectrum_blockDiagonal` (or `PiLp` eigenvalue decomposition in Mathlib).
5. M7 as immediate corollary: `det(xI − L_möb) = det(xI − L_s) · det(xI − L_sig)`.

**Estimated LOC:** ~150 for M6, ~30 additional for M7. **Budget:** ~30 min in agent wall-time.

**Secondary target if M6 stalls:** **B2** mixed-trace identity (~5 LOC, no spectrum). Failsafe if M6 requires Mathlib machinery not yet in scope.

## Net novelty scorecard

- **NEW Stage-2 promotion:** L15-rev (edge-deletion reverse-Lipschitz) — not in Stage-1 sheaves.
- **NEW refinement forwarded:** A5-Lip contraction-Lipschitz — replaces Stage-1's A5'/A6' conjectures.
- **Refuted:** Stage-1 one-sided contraction monotonicity (both directions).
- **Sharpened:** B14 bound is tight at 2.0 (Lean statement must allow equality).

## Zero conflicts

The three sheaves produced no contradictions. Overlap claims (G12 ≡ M2 ≡ A13's γ-lift) all pass identically. Stage 2 closed. Fiber-2 ready for consumption by Stage 3 PROVER-A.
