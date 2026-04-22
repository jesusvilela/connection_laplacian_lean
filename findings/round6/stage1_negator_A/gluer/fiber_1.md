# R6 Stage 1 gluer — fiber-1 manifest

**Date:** 2026-04-22. **Upstream:** sheaves α (14 claims), β (21), γ (21) = 56 raw claims. **Downstream:** fiber-1 feeds Stage 2 FUZZER-A and Stages 3/7 PROVER-A/B.

## Gluing discipline

1. **Deduplicate across sheaves.** Where two tiles described the same theorem from different angles, merge into a single entry with both provenances.
2. **Filter out R5 landings.** Silently drop claims that are restatements of already-landed Lean theorems.
3. **Rank by (novelty × leverage × ease).** Highest-leverage master lemmas first; their corollaries flagged as "downstream-of-X".
4. **Cross-sheaf boundary claims get a compound tag** (e.g. `β∩γ`) so provers know they need machinery from both sides.

## Landings that shadow fuzz claims (filter-out)

| fuzz claim | Lean name | file:line |
|---|---|---|
| G15 `dim ker L_sig = β` | `signedLaplacian_kernel_dim_general` | L8_Recognition.lean:53 |
| G16 `rank L_sig = \|V\| − β` | rank-nullity rephrasing of G15 | — |
| B9 `dim ker L_möb = #comps + β` | `connectionLaplacian_kernel_dim_general` (mobius=true) | L8_Recognition.lean:120 |
| B21 `tr sign(L_sig) = n − β` | G15 + L13 PSD | — |
| R4 C1 (spec multiset-union) in R4 INTEGRATION | already-redundant flag in R4 | — |

## Inter-sheaf merges

| merged entry | α source | β source | γ source | tag |
|---|---|---|---|---|
| **M1** kernel-support ↔ ε-partition | — | B11 (supp(ker L_sig) = bal comps) | G20 (ker L_sig ↔ ε-partition) | β∩γ |
| **M2** β is switching-invariant | A13 | — | G2, G12 | α∩γ |
| **M3** kernel-dim invariance under switching | — | (subsumed by B7) | G10 | γ (consequence of M6+M2) |
| **M4** kernel support = balanced components | — | B11 | G20 | β∩γ (same as M1) |
| **M5** balance ⇔ every cycle has even wrap-count | (α: equivalent to walk-even at wrap) | — | G3, G11 | γ, witnessed by L12 `isBalanced_iff_closedWalk_wrap_even` |

## Fiber-1 manifest — merged τ=1 claim set for Stage 2

### Tier 1 — master lemmas (highest leverage)

| id | claim | sheaf | implies |
|---|---|---|---|
| **M6** | `spec(L_möb) = spec(L_s) ⊎ spec(L_sig)` (multiset union) | β (B7) | B1, B6, B12, B13, B17, B19, G10 |
| **M7** | `p_{L_möb}(x) = p_{L_s}(x) · p_{L_sig}(x)` (charpoly) | β (B18) | polynomial-level form of M6 |
| **M1** | kernel-support = balanced components, ε-basis explicit | β∩γ (B11 ≡ G20) | strengthens R5 R13 |

### Tier 2 — γ cornerstones (cohomology / counting)

| id | claim | supports |
|---|---|---|
| **G1**  | #switching classes(G) = 2^{β₁(G)} | 49 |
| **G4**  | switching-class → (cycle-basis parities) is a bijection | 29 |
| **G5**  | #ε witnessing balance = 2^{#π₀} if all balanced, else 0 | 3453+3837 |
| **G13** | #coboundaries = 2^{\|V\|−#π₀} | 49 |
| **G18** | #switching-classes = ∏ᵢ 2^{β₁(Cᵢ)} | 15 |
| **G21** | #coboundaries · #switching-classes = 2^{\|E\|} | 15 |
| **M2**  | β switching-invariant (A13 ≡ G2 ≡ G12) | 132264 |
| **G14** | Euler χ: `\|V\| − \|E\| = #π₀(G) − β₁(G)` | 122 |

### Tier 3 — γ gluing calculus

| id | claim | tag |
|---|---|---|
| **G8**  | bridge-gluing: (G₁ ⊔ G₂ + bridge, W) balanced ⇔ each side balanced | α∩γ |
| **G9**  | vertex-id-gluing: balanced ⇔ both sides balanced | α∩γ |
| **G6**  | bal_radius(G,W) = min_S \|W △ δS\| (definitional) | γ |
| **G7**  | max_W bal_radius(G,W) ≤ ⌈\|E\|/2\| | γ |
| **G19** | bipartite G: bal_radius ≤ min(\|W\|, \|E\|−\|W\|) | γ |
| **G17** | switching-class separator ≥ 1 | γ (trivial) |

### Tier 4 — α edge operations (novel)

| id | claim | subsumes |
|---|---|---|
| **A8**  | parity-matching k-subdivision preserves β, k ∈ {2,3} | R5 R6, R5 R7, A7 |
| **A12** | theta-replacement of non-wrap edge preserves β | α∩γ |
| **A2**  | adding pendant non-wrap edge preserves β | — |
| **A3**  | adding pendant wrap edge preserves β | A2 ∘ M2 |
| **A10** | add-edge commutativity | (trivial) |

### Tier 5 — β higher-order identities

| id | claim |
|---|---|
| **B1**  | `tr(L_möb^k) = tr(L_s^k) + tr(L_sig^k)` for k ∈ {5,6,7,8} (M6 corollary) |
| **B2**  | `tr(L_s · L_sig) = Σ deg² + 2m − 4\|W\|` |
| **B4**  | Perron trace monotonicity for L_sig |
| **B14** | single-flip Weyl stability |
| **B15** | multi-edge interlacing (generalises R5 R17) |
| **B16** | connected ∧ β=0 ⇒ λ_min(L_sig) > 0 |
| **B17** | `‖L_möb‖_F² = ‖L_s‖_F² + ‖L_sig‖_F²` (M6 corollary) |
| **B20** | `tr L_möb = 4\|E\|` (M6 corollary; not in L9) |

### Tier 6 — α/β one-sided near-misses (to fuzz as inequalities)

| id | refined claim | provenance |
|---|---|---|
| **A5'** | β(G) ≤ β(G/e) for non-bridge non-wrap e (contraction mirror of L15) | α, α∩β via Cauchy |
| **A6'** | β(G) ≤ β(G/switched(e)) for wrap e | α, α∩γ |

## Stage-2 FUZZER-A directive

FUZZER-A should test, in order of priority:

1. **M6 / M7 at n=6 exhaustive and n=7 sampled** with high-precision arithmetic (`mpmath` prec=50). Max rel diff target: < 1e-10 at n=6, < 1e-7 at n=7.
2. **Tier-2 γ counting claims at n=6 exhaustive** (G1/G4/G5/G13/G14/G18/G21) — confirm the exact integer counts.
3. **Tier-4 α claims at n=6 including wrap-coverage** (A2/A3/A8/A12).
4. **Tier-6 one-sided inequalities at n=5 exhaustive + n=6 sample** — if τ=1, promote to R7 prover-queue.
5. **Spot-check** the filtered-out G15/B9 claims to re-verify the existing Lean landings still hold numerically at n=6 (sanity).

Stage-2 budget: ~20 min.

## Net-novel R7 prover queue (ranked)

1. **M6** — spec-union (master); collapses ≥ 6 Tier-5 claims.
2. **M7** — charpoly product (polynomial shadow of M6).
3. **M1** — kernel-support = balanced comps with explicit ε-basis (β∩γ bridge).
4. **M2** — β switching-invariance (cornerstone for switching-equivalence story).
5. **G1/G4/G13/G18/G21** — switching-class counting bundle.
6. **A8** — unified parity-subdivision.
7. **G3/G11** — cycle-parity characterisation (near-trivial via L12).
8. **A12** — theta-replacement.
9. **B2** — mixed-trace identity (~5 LOC).
10. **G6/G7/G19** — balance-radius bundle.
11. **B14/B15/B16** — eigenvalue-stability bundle.
12. **A5'/A6'** — contraction-monotonicity companions to L15.

## Zero conflicts

No two sheaves produced contradictory verdicts. The single "same-theorem-two-angles" case (M1 = B11 ≡ G20) merges cleanly. R5 landings shadow G15, G16, B9, B21 (redundant, not conflicting).

Stage 1 closed. Fiber-1 ready for consumption by Stage 2.
