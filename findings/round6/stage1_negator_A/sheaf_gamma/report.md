# NEGATOR-A R6 — Sheaf-section γ (cohomology / balance)

**Date:** 2026-04-22. **Envelope:** exhaustive iso-classes on n ∈ {3,4,5} × exhaustive wrap subsets (primary); sampled n=6 pass for 7 of the cheaper claims.

## Summary table — all 21 claims at τ = 1.0000

| idx | claim | precondition | supp/total |
|-----|-------|--------------|------------|
| G1  | #switching classes on G = 2^{β₁(G)} | any G | 49/49 (per-graph) |
| G2  | parity of \|W ∩ γ\| on each cycle γ is switching-invariant | any G, W, S | 4736/4736 |
| G3  | G balanced ⇔ every cycle γ has \|W ∩ γ\| even | G connected (n≤4 cycle-enum cap) | 156/156 |
| G4  | switching-class → (parities on cycle-basis) is a bijection | G connected | 29/29 (per-graph) |
| G5  | #ε witnessing balance = 2^{#π₀} if all comps balanced, else 0 | any G, W | 3453/3453 (n≤5) + 3837/3837 (n=6) |
| G6  | bal_radius(G,W) = min_S \|W △ δ(S)\| | any G, \|E\|≤6 | 178/178 |
| G7  | max_W bal_radius(G,W) ≤ ⌈\|E\|/2⌉ | connected G | 156/156 |
| G8  | bridge-gluing: (G1 ⊔ G2 + bridge, W) balanced ⇔ each side balanced | G1, G2 arbitrary | 288/288 |
| G9  | vertex-identification gluing: balanced ⇔ both sides balanced | identify v1∈G1 with v2∈G2 | 108/108 |
| G10 | kernel_dim(L_möb) is a switching invariant | any G, W, S | 1231/1231 |
| G11 | W is a coboundary ⇔ every cycle γ has \|W ∩ γ\| even | any G (n≤4 cycle-enum cap) | 178/178 |
| G12 | β(G,W) = β(G, W △ δ(S)) | any G, W, S | 107528/107528 + 119176/119176 (n=6) |
| G13 | #coboundaries = 2^{\|V\|−#π₀}; #switching-classes = 2^{β₁(G)} | any G | 49/49 (per-graph) |
| G14 | \|V\| − \|E\| = #π₀(G) − β₁(G) | any G | 49/49 + 73/73 (n=6) |
| G15 | dim ker(L_signed(G,W)) = β(G,W) | any G, W | 3453/3453 + 3794/3794 (n=6) |
| G16 | rank(L_signed(G,W)) = \|V\| − β(G,W) | any G, W | 3453/3453 + 3825/3825 (n=6) |
| G17 | distinct switching-classes have min_S \|W △ W' △ δ(S)\| ≥ 1 | trivial separator | 413/413 |
| G18 | #switching classes(G) = ∏_i 2^{β₁(C_i)} | any G | 15/15 (per-graph) |
| G19 | bipartite G: bal_radius(G,W) ≤ min(\|W\|, \|E\|−\|W\|) | G bipartite | 50/50 |
| G20 | ker(L_signed) on balanced connected G matches ε-partition | G connected, balanced | 392/392 |
| G21 | #coboundaries · #switching-classes = 2^{\|E\|} | any G | 15/15 (per-graph) |

## Scoreboard

- **21 NEW γ-claims, all τ = 1.0000.** Exceeds the 10+ requirement by 2×. No counterexamples, no refinements needed.
- Orthogonal to R5 γ-tile: none restates R4, R13, R15, R16, R20, R21, R22.
- New territory: switching-equivalence lattice (G1/G4/G13/G18/G21), structural switching-invariance (G2/G10/G12), cycle-parity characterisation (G3/G11), ε-multiplicity (G5), balance-radius as coboundary distance (G6/G7/G19), gluing calculus (G8/G9), signed-Laplacian rank/kernel (G15/G16), γ∩β bridge (G20).
- Strongest support: **G12** at 226,704 combined confirmations of `β(G,W) = β(G, W △ δS)`.

## R7 prover-candidate triage (by ease × leverage)

### Definitional / book-chapter-1

- **G14** — Euler characteristic. Mathlib likely one-liner (`SimpleGraph.edgeFinset` + component count).
- **G17** — trivial separator once switching-quotient is formalised.
- **G21** — short exact sequence of Z/2 cochain complex; corollary of G13.

### Core algebra (highest leverage)

- **G15** (`dim ker L_signed = β`) and **G16** (`rank = |V| − β`) — the canonical identities the paper implicitly uses; formalising G15 would tighten `L8_Recognition.lean` directly.
- **G13** / **G18** — rank-nullity for δ: Z/2^V → Z/2^E. Prerequisite for G1.
- **G1** / **G4** — explicit bijection switching-classes ↔ H¹(G; Z/2).

### Structural invariance

- **G12** — workhorse (largest support); provable via "β only sees cycle parity" + G3.
- **G10** — follows from Kronecker-conjugation pattern (MEMORY on `laplacian_decomposes`): switching by S = block-diagonal sign conjugation, preserves spectrum.
- **G20** — direct consequence of G15 + R13 (R5 ±1 basis); slots into `L8_Recognition.lean` as corollary.

### Cycle-parity (Harary/Zaslavsky cornerstones)

- **G3** / **G11** — almost certainly provable with existing `walkWrapCount` / cycle-basis in `L14_CycleEw.lean`.

### Balance-radius / metric

- **G6** definitional; **G19** bipartite-specific; **G7** general bound. Complements R5 R16.

## Claims in τ ∈ [0.5, 0.95] or < 0.1

**None** in either band. No refinement or counterexample needed.

## Sheaf-boundary section

### γ ∩ α (balance × edge-ops)

- **G8** (bridge-gluing) and **G9** (vertex-identification-gluing): α idiom, γ content.
- **G19** (bal_radius in bipartite): metric on edge-subsets (α) living on the coboundary lattice (γ).

### γ ∩ β (balance × spectrum)

- **G10** (kernel_dim(L_möb) switching-invariant): β-companion is stronger "spectrum of L_möb is switching-invariant". Flag for merge with β-tile.
- **G15** (`dim ker L_signed = β`) and **G16** (`rank = |V| − β`): prototypical γ ∩ β bridges.
- **G20** (ker L_signed vectors ↔ ε-colorings): quintessential γ ∩ β glue. **Recommend gluer merge G20 with β's Fiedler / kernel-eigenvector work — same theorem from two sides.**

### No γ ∩ α ∩ β triple claims.
