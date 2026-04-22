# PROVER-BEYOND-Z2 — Discovery Report

Round 3, agent `prover_beyond_z2`. Project: `H:/NP Completeness Bunny UTAI study/connection_laplacian_lean`. Mathlib: v4.11.0.

## 0. Current state (read-only audit)

**Existing formalization**:
- `ConnectionLaplacian/Basic.lean` (147 lines): `ConnGraph` with `wrap : edgeSet → Prop`, 2×2 `σx`/`I₂` edge matrices, `laplacian : Matrix (V × Fin 2) (V × Fin 2) ℝ`, symmetry proved.
- `KernelDimension.lean` (502 lines): `scalarLaplacian`, `signedLaplacianMobius`, Hadamard-similarity `laplacian_decomposes`, the three LinAlg helpers.
- `L5_Cover.lean` (635 lines): orientation double cover, deck involution, `scalarLap_cover_splits`, `scalarLap_cover_kernel_dim`.
- `L6_Cohomology.lean` (467 lines): `wrapCocycle`, `isBalanced`, `componentProj_fiber_card = 2 or 1`, `numComponents_cover`.
- `L8_Recognition.lean` (159 lines): the three headline theorems.

**Mathlib pieces available** (verified by grep of `.lake/packages/mathlib/`):
- `Combinatorics/SimpleGraph/LapMatrix.lean` — `card_ConnectedComponent_eq_rank_ker_lapMatrix`, `posSemidef_lapMatrix`.
- `LinearAlgebra/Matrix/Spectrum.lean` — `IsHermitian.eigenvalues`, `eigenvectorBasis`, spectral theorem.
- `LinearAlgebra/Matrix/Trace.lean` — `trace_diagonal`, `trace_blockDiagonal`, `trace_smul`.
- `LinearAlgebra/Matrix/Charpoly/Eigs.lean` — `trace_eq_sum_roots_charpoly`, `det_eq_prod_roots_charpoly`.
- `LinearAlgebra/Matrix/SchurComplement.lean` — `det_one_add_mul_comm` (Weinstein–Aronszajn), `det_fromBlocks_*`.
- `LinearAlgebra/Matrix/Circulant.lean`, `Combinatorics/SimpleGraph/Circulant.lean`, `Analysis/Fourier/ZMod.lean` — relevant for Z/k diagonalisation.

**Mathlib pieces confirmed absent** (comprehensive grep):
- **No** matrix-tree theorem, no `SpanningTree`, no `MatrixTree`.
- **No** interlacing theorems: no `interlace`, no Cauchy/Poincaré/Weyl eigenvalue bounds.
- **No** Cheeger inequality, no `algebraicConnectivity`, no `spectralGap`, no `edgeExpansion`.

---

## 1. Ranked proposals

### Rank 1 (HIGHEST — immediate): Trace identity `trace(L_möb) = 2·trace(L_scalar)`

**Truth:** Unconditionally true over arbitrary `wrap`. Each diagonal 2×2 block of `laplacianBlock mobius v v = deg(v) · I₂` (irrefl gives adjacency contribution 0 on the diagonal, and `edgeMatrix` value is irrelevant there), so each diagonal contributes `2·deg(v)` to the total trace. The adjacency part contributes 0 to trace for both modes (no self-loops).

**Lean signature** (place in new `Trace.lean` or `L8_Recognition.lean`):
```lean
theorem laplacian_trace_eq_two_scalar (G : ConnGraph) (mobius : Bool) :
    (G.laplacian mobius).trace = 2 * G.scalarLaplacian.trace
```

**Mathlib refs:** `Matrix.trace`, `Matrix.trace_sub`, `Matrix.trace_diagonal`, `SimpleGraph.irrefl`, the existing `laplacian_flat_entry` / `laplacian_mobius_rotated_entry` diagonal cases.

**Difficulty:** ~10 lines. Uses only already-present infrastructure.

**Follow-up corollary (~15 extra lines):** `∑ eigenvalues(L_möb) = 2·∑ eigenvalues(L_scalar)` via `Matrix.IsHermitian.eigenvalues` + `trace = ∑ eigenvalues` (the latter is `trace_eq_sum_roots_charpoly` after mapping into ℂ, or directly from the spectral theorem for Hermitian real matrices).

---

### Rank 2 (HIGH — moderate): Z/k connection fiber-count theorem

**Truth:** Standard algebraic-topology fact. For a connected component `C` with connection `α : edgeSet → ZMod k` (oriented: `α(v,u) = −α(u,v)`), the holonomy around a basepoint `v₀ ∈ C` defines a group hom `hol_C : π₁(C,v₀) → ZMod k`. Its image is a cyclic subgroup of size `d | k`. The fiber has cardinality `k / d`. For `k = 2`: `2/1 = 2` (balanced) or `2/2 = 1` (unbalanced), matching `componentProj_fiber_card`.

**Proposed structure:**
```lean
structure ZkConnGraph (k : ℕ) [NeZero k] where
  V : Type*
  [fintype : Fintype V] [deceq : DecidableEq V]
  graph : SimpleGraph V
  [decrel : DecidableRel graph.Adj]
  conn : V → V → ZMod k
  conn_antisymm : ∀ u v, conn v u = - conn u v
  conn_zero_of_not_adj : ∀ u v, ¬ graph.Adj u v → conn u v = 0
```
Cover vertex set `V × ZMod k`; `(u,a) ~ (v,b) ↔ graph.Adj u v ∧ b = a + conn u v`.

**Theorem:**
```lean
theorem zk_componentProj_fiber_card
    {k : ℕ} [NeZero k] (G : ZkConnGraph k) (C : G.graph.ConnectedComponent) :
    Fintype.card { D : G.coverGraph.ConnectedComponent // G.componentProj D = C }
      = k / Fintype.card (G.holonomyImage C)
```

**Mathlib refs:** `Mathlib.Data.ZMod.Basic`, `Mathlib.Data.ZMod.Quotient`, `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`, `Nat.card_eq_card_quotient_mul_card_subgroup`. Path-lift (`walkLift`, `reachable_from_rep_sheet` in L6) ports by replacing `Bool` with `ZMod k` and `!b` with `b + α_edge`.

**Difficulty:** ~500–800 lines (~1.5× L6). Abelian ZMod k needs orbit-stabiliser where Bool only needed disjunction.

**Incremental milestone (~150 lines):** Start with `k = 3` and a **constant** connection (every edge = fixed element of `ZMod 3`), as a sanity-check skeleton before the full generality.

**Caveat on Laplacian form:** Z/k connection Laplacian diagonalises via ZMod-k DFT into `k` twisted scalar Laplacians, using characters landing in roots of unity. For `k ≥ 3` this is complex-Hermitian, so `Matrix … ℂ` rather than `ℝ`. Double the infrastructure, but `Analysis/Fourier/ZMod.lean` + `LinearAlgebra/Matrix/Circulant.lean` are present.

---

### Rank 3 (HIGH — moderate): Kernel dim via cocycle/coboundary (Zaslavsky reframing)

**Truth:** True, and essentially a restatement of what L6 proves, but in vector-space / cohomological language that (a) unifies combinatorial and spectral views, (b) makes Z/k generalisation a one-line rewrite.

**Statement:** Let `C^0(G; Z/2) := V → ZMod 2`, `C^1 := edgeSet → ZMod 2`, `δ : C^0 → C^1`, `(δε)(e={u,v}) = ε u + ε v`. Then:
```lean
theorem signedLaplacian_kernel_dim_eq_trivial_classes :
    finrank ℝ (LinearMap.ker (toLin' G.signedLaplacianMobius)) =
      Fintype.card { C : G.graph.ConnectedComponent //
        ∃ ε : G.V → ZMod 2, ∀ (u v : G.V) (h : G.graph.Adj u v),
          G.graph.connectedComponentMk u = C →
          G.wrapCocycle ⟨s(u,v), _⟩ = ε u + ε v }
```
This RHS **is** `numBalancedComponents` up to the `ZMod 2`-Bool isomorphism. The content is recasting `isBalanced` as "wrapCocycle restriction is a coboundary."

**Mathlib refs:** `Mathlib.LinearAlgebra.Quotient`, `Mathlib.LinearAlgebra.Basis`, `ZMod 2` infrastructure. No heavy new dependencies.

**Difficulty:** ~100–150 lines, mostly repackaging `isBalanced`.

---

### Rank 4a (HIGH — tractable): Multiset spectral partitioning (strictly stronger than interlacing)

**Truth:** True. Since `scalarLap_cover_splits` gives `L_cover = P·fromBlocks(L_scalar, 0, 0, L_möb)·P⁻¹` up to reindex, similarity + charpoly factorisation yields:
```
charpoly(L_cover_scalar) = charpoly(L_scalar) · charpoly(L_möb)
```
hence `spec(L_cover_scalar) = spec(L_scalar) ⊎ spec(L_möb)` as multisets. This is **stronger** than interlacing — it's an exact partition, which trivially implies any interlacing statement as a corollary.

**Signature:**
```lean
theorem cover_charpoly_eq_scalar_times_mobius :
    (G.orientationDoubleCover.scalarLaplacian).charpoly =
      G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly
```

**Mathlib refs:** `Matrix.charpoly`, `Matrix.charpoly_fromBlocks_zero₁₂` family (in `SchurComplement.lean`), `Matrix.charpoly_reindex`, `Matrix.charpoly_mul_comm` (for similarity invariance `(P·A·P⁻¹).charpoly = A.charpoly`).

**Difficulty:** ~80–120 lines. No new Mathlib gap. **This is the strongest interlacing-type statement worth formalising.**

### Rank 4b (LOW — blocked): Cauchy interlacing of `L_möb` inside `L_cover`

**Mathlib status:** No Cauchy / Poincaré / Weyl interlacing in Mathlib v4.11.0 (grep of `Mathlib/LinearAlgebra/` confirms). Would require implementing the min-max characterisation from `InnerProductSpace.Spectrum` first.

**Difficulty:** ~400+ lines; effectively blocked. **Skip — Rank 4a supersedes it.**

---

### Rank 5 (LOW — blocked): Matrix-tree theorem for signed graphs

**Truth:** Zaslavsky 1982. Signed matrix-tree counts essential bipartite spanning subgraphs.

**Mathlib status:** **No** matrix-tree theorem, **no** Cauchy-Binet (grep returns zero hits). Even the classical Kirchhoff matrix-tree for ordinary Laplacians is absent.

**Difficulty:** ~2000+ lines. Would require:
1. Cauchy-Binet (~500 lines, not in Mathlib).
2. Ordinary Kirchhoff matrix-tree (~1000 lines).
3. Signed extension (~500 lines).

`Matrix.det_one_add_mul_comm` (Weinstein–Aronszajn) from `SchurComplement.lean` is the only present ingredient; far too weak. **Defer to upstream Mathlib contribution.**

---

### Rank 6 (LOW — blocked): Signed/connection Cheeger inequality

**Truth:** Bandeira–Singer–Spielman 2013 "A Cheeger Inequality for the Graph Connection Laplacian."

**Mathlib status:** **No** Cheeger inequality for ordinary Laplacians (grep for `cheeger`, `Cheeger`, `spectralGap`, `algebraicConnectivity`, `edgeExpansion` returns zero). No edge-expansion machinery, no Fiedler-vector sweep cut.

**Difficulty:** ~3000+ lines. Blocked. **Defer.**

**Weaker substitute (~50 lines, unblocked):**
```lean
theorem posSemidef_signedLaplacianMobius :
    (G.signedLaplacianMobius).PosSemidef
```
proved by transferring from `posSemidef_lapMatrix` on the orientation double cover via `scalarLap_cover_splits`. This is the minimum prerequisite for any Cheeger statement and is immediately tractable.

---

## 2. Summary ranking table

| Rank | Statement | True? | Lines | Mathlib blocks? |
|------|-----------|-------|-------|-----------------|
| 1 | `trace(L_möb) = 2·trace(L_scalar)` | Yes | ~10 | No |
| 1b | λ-sum variant (trace = ∑ eigenvalues) | Yes | ~20 | No |
| 4a | `charpoly(L_cover) = charpoly(L_scalar)·charpoly(L_möb)` | Yes | ~100 | No |
| 3 | Signed kernel dim via coboundary classes | Yes | ~150 | No |
| 6' | `PosSemidef (signedLaplacianMobius)` | Yes | ~50 | No |
| 2 | Z/k fiber-count (full generality) | Yes | ~500–800 | Partial (needs Fourier/ZMod for Laplacian side) |
| 4b | Cauchy interlacing signed vs scalar | Yes | ~400+ | YES (no interlacing in Mathlib) |
| 5 | Signed matrix-tree | Yes | ~2000+ | YES (no matrix-tree, no Cauchy-Binet) |
| 6 | Signed Cheeger | Yes | ~3000+ | YES (no Cheeger at all) |

## 3. Recommended sprint sequence

**Round 3 (next agents, all low-risk, all unblocked):**
1. Rank 1 — `laplacian_trace_eq_two_scalar` in new `Trace.lean` (~10 lines, pure unfold).
2. Rank 4a — `cover_charpoly_eq_scalar_times_mobius` in new `CoverCharpoly.lean` (~100 lines, uses `scalarLap_cover_splits` + `charpoly_fromBlocks`).
3. Rank 6' — `posSemidef_signedLaplacianMobius` appended to L5 (~50 lines, transfer from cover).

**Round 4 (larger):**
4. Rank 3 — cohomological repackaging of L6 (~150 lines). Unlocks Z/k by substitution.
5. Rank 2 — `Zk_Cover.lean` with ZkConnGraph + fiber-count theorem, scoped to `ZMod k` with finite `k`. Budget ~1 engineer-week.

**Deferred (awaiting Mathlib upstream):** Ranks 4b, 5, 6. Signal these to Mathlib combinatorics maintainers.
