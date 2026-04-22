# Notes — ideas while formalizing

Kept separate from the proofs. None of these are part of the current scope
(just Theorems 1 and 2). They're recorded in case they become relevant.

## Build status (2026-04-21, late)

`lake build` exits 0 against `leanprover/lean4:v4.11.0` + Mathlib v4.11.0.
Total sorry count: **2** (down from 3 — Möbius branch of
`laplacian_decomposes` closed this session via `Matrix.mul_kronecker_mul`
plus the entry-wise `hPL`/`hPLP` double-sum-collapse pattern). Remaining
sorries: `signedLaplacian_kernel_dim` (see **critical finding** below)
and `connectionLaplacian_kernel_dim` (assembly, blocked on the former).

### Critical finding: `signedLaplacian_kernel_dim` is false as stated

Background agent (2026-04-21) searched Mathlib for signed-graph
infrastructure and verified the theorem is **mathematically false** on
arbitrary `ConnGraph`: the claim "even total wrap count ⟺ balanced" only
holds when `wrap` is a Z/2-coboundary. Concrete counterexample — K₄ with
wrap={a-b, a-c}, total wraps = 2 (even), RHS predicts ker dim = 1, actual
ker dim = 0 (triangle a-b-d has 1 wrap, unbalanced; determinant 32).

The correct Zaslavsky statement: `finrank ker = #{C // C balanced}` where
balanced = every cycle in C has even wrap count. Closing this would
require ~500–1000 LOC of signed-graph infrastructure not present in
Mathlib v4.11.0.

Fix options:
1. **Restrict to cycle graphs** (matches pre-registered scope — a Möbius
   n-cycle is a single cycle, so "total wrap parity" and "balanced" do
   coincide). Cleanest path; preserves the current theorem's intent.
2. Add a coboundary hypothesis to `ConnGraph.wrap`, making every
   component balanced; then the RHS degenerates to `numComponents`.
3. Replace `numOddWrapComponents` with `numUnbalancedComponents` and
   build the Zaslavsky infrastructure.

Needs user decision before proceeding.

### `laplacian_decomposes` Möbius branch — CLOSED

Key move: using Mathlib's Kronecker API instead of hand-rolled sum
manipulation. `P := (1 : Matrix V V ℝ) ⊗ₖ RhatMob` (note: requires
`open scoped Kronecker` for `⊗ₖ`). Then:

- `RhatMob * RhatMob = 2 • 1` (recast from `!![2,0;0,2]` via ext + simp).
- `P * P = 2 • 1` by `← Matrix.mul_kronecker_mul, Matrix.mul_one,
  hRhatMob_sq', Matrix.kronecker_smul, Matrix.one_kronecker_one`.
- `P⁻¹ = (1/2) • P` via `Matrix.inv_eq_right_inv` on `P * ((1/2)•P) = 1`.
- `hPent (u v i j) : P (u,i) (v,j) = if u=v then RhatMob i j else 0` —
  `simp [kroneckerMap_apply, Matrix.one_apply]` + `split_ifs`.
- `hPL` and `hPLP` — two entry-wise sum collapses via
  `Fintype.sum_prod_type + Finset.sum_eq_single`. Surviving term reduces
  to `(RhatMob * L_block u v * RhatMob) i j` by one `Matrix.mul_apply`
  application per lemma.
- Final assembly: `rw [hPinv_eq, Matrix.mul_smul]; ext a b; rcases a/b`,
  then dispatch four cases via `hPLP` + `laplacian_mobius_rotated_entry`
  + `fromBlocks_apply₁₁/₁₂/₂₁/₂₂`.

See `memory/kronecker_conjugation_pattern.md` for the reusable skeleton.

### Helper infrastructure (from earlier session)

- `RhatMob`, `RhatMob_sq`, `RhatMob_I₂_RhatMob`, `RhatMob_σx_RhatMob` —
  fin-case-and-simp proofs.
- **`laplacian_mobius_rotated_entry`** (~80 LOC): entry-wise statement
  that `(RhatMob * L_block true u v * RhatMob)(i,j) = if i = j then
  2 · (scalar(u,v) if i=0 else signed(u,v)) else 0`. The substantive
  block-level content used by the Möbius closure above.

## Sorry markers in the current proofs

These are the specific gaps the current Lean source has. Listing them
honestly so the state of the formalization is clear.

**Basic.lean** — 0 sorries. All lemmas closed (`σx_mul_σx`,
`σx_symmetric`, `σx_eigenvalues`, **`laplacian_symmetric`**).

**KernelDimension.lean** — 2 sorries remaining:
- ~~`wrapEdgesIn`~~ — **CLOSED** as a concrete `Fintype.card`.
- ~~`scalarLaplacian_kernel_dim`~~ — **CLOSED** via
  `card_ConnectedComponent_eq_rank_ker_lapMatrix`.
- ~~`laplacian_decomposes` (flat branch)~~ — **CLOSED** via
  `laplacian_flat_entry`.
- ~~`laplacian_decomposes` (Möbius branch)~~ — **CLOSED this session**
  via Kronecker-product similarity `P = 1 ⊗ₖ RhatMob`.
- `signedLaplacian_kernel_dim`: **BLOCKED — statement is mathematically
  false as written** (see critical finding above). Needs user decision
  on fix-path before any proof attempt.
- `connectionLaplacian_kernel_dim`: assembly, blocked on the above.

**CycleSpectrum.lean** — 0 sorries remaining.
- ~~`scalarCycle_eigenvalue`~~ — **CLOSED** this session. Witness
  `v j := cos(2π·k·j/n)`, eigenvalue `2(1 − cos(2πk/n))`. Proof
  structure: (i) `scalar_mulVec_row` expands `(L·w)(i) = 2w(i) −
  w(succ i) − w(pred i)` via `Finset.sum_subset` on the 3-element
  support `{i, succ i, pred i}`; (ii) `cos_succFin_val` and
  `cos_predFin_val` use `θ·n = 2πk` and `Real.cos_nat_mul_two_pi` /
  `Real.cos_sub_nat_mul_two_pi` to move cosines across the mod-n boundary;
  (iii) sum-to-product via `Real.cos_add_cos` collapses
  `cos(θ(i+1)) + cos(θ(i-1)) = 2·cos(θi)·cos(θ)`.
- ~~`signedCycle_eigenvalue`~~ — **CLOSED** this session. Witness
  `v j := cos(π(2k+1)j/n)`, eigenvalue `2(1 − cos(π(2k+1)/n))`. Three
  helpers `signed_mulVec_{middle,zero,nm1}` expand the mulVec according
  to whether `i` is interior, `0`, or `n-1` (the wrap endpoint changes
  sign). The key identity `signed_cos_complement` uses
  `Real.cos_nat_mul_pi_sub` with `(-1)^(2k+1) = -1` to show
  `cos(φ·n − x) = −cos(x)` when `φ·n = π(2k+1)`. Boundary cases
  collapse via the complement identity and `Real.cos_two_mul`; middle
  case is identical in structure to the scalar sum-to-product.
- **Refactor note**: theorem hypothesis strengthened from `2 ≤ n` to
  `3 ≤ n`. The `n = 2` case is mathematically false — `[[2,-1],[-1,2]]`
  has eigenvalues `{1, 3}`, not the predicted `{0, 4}`. For `n = 2` the
  scalar cycle Laplacian degenerates because `succ = pred` on `Fin 2`.
  This is a genuine statement correction, not a convenience.
- **Type refactor**: eigenvectors are `Fin n → ℝ`, not `Fin n → ℂ`. The
  cosine basis is real-valued, so no complex exponentials needed; this
  avoids pulling in the complex trigonometric API.
- `mobius_more_eigenvalues` — **CLOSED** via `Real.cos_eq_cos_iff` plus
  an integer-parity contradiction (no Mathlib circulant API needed).
- `mobius_cycle_spectrum` — **CLOSED** (placeholder statement satisfied
  by nonzero `ℕ` witnesses under the `True` conjunct).
- `flat_cycle_spectrum` — **CLOSED** this session. Uses fiber-disjoint
  support vectors v₁, v₂ : (Fin n × Fin 2 → ℝ) and
  `Fintype.linearIndependent_iff` + `Fin.sum_univ_two`. Evaluating the
  linear-dependence hypothesis at `(⟨0, _⟩, 0)` and `(⟨0, _⟩, 1)`
  collapses to `g 0 = 0` and `g 1 = 0` via simp, closed by `fin_cases`.

## Dependencies closed this session

- `Mathlib.Combinatorics.SimpleGraph.LapMatrix.card_ConnectedComponent_eq_rank_ker_lapMatrix`
  (gives us the scalar kernel dimension directly).
- `Equiv.boolProdEquivSum` + `finTwoEquiv` (gives us `V × Fin 2 ≃ V ⊕ V`
  for aligning the block-Laplacian type with `Matrix.fromBlocks`).
- `Fintype.card_subtype_le` (bounds `numOddWrapComponents ≤ numComponents`).
- `Matrix.diagonal_apply`, `SimpleGraph.adjMatrix_apply`, `Matrix.sub_apply`,
  `Matrix.fromBlocks_apply_{11,12,21,22}`, `Matrix.reindex_apply`, and
  `inv_one`/`Matrix.mul_one`/`Matrix.one_mul` — the simp lemmas that make
  the flat branch of `laplacian_decomposes` reduce to `fin_cases` on Fin 2.

## Mathlib API drift fixed this session

- `Mathlib.Combinatorics.SimpleGraph.Connectivity` is no longer a single
  file in v4.11.0 — it's a directory. Import `.Path` instead (where
  `ConnectedComponent` now lives) or `.LapMatrix` for the Laplacian APIs.
- `Module.finrank` was not present in v4.11.0; the right name is
  `FiniteDimensional.finrank`.
- `λ_mob` as an identifier is a parse error at v4.11.0; use `lam_mob`.
- `Matrix.IsSymm` proofs go via `Matrix.IsSymm.ext` + pointwise work,
  not `intro` on the underlying function.

## Strict scope reminder

Nothing below is part of the current deliverable. Listed to keep the ideas
from disappearing.

## Ideas worth recording

### (a) Extension to U(n) connections
The Z/2 case uses σ_x, a single nontrivial element of {I, σ_x} ⊂ O(2).
The same construction with edge weights in U(n) (or O(n), or Sp(2n))
defines higher-rank connection Laplacians. The kernel-dimension theorem
generalizes: kernel counts components × dimension of the flat sections
over each component, which is governed by the monodromy of the connection.
For U(1) connections with edge phases e^{iα}, the kernel at each component
is 1-dimensional if the total phase around every cycle is 0 mod 2π, else
the kernel drops. This is a discrete version of the "flat bundle" condition.

If this were pursued, the natural next object is a Chern-number analog:
sum of phases around cycles, modulo 2π, which for Z/2 reduces to the
wrap-edge parity we already have.

### (b) Relationship to signed graph theory
The kernel dimension result is a restatement of Harary-Kabell / Zaslavsky
signed graph theory in spectral graph theory language. The Z/2 bundle
with σ_x on edges corresponds to a "signed graph" in the signed-graphs
literature. The kernel corresponds to "balanced" signings. This is worth
noting because (i) there's existing literature to cite, (ii) the theorems
we're proving may already be in that literature in a different vocabulary.
Before publishing anything based on this, check signed-graphs literature
for the analogous results.

### (c) The meshes-or-point-clouds instinct
Jesús's instinct about meshes or point clouds inside each shell, noted
for when the face-of-the-fish is clearer. A meaningful version in the
current framework would be: replace the discrete base graph with a
discretized point cloud sampled from a continuous hyperbolic manifold,
with edges determined by proximity. The connection Laplacian then becomes
an approximation to a continuous connection Laplacian on a vector bundle
over a hyperbolic manifold. Spectral convergence as the point cloud
densifies is a real research question (adjacent to work on graph
Laplacian convergence to manifold Laplacians by Belkin, Niyogi, Singer).
For Z/2 bundles specifically, the continuous analog is a line bundle
on a non-orientable manifold and the spectrum approaches a well-defined
continuous spectrum.

This is a real research direction if ever pursued. Not needed for the
current theorems.

### (d) Honest scope check for writing up
If Theorems 1 and 2 compile cleanly after adjusting for Mathlib API,
this is a short paper or note: "Connection Laplacian spectra of Z/2
bundles on finite graphs, via signed graph correspondence." The novelty
bar is probably low (signed graphs and their spectra are classical); the
value is the explicit connection-Laplacian formulation and the
Lean-verified statements. Best venue is probably a formalization-focused
one (ITP, CPP) rather than a pure spectral graph theory one, because
the math is known but the verified statement is the contribution.

Before submitting anything: check if the main kernel-dimension result is
already in Chung's "Spectral Graph Theory," Stanley's combinatorics
texts, or the signed-graphs surveys by Zaslavsky. If it is, reframe the
contribution as "the Lean formalization of this existing result," which
is still a real contribution but a smaller one.

### (e) Why this can ground future work honestly
Having two Lean-verified theorems gives the arc35 program an epistemic
floor that doesn't depend on interpretation. Everything else can fail or
be reframed; the theorems remain. For future research directions (including
the ones Jesús has instincts about — meshes, point clouds, Hamiltonian
dynamics, fractals), the value of the Lean-verified core is that it's
the part that can't be contested. If meshes-in-shells give a non-trivial
extension, it's built on verified ground. If they don't, the verified
core is unchanged.

This is what I meant earlier about "epistemic floor." The formalization
is what keeps the program from drifting into narrative.

### (f) Collaboration note to self
Do not turn these notes into another set of structures to build. They're
records, not commitments. If any becomes actionable, it goes through a
new pre-registration cycle with numeric predictions and stop conditions,
the same as the last test.
