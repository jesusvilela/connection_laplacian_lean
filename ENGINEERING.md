# Engineering notes

Mathlib-specific techniques and API pointers accumulated while building the
verified spine. These are working-level notes for anyone extending the library
against Mathlib v4.11.0 — not part of the paper, not part of the theorem
statements.

## Mathlib API drift (v4.11.0)

- `Mathlib.Combinatorics.SimpleGraph.Connectivity` is no longer a single file;
  it is a directory. Import `.Path` (where `ConnectedComponent` now lives) or
  `.LapMatrix` for the Laplacian APIs.
- `Module.finrank` is not present in v4.11.0; the current name is
  `FiniteDimensional.finrank`.
- `λ_mob` is a parse error at v4.11.0; use `lam_mob`.
- `Matrix.IsSymm` proofs proceed via `Matrix.IsSymm.ext` + pointwise work,
  not `intro` on the underlying function.

## Kronecker conjugation pattern (Möbius branch)

The Möbius branch of `laplacian_decomposes` closes via a Kronecker-product
similarity rather than by hand-rolled double-sum manipulation. The pattern is
reusable for any block-diagonal conjugation whose diagonal factor squares to
a scalar.

Setup — with `open scoped Kronecker` so that `⊗ₖ` resolves to
`Matrix.kroneckerMap`:

```
P := (1 : Matrix V V ℝ) ⊗ₖ RhatMob
```

Core rewrites:

- `RhatMob * RhatMob = 2 • 1` — recast from the explicit `!![2,0;0,2]` via
  `Matrix.ext` + `simp`.
- `P * P = 2 • 1` — by
  `← Matrix.mul_kronecker_mul`, `Matrix.mul_one`, `hRhatMob_sq'`,
  `Matrix.kronecker_smul`, `Matrix.one_kronecker_one`.
- `P⁻¹ = (1/2) • P` — via `Matrix.inv_eq_right_inv` on `P * ((1/2) • P) = 1`.

Entry lemma (Kronecker entry form):

```
hPent (u v : V) (i j : Fin 2) :
  P (u, i) (v, j) = if u = v then RhatMob i j else 0
```

Proved by `simp [kroneckerMap_apply, Matrix.one_apply]` followed by
`split_ifs`.

Two entry-wise sum collapses — `hPL` and `hPLP` — reduce to
`(RhatMob * L_block u v * RhatMob) i j` via
`Fintype.sum_prod_type` + `Finset.sum_eq_single`. One `Matrix.mul_apply`
application per lemma finishes the surviving term.

Final assembly:

```
rw [hPinv_eq, Matrix.mul_smul]
ext a b
rcases a with ⟨u, i⟩
rcases b with ⟨v, j⟩
```

Then dispatch four cases via `hPLP` + `laplacian_mobius_rotated_entry` +
`fromBlocks_apply₁₁/₁₂/₂₁/₂₂`.

### Supporting infrastructure

- `RhatMob`, `RhatMob_sq`, `RhatMob_I₂_RhatMob`, `RhatMob_σx_RhatMob` — each
  closed by `fin_cases` + `simp`.
- `laplacian_mobius_rotated_entry` (~80 LOC) is the substantive block-level
  content: entry-wise statement that
  `(RhatMob * L_block true u v * RhatMob)(i, j) = if i = j then
  2 · (scalar(u,v) if i = 0 else signed(u,v)) else 0`.

## Cycle spectra — witness formulas

`scalarCycle_eigenvalue` uses witness `v j := cos(2π·k·j/n)` with eigenvalue
`2(1 − cos(2πk/n))`. Proof shape:

1. `scalar_mulVec_row` expands `(L · w)(i) = 2 w(i) − w(succ i) − w(pred i)`
   by `Finset.sum_subset` on the three-element support
   `{i, succ i, pred i}`.
2. `cos_succFin_val` and `cos_predFin_val` use `θ · n = 2πk` and
   `Real.cos_nat_mul_two_pi` / `Real.cos_sub_nat_mul_two_pi` to move cosines
   across the mod-n boundary.
3. Sum-to-product via `Real.cos_add_cos` collapses
   `cos(θ(i+1)) + cos(θ(i−1)) = 2 · cos(θi) · cos(θ)`.

`signedCycle_eigenvalue` uses witness `v j := cos(π(2k+1)j/n)` with eigenvalue
`2(1 − cos(π(2k+1)/n))`. Three helpers `signed_mulVec_{middle,zero,nm1}`
expand the mulVec according to whether `i` is interior, `0`, or `n-1` (the
wrap endpoint flips sign). The key identity `signed_cos_complement` uses
`Real.cos_nat_mul_pi_sub` with `(−1)^(2k+1) = −1` to show
`cos(φ · n − x) = −cos(x)` when `φ · n = π(2k+1)`. Boundary cases collapse
via the complement identity and `Real.cos_two_mul`; the interior case is
identical in structure to the scalar sum-to-product.

### Refactor notes

- Hypothesis strengthened from `2 ≤ n` to `3 ≤ n`. The `n = 2` case is
  mathematically false: `[[2, −1], [−1, 2]]` has eigenvalues `{1, 3}`, not
  the predicted `{0, 4}`. For `n = 2` the scalar cycle Laplacian degenerates
  because `succ = pred` on `Fin 2`. Genuine statement correction, not a
  convenience.
- Eigenvectors are typed `Fin n → ℝ`, not `Fin n → ℂ`. The cosine basis is
  real-valued, so no complex exponentials are pulled in.

## `flat_cycle_spectrum`

Closed via fiber-disjoint support vectors `v₁, v₂ : Fin n × Fin 2 → ℝ` and
`Fintype.linearIndependent_iff` + `Fin.sum_univ_two`. Evaluating the
linear-dependence hypothesis at `(⟨0, _⟩, 0)` and `(⟨0, _⟩, 1)` collapses to
`g 0 = 0` and `g 1 = 0` via `simp`, closed by `fin_cases`.

## Mathlib dependencies exercised

- `Mathlib.Combinatorics.SimpleGraph.LapMatrix.card_ConnectedComponent_eq_rank_ker_lapMatrix`
  gives the scalar kernel dimension directly.
- `Equiv.boolProdEquivSum` + `finTwoEquiv` align `V × Fin 2 ≃ V ⊕ V` with
  `Matrix.fromBlocks`.
- `Fintype.card_subtype_le` bounds
  `numOddWrapComponents ≤ numComponents`.
- `Matrix.diagonal_apply`, `SimpleGraph.adjMatrix_apply`, `Matrix.sub_apply`,
  `Matrix.fromBlocks_apply_{11,12,21,22}`, `Matrix.reindex_apply`, and
  `inv_one` / `Matrix.mul_one` / `Matrix.one_mul` — the simp lemmas that
  reduce the flat branch of `laplacian_decomposes` to `fin_cases` on `Fin 2`.
