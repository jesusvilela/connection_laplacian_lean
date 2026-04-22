# Actor notes — `laplacian_kernel_dim_decomposes`

## Strategy

Chain three kernel-dim invariances across the explicit similarity given by
`KernelDimension.laplacian_decomposes`:

1. **Similarity invariance** — if `P.det ≠ 0`, then
   `finrank ker (toLin' (P*L*P⁻¹)) = finrank ker (toLin' L)`.
   Built as `e := LinearEquiv.ofLinear (toLin' P) (toLin' P⁻¹) _ _`; factor
   `toLin' (P*L*P⁻¹) = e.comp ((toLin' L).comp e.symm)` using
   `← Matrix.mulVec_mulVec`; then `LinearEquiv.ker_comp` + `LinearMap.ker_comp`
   + `Submodule.comap_equiv_eq_map_symm` + `LinearEquiv.finrank_map_eq`.

2. **Reindex invariance** — `toLin'_reindex` rewrites the reindex as a
   composition with `funCongrLeft` equivalences; same ker-shuffle as (1).

3. **Block-diagonal split** — explicit `LinearEquiv` between
   `ker (toLin' (fromBlocks A 0 0 B))` and `ker (toLin' A) × ker (toLin' B)`,
   using `fromBlocks_mulVec` and `Sum.elim` / `inl`-`inr` projections. Then
   `FiniteDimensional.finrank_prod`.

Assembly: `obtain ⟨P, hPdet, hreindex⟩ := G.laplacian_decomposes mobius`;
rewrite `hreindex` into the reindex-invariance step; `linarith` combines
the three equalities.

## New helpers

All three helpers are module-level lemmas, universe-polymorphic over the
index type, reusable for the twin sorry `L5_Cover.scalarLap_cover_kernel_dim`
(same three-step pattern).

## Risks (self-identified)

- `LinearEquiv.ker_comp` unification relies on the coerce-to-`LinearMap`
  pattern `(e : _ →ₗ _).comp _` matching the stated lemma shape; if
  Mathlib's signature differs, swap for `LinearMap.ker_comp_of_injective`
  with `e.injective`.
- The `show`-line in (1) trusts `ofLinear_toLinearMap` / `_symm_toLinearMap`
  as definitional equalities.
- Helper (3)'s `LinearEquiv` uses η-reduction (`fun i => f i = f`) in
  `left_inv`/`right_inv`; Lean 4 has η, but a `funext` fallback is included.

## Self-grep

Ran Grep for `sorry|sorryAx` on `actor_proof.lean`: only two hits,
both inside explanatory comments (lines 16, 21). No `sorry` or
`sorryAx` appears in proof code.
