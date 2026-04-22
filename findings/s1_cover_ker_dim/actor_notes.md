# s1_cover_ker_dim — actor notes

## (a) Strategy taken

Direct deck-eigenspace decomposition, bypassing `scalarLap_cover_splits`
(which is still `sorry`). The proof of the target theorem is reduced to a
single linear equivalence
`kerCoverEquiv : ker(toLin' L̃) ≃ₗ[ℝ] ker(toLin' L_scalar) × ker(toLin' L_signed)`
constructed from the `symProj` / `antiProj` projections already defined in
`L5_Cover.lean` and an explicit `combine` inverse
`(g, h) ↦ fun (v, b) ↦ if b then g v − h v else g v + h v`.

Given `kerCoverEquiv`, the theorem is closed in three lines:
`LinearEquiv.finrank_eq` + `FiniteDimensional.finrank_prod` + `rw`.

## (b) New helper lemmas required

The residual work is concentrated inside `kerCoverEquiv`. To finish it, the
following standalone lemma (not yet in the codebase) is required:

```
theorem signedLaplacianMobius_toLin'_apply_eq_zero_iff (x : G.V → ℝ) :
    toLin' G.signedLaplacianMobius x = 0 ↔
    ∀ u v (h : G.graph.Adj u v),
      if G.wrap ⟨s(u,v), _⟩ then x u = -x v else x u = x v
```

the signed analogue of Mathlib's
`SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_adj`. Once this is
in hand, together with the cover's version of the same lemma, both
directions of `kerCoverEquiv` are a case split on wrap status.

No changes to `Basic.lean` or `KernelDimension.lean` are required.

## (c) Self-identified risks / gaps

1. The signed-Laplacian kernel characterisation above is standard but not
   yet in the project; it could be surprisingly fiddly to derive from
   scratch (positive-semidefinite quadratic form, edge-by-edge vanishing),
   though the `PosSemidef` argument used by Mathlib for `lapMatrix`
   transfers nearly verbatim.
2. `G.orientationDoubleCover.scalarLaplacian = G.coverGraph.lapMatrix ℝ` is
   claimed as definitionally true; needs verification — the
   `orientationDoubleCover` definition uses `graph := G.coverGraph` and
   `scalarLaplacian := graph.lapMatrix ℝ`, so this should reduce by `rfl`
   but may need `show` / `unfold`.
3. The `LinearEquiv` bookkeeping (that `symProj`/`antiProj`/`combine`
   actually land in the stated kernels and are mutual inverses as linear
   maps) is routine but voluminous; no conceptual obstacle.
4. No hidden `sorryAx` risk in helper terms because the only `sorry` in
   the artifact is the final `sorry` in the `noncomputable def`
   `kerCoverEquiv`. The theorem `scalarLap_cover_kernel_dim_candidate`
   uses only `LinearEquiv.finrank_eq` and `FiniteDimensional.finrank_prod`
   over `kerCoverEquiv`, so no intermediate `have` can harbour a sorry.

## (d) Self-search confirmation

I grepped the artifact `actor_proof.lean` for `sorry`, `sorryAx`, and
`admit`. Result: exactly one real `sorry` (line 92, inside
`kerCoverEquiv`); the other four matches are inside docstring prose
describing the strategy. No `sorryAx`, no `admit`.
