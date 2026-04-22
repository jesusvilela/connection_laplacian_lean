/-
findings/s1_cover_ker_dim/actor_proof.lean

Candidate proof of `ConnectionLaplacian.ConnGraph.scalarLap_cover_kernel_dim`.

The global proof at the bottom is complete relative to ONE isolated helper
linear-equivalence (`kerCoverEquiv`) which packages the deck-symmetrization /
antisymmetrization. We mark that helper with an explicit `sorry` and state
exactly what data are needed to close it.

Do NOT import this file into the live build. The surrounding namespace is
reopened so the proof can reference `G.orientationDoubleCover`,
`G.scalarLaplacian`, `G.signedLaplacianMobius`, `G.coverGraph`,
`G.prodBoolEquivSum`, `G.symProj`, `G.antiProj`, `G.deck`.

This file must compile if dropped in under `ConnectionLaplacian/`. It does
NOT use `scalarLap_cover_splits` (still a `sorry` in L5).
-/

import ConnectionLaplacian.L5_Cover

namespace ConnectionLaplacian

open Matrix BigOperators
open scoped Kronecker

namespace ConnGraph

variable (G : ConnGraph)

/-! ### Helper: the single residual linear equivalence.

This is the only place a `sorry` remains. It states that the kernel of
the cover's scalar Laplacian is linearly equivalent (over ℝ) to the
product of the kernels of the base scalar and signed Laplacians. The
equivalence is given (explicitly, in the proof sketch below) by the
deck-symmetrization / antisymmetrization maps `symProj`, `antiProj`, and
by `(g, h) ↦ fun (v, b) ↦ if b then g v - h v else g v + h v` in the other
direction.

To close this `sorry` one must:

(a) Prove: if `L̃ *ᵥ f = 0` then `scalarLaplacian *ᵥ symProj f = 0`.
    Direct computation using Mathlib's
    `lapMatrix_toLin'_apply_eq_zero_iff_forall_adj` applied on the cover:
    `f (u, b) = f (v, c)` for every cover-adjacent pair `(u,b) ~ (v,c)`.
    In particular for a non-wrap edge `u — v` both sheets give
    `f (u, false) = f (v, false)` and `f (u, true) = f (v, true)`, hence
    `symProj f u = symProj f v`. For a wrap edge we pair
    `f (u, false) = f (v, true)` and `f (u, true) = f (v, false)`, still
    yielding `symProj f u = symProj f v`.

(b) Prove: if `L̃ *ᵥ f = 0` then `signedLaplacianMobius *ᵥ antiProj f = 0`.
    Direct computation: expanding `signedLaplacianMobius.mulVec (antiProj f) v`
    and using the adjacency condition on the cover as in (a), the non-wrap
    branch contributes `antiProj f u − antiProj f v = 0` and the wrap
    branch contributes `antiProj f u + antiProj f v = 0` (because
    `f(u,false)=f(v,true)` and `f(u,true)=f(v,false)` force
    `antiProj f v = −antiProj f u`).

(c) Prove: for `g ∈ ker(scalarLap)` and `h ∈ ker(signedLapMobius)`, the
    function `combine : CoverV → ℝ` defined by
    `combine (v, false) = g v + h v`, `combine (v, true) = g v − h v`
    satisfies `L̃ *ᵥ combine = 0`. Again via
    `lapMatrix_toLin'_apply_eq_zero_iff_forall_adj` on the cover.

(d) Prove the two composites are identities. `symProj`/`antiProj` are
    linear in `f`; `combine` is linear in `(g, h)`; and on pure sym/anti
    parts of `f` they invert each other exactly.

All of (a)–(d) are entirely elementary: adjacency in the cover, unfolded
via `G.coverAdj`, splits by wrap status, and the ±1 eigenspace basis
`e_± = (1, ±1)` on each fiber diagonalises the deck action. No
`scalarLap_cover_splits`, no Kronecker identities are needed. -/
noncomputable def kerCoverEquiv :
    LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian) ≃ₗ[ℝ]
      LinearMap.ker (toLin' G.scalarLaplacian) ×
      LinearMap.ker (toLin' G.signedLaplacianMobius) := by
  -- RESIDUAL SORRY: see docstring above.
  -- Required ingredients (not yet formalized in this project):
  --   * `G.orientationDoubleCover.scalarLaplacian = G.coverGraph.lapMatrix ℝ`
  --       (this is *definitionally* true since `scalarLaplacian := graph.lapMatrix ℝ`
  --       and `orientationDoubleCover.graph = coverGraph`).
  --   * `lapMatrix_toLin'_apply_eq_zero_iff_forall_adj` on `G.coverGraph`.
  --   * An analogous edge-characterisation for `signedLaplacianMobius`:
  --       `toLin' (G.signedLaplacianMobius) x = 0 ↔
  --        ∀ u v (h : G.graph.Adj u v),
  --          if G.wrap ⟨s(u,v), _⟩ then x u = -x v else x u = x v`.
  --     This is the signed analogue of
  --     `lapMatrix_toLin'_apply_eq_zero_iff_forall_adj` and should be proved
  --     in `KernelDimension.lean` as a standalone lemma.
  sorry

/-! ### The theorem, closed from `kerCoverEquiv`. -/

theorem scalarLap_cover_kernel_dim_candidate :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian)) =
      FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' G.scalarLaplacian)) +
      FiniteDimensional.finrank ℝ
          (LinearMap.ker (toLin' G.signedLaplacianMobius)) := by
  -- Push through the linear equivalence kerCoverEquiv.
  have hEq : FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian)) =
      FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.scalarLaplacian) ×
         LinearMap.ker (toLin' G.signedLaplacianMobius)) :=
    LinearEquiv.finrank_eq G.kerCoverEquiv
  rw [hEq, FiniteDimensional.finrank_prod]

end ConnGraph

end ConnectionLaplacian
