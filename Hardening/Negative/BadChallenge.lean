/-
NEGATIVE CONTROL 1 (do not import from anything).

Identical to `Hardening.Challenge` except that the coefficient `2` in
`trace_mul_scalar_signed_eq` has been tampered to `3`. A comparator run
against `Hardening.Solution` with this challenge MUST FAIL with a
statement mismatch. This module exists to demonstrate that the
comparator gate detects translation errors, not only kernel errors.
-/
import ConnectionLaplacian
import Hardening.Compat

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators
open Polynomial (C)

variable (G : ConnGraph)

theorem cover_charpoly_eq_scalar_times_mobius :
    (G.orientationDoubleCover.scalarLaplacian).charpoly =
      G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly := by
  sorry

theorem isBalanced_iff_closedWalk_wrap_even
    (C : G.graph.ConnectedComponent) : G.isBalanced C ↔
      ∀ (v : G.V) (p : G.graph.Walk v v),
        G.graph.connectedComponentMk v = C →
        Even (p.edges.countP
                (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))) := by
  sorry

theorem signedLaplacianMobius_posSemidef :
    G.signedLaplacianMobius.PosSemidef := by
  sorry

theorem numBalancedComponents_monotone_remove_nonwrap_nonbridge
    (G : ConnGraph) (e : G.graph.edgeSet)
    (_hnonwrap : ¬ G.wrap e)
    (hnonbridge : ¬ G.graph.IsBridge e.val) :
    G.numBalancedComponents ≤ (G.eraseEdge e).numBalancedComponents := by
  sorry

theorem mobius_charpoly_roots_eq_union :
    (G.laplacian true).charpoly.roots =
      G.scalarLaplacian.charpoly.roots +
        G.signedLaplacianMobius.charpoly.roots := by
  sorry

theorem frobenius_laplacian_decomposes :
    ((G.laplacian true)ᵀ * (G.laplacian true)).trace
      = (G.scalarLaplacianᵀ * G.scalarLaplacian).trace +
        (G.signedLaplacianMobiusᵀ * G.signedLaplacianMobius).trace := by
  sorry

/-- TAMPERED: the honest statement has coefficient `2`, not `3`. -/
theorem trace_mul_scalar_signed_eq :
    3 * (G.scalarLaplacian * G.signedLaplacianMobius).trace
      = ((G.scalarLaplacian + G.signedLaplacianMobius) *
           (G.scalarLaplacian + G.signedLaplacianMobius)).trace
        - (G.scalarLaplacian * G.scalarLaplacian).trace
        - (G.signedLaplacianMobius * G.signedLaplacianMobius).trace := by
  sorry

end Hardening
