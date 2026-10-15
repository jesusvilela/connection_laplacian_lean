/-
Comparator CHALLENGE module (local hardening harness).

The seven statements below are transcriptions of the representative
end theorems of the repository's verified spine (the same list the CI
axiom audit in `ConnectionLaplacian/AxiomAudit.lean` prints). Each is
stated with `sorry`: this module asserts WHAT is claimed, and provides
no proof. The companion `Hardening.Solution` module supplies proofs by
aliasing the spine theorems. `comparator` checks that the two agree on
every statement, that the solution uses only the three standard Lean
axioms, and that every exported constant kernel-replays.
-/
import ConnectionLaplacian
import Hardening.Compat

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators
open Polynomial (C)

variable (G : ConnGraph)

/-- Challenge form of
`ConnectionLaplacian.ConnGraph.cover_charpoly_eq_scalar_times_mobius`. -/
theorem cover_charpoly_eq_scalar_times_mobius :
    (G.orientationDoubleCover.scalarLaplacian).charpoly =
      G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly := by
  sorry

/-- Challenge form of
`ConnectionLaplacian.ConnGraph.isBalanced_iff_closedWalk_wrap_even`. -/
theorem isBalanced_iff_closedWalk_wrap_even
    (C : G.graph.ConnectedComponent) : G.isBalanced C ↔
      ∀ (v : G.V) (p : G.graph.Walk v v),
        G.graph.connectedComponentMk v = C →
        Even (p.edges.countP
                (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))) := by
  sorry

/-- Challenge form of
`ConnectionLaplacian.ConnGraph.signedLaplacianMobius_posSemidef`. -/
theorem signedLaplacianMobius_posSemidef :
    G.signedLaplacianMobius.PosSemidef := by
  sorry

/-- Challenge form of
`ConnectionLaplacian.ConnGraph.numBalancedComponents_monotone_remove_nonwrap_nonbridge`. -/
theorem numBalancedComponents_monotone_remove_nonwrap_nonbridge
    (G : ConnGraph) (e : G.graph.edgeSet)
    (_hnonwrap : ¬ G.wrap e)
    (hnonbridge : ¬ G.graph.IsBridge e.val) :
    G.numBalancedComponents ≤ (G.eraseEdge e).numBalancedComponents := by
  sorry

/-- Challenge form of
`ConnectionLaplacian.ConnGraph.mobius_charpoly_roots_eq_union`. -/
theorem mobius_charpoly_roots_eq_union :
    (G.laplacian true).charpoly.roots =
      G.scalarLaplacian.charpoly.roots +
        G.signedLaplacianMobius.charpoly.roots := by
  sorry

/-- Challenge form of
`ConnectionLaplacian.ConnGraph.frobenius_laplacian_decomposes`. -/
theorem frobenius_laplacian_decomposes :
    ((G.laplacian true)ᵀ * (G.laplacian true)).trace
      = (G.scalarLaplacianᵀ * G.scalarLaplacian).trace +
        (G.signedLaplacianMobiusᵀ * G.signedLaplacianMobius).trace := by
  sorry

/-- Challenge form of
`ConnectionLaplacian.ConnGraph.trace_mul_scalar_signed_eq`. -/
theorem trace_mul_scalar_signed_eq :
    2 * (G.scalarLaplacian * G.signedLaplacianMobius).trace
      = ((G.scalarLaplacian + G.signedLaplacianMobius) *
           (G.scalarLaplacian + G.signedLaplacianMobius)).trace
        - (G.scalarLaplacian * G.scalarLaplacian).trace
        - (G.signedLaplacianMobius * G.signedLaplacianMobius).trace := by
  sorry

end Hardening
