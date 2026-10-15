/-
NEGATIVE CONTROL 2 (do not import from anything).

Identical to `Hardening.Solution` except that ONE theorem
(`mobius_charpoly_roots_eq_union`) is "proved" from a smuggled local
axiom instead of the spine. A comparator run against
`Hardening.Challenge` with this solution MUST FAIL with
`Illegal axiom detected: 'Hardening.smuggled_roots_union'`.
This models a solution that hides an unproven assumption behind an
otherwise honest-looking development.
-/
import ConnectionLaplacian
import Hardening.Compat

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators
open Polynomial (C)

variable (G : ConnGraph)

/-- The smuggled assumption: exactly the statement we should have to prove. -/
axiom smuggled_roots_union (G : ConnGraph) :
    (G.laplacian true).charpoly.roots =
      G.scalarLaplacian.charpoly.roots +
        G.signedLaplacianMobius.charpoly.roots

theorem cover_charpoly_eq_scalar_times_mobius :
    (G.orientationDoubleCover.scalarLaplacian).charpoly =
      G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly :=
  ConnGraph.cover_charpoly_eq_scalar_times_mobius G

theorem isBalanced_iff_closedWalk_wrap_even
    (C : G.graph.ConnectedComponent) : G.isBalanced C ↔
      ∀ (v : G.V) (p : G.graph.Walk v v),
        G.graph.connectedComponentMk v = C →
        Even (p.edges.countP
                (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))) :=
  ConnGraph.isBalanced_iff_closedWalk_wrap_even G C

theorem signedLaplacianMobius_posSemidef :
    G.signedLaplacianMobius.PosSemidef :=
  ConnGraph.signedLaplacianMobius_posSemidef G

theorem numBalancedComponents_monotone_remove_nonwrap_nonbridge
    (G : ConnGraph) (e : G.graph.edgeSet)
    (_hnonwrap : ¬ G.wrap e)
    (hnonbridge : ¬ G.graph.IsBridge e.val) :
    G.numBalancedComponents ≤ (G.eraseEdge e).numBalancedComponents :=
  ConnGraph.numBalancedComponents_monotone_remove_nonwrap_nonbridge
    G e _hnonwrap hnonbridge

/-- SMUGGLED: proved from the local axiom, not from the spine. -/
theorem mobius_charpoly_roots_eq_union :
    (G.laplacian true).charpoly.roots =
      G.scalarLaplacian.charpoly.roots +
        G.signedLaplacianMobius.charpoly.roots :=
  smuggled_roots_union G

theorem frobenius_laplacian_decomposes :
    ((G.laplacian true)ᵀ * (G.laplacian true)).trace
      = (G.scalarLaplacianᵀ * G.scalarLaplacian).trace +
        (G.signedLaplacianMobiusᵀ * G.signedLaplacianMobius).trace :=
  ConnGraph.frobenius_laplacian_decomposes G

theorem trace_mul_scalar_signed_eq :
    2 * (G.scalarLaplacian * G.signedLaplacianMobius).trace
      = ((G.scalarLaplacian + G.signedLaplacianMobius) *
           (G.scalarLaplacian + G.signedLaplacianMobius)).trace
        - (G.scalarLaplacian * G.scalarLaplacian).trace
        - (G.signedLaplacianMobius * G.signedLaplacianMobius).trace :=
  ConnGraph.trace_mul_scalar_signed_eq G

end Hardening
