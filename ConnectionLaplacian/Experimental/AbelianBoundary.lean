import ConnectionLaplacian.Experimental.UnitaryEdge

/-!
The original Z/2 transport vocabulary is *abelian*, even though arbitrary
unitary graph connections need not be. This is a formal, bounded explanation
of why a scalar-channel Fourier analysis was adequate for that model but
cannot settle the noncommuting SU(2) experiment.
-/

namespace ConnectionLaplacian

open Matrix

namespace ConnGraph

variable (G : ConnGraph)

/-- Any two edge transports in the submitted I₂ / σx model commute. -/
theorem original_edge_transports_commute (mobius : Bool)
    (e f : G.graph.edgeSet) :
    G.edgeMatrix mobius e * G.edgeMatrix mobius f =
      G.edgeMatrix mobius f * G.edgeMatrix mobius e := by
  by_cases he : mobius ∧ G.wrap e <;> by_cases hf : mobius ∧ G.wrap f <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [edgeMatrix, he, hf, σx, I₂, Matrix.mul_fin_two]

/-- The common symmetric mode is fixed by every original edge transport. -/
theorem original_edge_fixes_symmetric_mode (mobius : Bool)
    (e : G.graph.edgeSet) :
    G.edgeMatrix mobius e *ᵥ ![(1 : ℝ), 1] = ![(1 : ℝ), 1] := by
  by_cases he : mobius ∧ G.wrap e <;>
    ext i <;> fin_cases i <;>
    simp [edgeMatrix, he, σx, I₂, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two]

end ConnGraph
end ConnectionLaplacian
