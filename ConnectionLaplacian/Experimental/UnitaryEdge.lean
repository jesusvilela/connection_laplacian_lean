/-!
# Experimental bridge: orthogonality of the manuscript's edge transports

This module is intentionally **not** imported by ConnectionLaplacian.lean:
the published Z/2 theorem surface is unchanged. It establishes the algebraic
premise needed to construct a covariant incidence map in a later dev step.
-/
import ConnectionLaplacian.Basic

namespace ConnectionLaplacian

open Matrix

private theorem I₂_sq : I₂ * I₂ = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I₂, Matrix.mul_fin_two]

namespace ConnGraph

variable (G : ConnGraph)

/-- Every transport in the original two-sheet model is involutive. -/
theorem edgeMatrix_involution (mobius : Bool) (e : G.graph.edgeSet) :
    G.edgeMatrix mobius e * G.edgeMatrix mobius e = I₂ := by
  unfold edgeMatrix
  split_ifs with h
  · exact σx_mul_σx
  · exact I₂_sq

/-- The two admissible real transports are symmetric matrices. -/
theorem edgeMatrix_transpose_eq (mobius : Bool) (e : G.graph.edgeSet) :
    (G.edgeMatrix mobius e).transpose = G.edgeMatrix mobius e := by
  unfold edgeMatrix
  split_ifs with h
  · exact σx_symmetric
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [I₂, Matrix.transpose]

/-- Real orthogonality: U^T U = I for every edge, including wrap edges. -/
theorem edgeMatrix_orthogonal (mobius : Bool) (e : G.graph.edgeSet) :
    (G.edgeMatrix mobius e).transpose * G.edgeMatrix mobius e = I₂ := by
  rw [G.edgeMatrix_transpose_eq]
  exact G.edgeMatrix_involution mobius e

end ConnGraph
end ConnectionLaplacian
