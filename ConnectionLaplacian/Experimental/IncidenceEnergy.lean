import ConnectionLaplacian.Experimental.UnitaryEdge

/-!
Finite fiber-level energy algebra of the existing real rank-two connections.
These lemmas are *local edge identities*, not yet the global D^T D = L theorem.
-/
namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-- Transport along any edge is its own inverse on the two-dimensional fiber. -/
theorem edgeTransport_involution (mobius : Bool) (e : G.graph.edgeSet)
    (x : Fin 2 → ℝ) :
    G.edgeMatrix mobius e *ᵥ (G.edgeMatrix mobius e *ᵥ x) = x := by
  rw [← Matrix.mulVec_mulVec, G.edgeMatrix_involution]
  ext i
  fin_cases i <;> simp [I₂, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- An oriented covariant edge difference, before assembling graph incidence. -/
noncomputable def edgeDifference (mobius : Bool) (e : G.graph.edgeSet)
    (x y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => x i - (G.edgeMatrix mobius e *ᵥ y) i

/-- Reversing an edge preserves its squared covariant difference norm. -/
theorem edgeEnergy_reverse (mobius : Bool) (e : G.graph.edgeSet)
    (x y : Fin 2 → ℝ) :
    (∑ i : Fin 2, (G.edgeDifference mobius e x y i)^2) =
      ∑ i : Fin 2, (G.edgeDifference mobius e y x i)^2 := by
  by_cases hw : mobius ∧ G.wrap e
  · simp [edgeDifference, edgeMatrix, hw, σx, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two] <;> ring
  · simp [edgeDifference, edgeMatrix, hw, I₂, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two] <;> ring

/-- A local Gram identity: ||x-Uy||^2 = ||x||^2+||y||^2-2<x,Uy>. -/
theorem edgeEnergy_expand (mobius : Bool) (e : G.graph.edgeSet)
    (x y : Fin 2 → ℝ) :
    (∑ i : Fin 2, (G.edgeDifference mobius e x y i)^2) =
    (∑ i : Fin 2, (x i)^2) + (∑ i : Fin 2, (y i)^2)
      - 2 * (∑ i : Fin 2, x i * (G.edgeMatrix mobius e *ᵥ y) i) := by
  by_cases hw : mobius ∧ G.wrap e
  · simp [edgeDifference, edgeMatrix, hw, σx, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two] <;> ring
  · simp [edgeDifference, edgeMatrix, hw, I₂, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two] <;> ring

end ConnGraph
end ConnectionLaplacian
