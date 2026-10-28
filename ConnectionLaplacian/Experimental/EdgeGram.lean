import ConnectionLaplacian.Experimental.IncidenceEnergy

/-!
A literal one-edge incidence matrix B = [I₂ | -U] and its Gram block.
This is the local building block for the graph-wide factorization.
It does not claim to prove the global identity D^T D = L.
-/
namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-- Local incidence between the two endpoint fibers of one undirected edge. -/
noncomputable def edgeIncidence (mobius : Bool) (e : G.graph.edgeSet) :
    Matrix (Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  fun i p => match p with
    | Sum.inl j => if i = j then 1 else 0
    | Sum.inr j => -(G.edgeMatrix mobius e) i j

/-- Gram block of one edge: [I, -U; -U, I] for symmetric orthogonal U. -/
theorem edgeIncidence_gram (mobius : Bool) (e : G.graph.edgeSet) :
    (G.edgeIncidence mobius e).transpose * G.edgeIncidence mobius e =
      Matrix.fromBlocks I₂ (-(G.edgeMatrix mobius e))
        (-(G.edgeMatrix mobius e)) I₂ := by
  by_cases hw : mobius ∧ G.wrap e
  · ext a b
    rcases a with i | i <;> rcases b with j | j
      <;> fin_cases i <;> fin_cases j
      <;> simp [edgeIncidence, edgeMatrix, hw, I₂, σx,
          Matrix.mul_apply, Matrix.transpose, Matrix.fromBlocks, Fin.sum_univ_two]
      <;> ring
  · ext a b
    rcases a with i | i <;> rcases b with j | j
      <;> fin_cases i <;> fin_cases j
      <;> simp [edgeIncidence, edgeMatrix, hw, I₂, σx,
          Matrix.mul_apply, Matrix.transpose, Matrix.fromBlocks, Fin.sum_univ_two]
      <;> ring

end ConnGraph
end ConnectionLaplacian
