import ConnectionLaplacian.Experimental.EdgeGram

/-!
Global *entry identification* for the manuscript's ConnGraph.laplacian.
These statements retain the actual graph and fiber types and include
isolated vertices; they are not a proof of a global incidence Gram identity.
-/

namespace ConnectionLaplacian
open Matrix

namespace ConnGraph

variable (G : ConnGraph)

/-- A vertex block is its ordinary graph degree times the fiber identity,
including an isolated vertex, where the entire block vanishes. -/
theorem laplacian_diagonal_block (mobius : Bool) (u : G.V) :
    G.laplacianBlock mobius u u = (G.degree u : ℝ) • I₂ := by
  have hno : ¬ G.graph.Adj u u := SimpleGraph.irrefl _
  simp [laplacianBlock, degreeBlockMatrix, adjacencyMatrix, hno]

/-- The off-diagonal block of an actual edge is minus its transport.
The formula does not depend on selecting an orientation of the unordered edge. -/
theorem laplacian_edge_block (mobius : Bool) {u v : G.V}
    (h : G.graph.Adj u v) :
    G.laplacianBlock mobius u v =
      -(G.edgeMatrix mobius
        ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩) := by
  have hne : u ≠ v := by
    intro huv
    subst v
    exact (SimpleGraph.irrefl _) h
  simp [laplacianBlock, degreeBlockMatrix, adjacencyMatrix, hne, h]

/-- Two distinct nonadjacent vertices have an exact zero coupling block. -/
theorem laplacian_nonedge_block (mobius : Bool) {u v : G.V}
    (hne : u ≠ v) (h : ¬ G.graph.Adj u v) :
    G.laplacianBlock mobius u v = 0 := by
  simp [laplacianBlock, degreeBlockMatrix, adjacencyMatrix, hne, h]

end ConnGraph
end ConnectionLaplacian
