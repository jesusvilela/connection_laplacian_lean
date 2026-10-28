import ConnectionLaplacian.Experimental.ArbitraryFiberIncidence
import ConnectionLaplacian.Experimental.GlobalEntries

/-!
A typed bridge from the actual ConnGraph to the arbitrary-fiber incidence
constructor, with both directions of every adjacency.

The global Gram *assembly* is proved. The final half-normalized identity
with ConnGraph.laplacian is a named proposition/target, NOT an axiom or a
claimed theorem. This avoids replacing the paper's graph with a surrogate.
-/

namespace ConnectionLaplacian
namespace ConnGraph

open Matrix

variable (G : ConnGraph)

/-- Genuine directed adjacency of the paper's graph; no chosen linear
order or orientation of the underlying unordered edge is required. -/
def OrientedAdjacency : Type _ :=
  {uv : G.V × G.V // G.graph.Adj uv.1 uv.2}

def orientedSource (e : G.OrientedAdjacency) : G.V := e.1.1

def orientedTarget (e : G.OrientedAdjacency) : G.V := e.1.2

/-- Reverse-compatible transport on the true edge of G. -/
noncomputable def orientedTransport (mobius : Bool)
    (e : G.OrientedAdjacency) : Matrix (Fin 2) (Fin 2) ℝ :=
  G.edgeMatrix mobius
    ⟨s(e.1.1, e.1.2), (SimpleGraph.mem_edgeSet G.graph).mpr e.2⟩

/-- The explicit oriented covariant incidence, before 1/sqrt(2)
normalization. One row of the full two-dimensional fiber per half edge.
Unlike a scalar Fourier surrogate, this retains every vertex fiber. -/
noncomputable def orientedIncidence (mobius : Bool) :
    Matrix (G.OrientedAdjacency × Fin 2) (G.V × Fin 2) ℝ := by
  classical
  exact ArbitraryFiberIncidence.globalIncidence
    (G.orientedSource) (G.orientedTarget) (G.orientedTransport mobius)

/-- The incidence Gram is assembled edge-by-edge on the actual graph. -/
theorem orientedIncidence_gram_assembled (mobius : Bool) :
    (G.orientedIncidence mobius).transpose * G.orientedIncidence mobius =
      ArbitraryFiberIncidence.assembledEdgeGram
        G.orientedSource G.orientedTarget (G.orientedTransport mobius) := by
  classical
  exact ArbitraryFiberIncidence.globalIncidence_gram
    G.orientedSource G.orientedTarget (G.orientedTransport mobius)

/-- Open target for the ORIGINAL manuscript Laplacian. Every actual edge
appears twice, so normalization is by 1/2 at the Gram level.
Defining this proposition does not establish it. -/
def halfOrientedGramEqualsLaplacian (mobius : Bool) : Prop :=
    (1 / 2 : ℝ) •
      ((G.orientedIncidence mobius).transpose * G.orientedIncidence mobius)
      = G.laplacian mobius

end ConnGraph
end ConnectionLaplacian
