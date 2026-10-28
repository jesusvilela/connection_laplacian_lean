import ConnectionLaplacian.Experimental.GeneralFiberGauge

/-!
Graph-wide fiber-valued incidence over an arbitrary finite incidence family.

The fiber index F can have any finite cardinality; edge transports are
arbitrary real matrices, and can be noncommuting. This is a genuine global
assembly identity, not a scalar decomposition or a 2x2 calculation.

The *separate* bridge from this assembled Gram to the manuscript's
ConnGraph.laplacian needs a proof that undirected graph edges, orientation,
unitarity and degree counting agree with the chosen incidence family.
-/

namespace ConnectionLaplacian
namespace ArbitraryFiberIncidence

open Matrix BigOperators

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq F]

/-- One edge acts on all vertex fibers, with source identity and destination
negative transport. Arbitrary finite fiber rank, with no commutativity axiom. -/
noncomputable def edgeRow (src dst : E → V)
    (transport : E → Matrix F F ℝ) (e : E) :
    Matrix F (V × F) ℝ :=
  fun i vi =>
    (if vi.1 = src e then (if i = vi.2 then 1 else 0) else 0) -
    (if vi.1 = dst e then transport e i vi.2 else 0)

/-- The graph-wide incidence is a stack of actual fiber-valued edge rows. -/
noncomputable def globalIncidence (src dst : E → V)
    (transport : E → Matrix F F ℝ) :
    Matrix (E × F) (V × F) ℝ :=
  fun ei vi => edgeRow src dst transport ei.1 ei.2 vi

/-- Independent edge-by-edge energy assembly, indexed by the edge family. -/
noncomputable def assembledEdgeGram (src dst : E → V)
    (transport : E → Matrix F F ℝ) :
    Matrix (V × F) (V × F) ℝ :=
  ∑ e : E, (edgeRow src dst transport e).transpose *
           edgeRow src dst transport e

/-- Gram of the full incidence equals the sum of its edge contributions,
including an empty edge family. No reduction to rank one, to a commuting
transport, or to a cycle family is used in this proof. -/
theorem globalIncidence_gram (src dst : E → V)
    (transport : E → Matrix F F ℝ) :
    (globalIncidence src dst transport).transpose *
      globalIncidence src dst transport =
      assembledEdgeGram src dst transport := by
  classical
  ext a b
  simp [globalIncidence, assembledEdgeGram, edgeRow,
        Matrix.mul_apply, Matrix.transpose_apply,
        Fintype.sum_prod_type]

end ArbitraryFiberIncidence
end ConnectionLaplacian
