/-
ConnectionLaplacian/L18_RussellZ2Bridge.lean

A deliberately narrow bridge from the scalar, unknown-reliability Russell
co-observation model to the EXISTING signed connection Laplacian theorem.

For positive scalar skills k_i and pair correlations C_ij = k_i*k_j,
log coordinates satisfy z_i + z_j = log C_ij. Their edge-to-edge linear
transport is z -> -z, i.e. every graph edge has Z/2 sign -1.

Only the LINEAR sign cocycle is formalized here. Affine translations
(log C_ij), Gaussian/covariance gauges, unknown sensor reliabilities and
finite-sample conclusions are NOT proved by this file.
-/

import ConnectionLaplacian.L8_Recognition

namespace ConnectionLaplacian
namespace ConnGraph

open Matrix FiniteDimensional

variable (G : ConnGraph)

/-- The special signed connection with -1 on every edge (a negative edge
    corresponds to wrap=true in the existing ConnGraph convention). -/
def allEdgesNegative : Prop :=
  ∀ e : G.graph.edgeSet, G.wrap e

/-- A component admits a proper two-coloring of its incident edges.
    Coloring is defined on all vertices for compatibility with L6.isBalanced;
    only edges in the designated component impose conditions. -/
def isBipartiteComponent (C : G.graph.ConnectedComponent) : Prop :=
  ∃ ε : G.V → Bool, ∀ (u v : G.V), ∀ (_h : G.graph.Adj u v),
    G.graph.connectedComponentMk u = C → ε u ≠ ε v

noncomputable def numBipartiteComponents : ℕ :=
  Fintype.card { C : G.graph.ConnectedComponent // G.isBipartiteComponent C }

/-- D + A for a loopless simple graph: diagonal degree, positive adjacent
    off-diagonal entries, zero on nonedges. -/
noncomputable def signlessLaplacian : Matrix G.V G.V ℝ :=
  fun u v =>
    if u = v then (G.graph.neighborFinset u).card
    else if G.graph.Adj u v then 1 else 0

/-- Under all-negative edge transport, the existing signed Mobius
    Laplacian IS the signless graph Laplacian, entry by entry. -/
theorem allNegative_signed_eq_signless
    (hneg : G.allEdgesNegative) :
    G.signedLaplacianMobius = G.signlessLaplacian := by
  ext u v
  by_cases huv : u = v
  · simp [signedLaplacianMobius, signlessLaplacian, huv]
  · by_cases hadj : G.graph.Adj u v
    · have hw :
        G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩ :=
        hneg _
      simp [signedLaplacianMobius, signlessLaplacian, huv, hadj, hw]
    · simp [signedLaplacianMobius, signlessLaplacian, huv, hadj]

/-- L6 balance of an all-negative connection is the ordinary
    two-coloring (bipartiteness) criterion on each component. -/
theorem allNegative_balanced_iff_bipartite
    (hneg : G.allEdgesNegative) (C : G.graph.ConnectedComponent) :
    G.isBalanced C ↔ G.isBipartiteComponent C := by
  unfold isBalanced isBipartiteComponent
  constructor
  · rintro ⟨ε, hε⟩
    refine ⟨ε, ?_⟩
    intro u v hadj hC
    exact (hε u v hadj hC).mp (hneg _)
  · rintro ⟨ε, hε⟩
    refine ⟨ε, ?_⟩
    intro u v hadj hC
    constructor
    · intro _
      exact hε u v hadj hC
    · intro _
      exact hneg _

theorem allNegative_balanced_count_eq_bipartite
    (hneg : G.allEdgesNegative) :
    G.numBalancedComponents = G.numBipartiteComponents := by
  classical
  unfold numBalancedComponents numBipartiteComponents
  let e :
      { C : G.graph.ConnectedComponent // G.isBalanced C } ≃
      { C : G.graph.ConnectedComponent // G.isBipartiteComponent C } :=
    { toFun := fun C =>
        ⟨C.1, (G.allNegative_balanced_iff_bipartite hneg C.1).mp C.2⟩
      invFun := fun C =>
        ⟨C.1, (G.allNegative_balanced_iff_bipartite hneg C.1).mpr C.2⟩
      left_inv := by
        intro C
        apply Subtype.ext
        rfl
      right_inv := by
        intro C
        apply Subtype.ext
        rfl }
  exact Fintype.card_congr e

/-- The pre-existing kernel-dimension theorem specializes to the scalar
    Russell all-negative-edge operator. This is the FIRST formal bridge;
    it does not claim a theorem about finite-sample learning or GL(d). -/
theorem allNegative_signless_kernel_dim
    (hneg : G.allEdgesNegative) :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.signlessLaplacian)) =
      G.numBipartiteComponents := by
  rw [← G.allNegative_signed_eq_signless hneg,
      G.signedLaplacian_kernel_dim_general,
      G.allNegative_balanced_count_eq_bipartite hneg]

/-- The full (two-fiber) connection Laplacian inherits the same
    decomposition, with one ordinary scalar zero mode for each
    connected component and one extra for each bipartite component. -/
theorem allNegative_connection_kernel_dim
    (hneg : G.allEdgesNegative) :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian true))) =
      G.numComponents + G.numBipartiteComponents := by
  calc
    _ = G.numComponents + G.numBalancedComponents := by
      simpa using (G.connectionLaplacian_kernel_dim_general true)
    _ = G.numComponents + G.numBipartiteComponents := by
      rw [G.allNegative_balanced_count_eq_bipartite hneg]

end ConnGraph
end ConnectionLaplacian
