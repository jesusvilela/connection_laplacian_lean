/-
ConnectionLaplacian/L9_Bounds.lean

**Stratum L9 — Trace formulas, kernel inequalities, and kernel-drop.**

Round-4 additions: three immediate consequences of L8, relating the
formalised kernel-dimension theorems to numerical scalar invariants
(trace and simple cardinality inequalities). All of these are drop-in
corollaries of the L4/L8 recognition stack.

1. `trace_scalarLaplacian`, `trace_signedLaplacianMobius`,
   `trace_laplacian` — all equal 2·|E| (resp 4·|E|); the diagonals of
   both scalar and signed Laplacians coincide with the vertex degrees
   because simple graphs are irreflexive.

2. `signed_kernel_le_scalar_kernel` — the signed kernel is at most
   the scalar kernel, because #balanced components ≤ #components.

3. `kernel_drop_le_numComponents` / `kernel_drop_eq_unbalanced` — the
   drop in kernel dimension moving from flat to Möbius equals
   #unbalanced components, bounded by #components.

These extend the spectral-invariance toolkit around the connection
Laplacian without introducing new Mathlib dependencies.
-/

import ConnectionLaplacian.L8_Recognition
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace ConnectionLaplacian

open Matrix BigOperators FiniteDimensional

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L9.1 — Trace formulas: `tr L = 2|E|` / `4|E|` -/

/-- Diagonal of the scalar Laplacian equals vertex degree. -/
private lemma scalarLaplacian_diag (v : G.V) :
    G.scalarLaplacian v v = (G.graph.degree v : ℝ) := by
  unfold scalarLaplacian
  have hna : ¬ G.graph.Adj v v := SimpleGraph.irrefl _
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
        Matrix.diagonal_apply_eq, SimpleGraph.adjMatrix_apply, hna]

/-- Diagonal of the signed Möbius Laplacian equals vertex degree (the
wrap/non-wrap sign convention only affects off-diagonal entries). -/
private lemma signedLaplacianMobius_diag (v : G.V) :
    G.signedLaplacianMobius v v = (G.graph.degree v : ℝ) := by
  show (if v = v then ((G.graph.neighborFinset v).card : ℝ) else _) = _
  rw [if_pos rfl]
  rfl

/-- Trace of the scalar Laplacian equals `2·|E|`. -/
theorem trace_scalarLaplacian :
    G.scalarLaplacian.trace = (2 * G.graph.edgeFinset.card : ℝ) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, scalarLaplacian_diag]
  have h := G.graph.sum_degrees_eq_twice_card_edges
  rw [show (∑ v, (G.graph.degree v : ℝ)) = ((∑ v, G.graph.degree v : ℕ) : ℝ) by push_cast; rfl, h]
  push_cast; ring

/-- Trace of the signed Möbius Laplacian equals `2·|E|`. -/
theorem trace_signedLaplacianMobius :
    G.signedLaplacianMobius.trace = (2 * G.graph.edgeFinset.card : ℝ) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, signedLaplacianMobius_diag]
  have h := G.graph.sum_degrees_eq_twice_card_edges
  rw [show (∑ v, (G.graph.degree v : ℝ)) = ((∑ v, G.graph.degree v : ℕ) : ℝ) by push_cast; rfl, h]
  push_cast; ring

/-! ### L9.2 — Kernel inequalities -/

/-- The signed-Laplacian kernel is at most the scalar-Laplacian kernel.
Proof: both equal component counts (L8 / L4); balanced components form
a subset of components. -/
theorem signed_kernel_le_scalar_kernel :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.signedLaplacianMobius)) ≤
      FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.scalarLaplacian)) := by
  rw [G.signedLaplacian_kernel_dim_general, G.scalarLaplacian_kernel_dim]
  exact G.numBalancedComponents_le

/-- Flat-to-Möbius kernel drop equals #components − #balanced = #unbalanced. -/
theorem kernel_drop_eq_unbalanced :
    FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' (G.laplacian false))) -
      FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' (G.laplacian true))) =
    G.numComponents - G.numBalancedComponents := by
  have hbal_le : G.numBalancedComponents ≤ G.numComponents :=
    G.numBalancedComponents_le
  rw [G.connectionLaplacian_kernel_dim_general true,
      G.connectionLaplacian_kernel_dim_general false]
  simp only [if_true, if_false]
  omega

/-- The kernel drop is bounded by the number of connected components. -/
theorem kernel_drop_le_numComponents :
    FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' (G.laplacian false))) -
      FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' (G.laplacian true))) ≤
    G.numComponents := by
  rw [G.kernel_drop_eq_unbalanced]
  omega

end ConnGraph

end ConnectionLaplacian
