/-
ConnectionLaplacian/Basic.lean

Definitions. A finite simple graph G on a finite vertex set V, with a
distinguished subset W ⊆ edges(G) of wrap edges. For each edge we attach
a 2×2 real matrix — the identity on non-wrap edges, σ_x on wrap edges
(Möbius) or identity everywhere (flat). The connection Laplacian L is
a V×V block matrix with 2×2 blocks, defined as degree diagonal minus
the signed adjacency.

We work over ℝ throughout. Mathlib's Matrix infrastructure provides what
we need for the block structure and eigenvalue statements.

Honest note: this file was written to compile against Mathlib v4.11.0,
but not verified by running Lean. Some lemma names may need adjusting.
-/

import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block

namespace ConnectionLaplacian

open Matrix BigOperators

/-- The 2×2 Pauli X matrix. Swaps the two fiber components. -/
def σx : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- The 2×2 identity. -/
def I₂ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 1]

lemma σx_mul_σx : σx * σx = I₂ := by
  simp [σx, I₂, Matrix.mul_fin_two]

lemma σx_symmetric : σx.transpose = σx := by
  simp [σx, Matrix.transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- σ_x has eigenvalues +1 (symmetric fiber) and −1 (antisymmetric fiber). -/
lemma σx_eigenvalues : ∃ (v_sym v_anti : Fin 2 → ℝ),
    v_sym ≠ 0 ∧ v_anti ≠ 0 ∧
    σx.mulVec v_sym = v_sym ∧
    σx.mulVec v_anti = -v_anti := by
  refine ⟨![1, 1], ![1, -1], ?_, ?_, ?_, ?_⟩
  · intro h; simpa using congrArg (· 0) h
  · intro h; simpa using congrArg (· 0) h
  · ext i; fin_cases i <;> simp [σx, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  · ext i; fin_cases i <;> simp [σx, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- A connection graph: a finite simple graph together with a subset of its
edges designated as "wrap" edges. -/
structure ConnGraph where
  V : Type*
  [fintype : Fintype V]
  [deceq : DecidableEq V]
  graph : SimpleGraph V
  [decrel : DecidableRel graph.Adj]
  wrap : graph.edgeSet → Prop
  [decwrap : DecidablePred wrap]

attribute [instance] ConnGraph.fintype ConnGraph.deceq ConnGraph.decrel ConnGraph.decwrap

namespace ConnGraph

variable (G : ConnGraph)

/-- The edge weight: σ_x on wrap edges in Möbius mode, I₂ otherwise. -/
def edgeMatrix (mobius : Bool) (e : G.graph.edgeSet) : Matrix (Fin 2) (Fin 2) ℝ :=
  if mobius ∧ G.wrap e then σx else I₂

/-- The scalar degree of a vertex — number of incident edges. -/
noncomputable def degree (v : G.V) : ℕ :=
  (G.graph.neighborFinset v).card

/-- The matrix-valued adjacency. For each ordered pair (u, v) with an edge
between them, we record the edge's matrix. Self-loops absent (simple graph). -/
noncomputable def adjacencyMatrix (mobius : Bool) :
    Matrix G.V G.V (Matrix (Fin 2) (Fin 2) ℝ) :=
  fun u v =>
    if h : G.graph.Adj u v then
      G.edgeMatrix mobius ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
    else 0

/-- The block-diagonal degree operator: D[v,v] = deg(v) · I₂. -/
noncomputable def degreeBlockMatrix :
    Matrix G.V G.V (Matrix (Fin 2) (Fin 2) ℝ) :=
  fun u v => if u = v then (G.degree u : ℝ) • I₂ else 0

/-- The connection Laplacian in block form: L = D − A. This is a V×V matrix
whose entries are 2×2 blocks. We'll flatten it to a (V × Fin 2) × (V × Fin 2)
real matrix in downstream theorems. -/
noncomputable def laplacianBlock (mobius : Bool) :
    Matrix G.V G.V (Matrix (Fin 2) (Fin 2) ℝ) :=
  G.degreeBlockMatrix - G.adjacencyMatrix mobius

/-- Flatten the block structure to a real matrix on V × Fin 2. -/
noncomputable def laplacian (mobius : Bool) :
    Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ :=
  fun (u, i) (v, j) => (G.laplacianBlock mobius u v) i j

/-- The edgeMatrix is symmetric: both σx and I₂ equal their transpose pointwise. -/
private lemma edgeMatrix_symm (mobius : Bool) (e : G.graph.edgeSet) (i j : Fin 2) :
    G.edgeMatrix mobius e i j = G.edgeMatrix mobius e j i := by
  unfold edgeMatrix
  split_ifs with h
  · -- σx branch
    fin_cases i <;> fin_cases j <;> simp [σx]
  · -- I₂ branch
    fin_cases i <;> fin_cases j <;> simp [I₂]

/-- The Laplacian is symmetric (real-symmetric, hence self-adjoint). -/
theorem laplacian_symmetric (mobius : Bool) :
    (G.laplacian mobius).IsSymm := by
  apply Matrix.IsSymm.ext
  rintro ⟨v, j⟩ ⟨u, i⟩
  show G.laplacian mobius (u, i) (v, j) = G.laplacian mobius (v, j) (u, i)
  simp only [laplacian, laplacianBlock, degreeBlockMatrix, adjacencyMatrix,
             Matrix.sub_apply]
  by_cases huv : u = v
  · subst huv
    have hnoadj : ¬ G.graph.Adj u u := SimpleGraph.irrefl _
    simp only [if_true, hnoadj, dif_neg, not_false_eq_true,
               Matrix.zero_apply, sub_zero]
    fin_cases i <;> fin_cases j <;> simp [I₂]
  · have hvu : v ≠ u := Ne.symm huv
    simp only [if_neg huv, if_neg hvu, Matrix.zero_apply, zero_sub, neg_inj]
    by_cases hadj : G.graph.Adj u v
    · have hadjvu : G.graph.Adj v u := hadj.symm
      have hedge_eq :
          (⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩ :
              G.graph.edgeSet)
            = ⟨s(v, u), (SimpleGraph.mem_edgeSet G.graph).mpr hadjvu⟩ := by
        apply Subtype.ext; exact Sym2.eq_swap
      rw [dif_pos hadj, dif_pos hadjvu, hedge_eq]
      exact G.edgeMatrix_symm mobius _ i j
    · have hnadjvu : ¬ G.graph.Adj v u := fun h => hadj h.symm
      rw [dif_neg hadj, dif_neg hnadjvu]
      rfl

end ConnGraph

end ConnectionLaplacian
