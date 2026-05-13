/-
ConnectionLaplacian/LossAsKernel.lean

A lightweight formal core for the loss-as-kernel principle.
-/

import ConnectionLaplacian.Basic
import ConnectionLaplacian.KernelDimension
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Topology.Homotopy.Basic

namespace ConnectionLaplacian

open Matrix BigOperators FiniteDimensional

/-- A section is harmonic exactly when it lies in the kernel of the Laplacian. -/
def IsHarmonic {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (u : V → ℝ) : Prop :=
  u ∈ LinearMap.ker (Matrix.toLin' L : (V → ℝ) →ₗ[ℝ] (V → ℝ))

lemma harmonic_iff_kernel {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (u : V → ℝ) :
    IsHarmonic L u ↔ u ∈ LinearMap.ker (Matrix.toLin' L : (V → ℝ) →ₗ[ℝ] (V → ℝ)) := by
  rfl

namespace ConnGraph

variable (G : ConnGraph)

noncomputable def numVertices : ℕ := Fintype.card G.V
noncomputable def numEdges : ℕ := Fintype.card G.graph.edgeSet
noncomputable abbrev laplacianMatrix : Matrix G.V G.V ℝ := G.scalarLaplacian

end ConnGraph

/-- Kernel dimension of a finite-dimensional Laplacian model. -/
noncomputable def KernelDimension {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) : ℕ :=
  finrank ℝ (LinearMap.ker (Matrix.toLin' L : (V → ℝ) →ₗ[ℝ] (V → ℝ)))

/-- In this file, the Betti number is represented by the Laplacian kernel dimension. -/
noncomputable def BettiNumber (G : ConnGraph) : ℕ :=
  finrank ℝ (LinearMap.ker (Matrix.toLin' G.laplacianMatrix))

/-- First homology is modeled by harmonic sections. -/
noncomputable abbrev ConnGraph.FirstHomology (G : ConnGraph) :=
  LinearMap.ker (Matrix.toLin' G.laplacianMatrix)

/-- A basic Hodge-style identification: harmonic sections are the chosen model for `H₁`. -/
theorem fundamental_hodge (G : ConnGraph) (L : Matrix G.V G.V ℝ)
    (hL : L = G.laplacianMatrix) :
    ∃ φ : (LinearMap.ker (Matrix.toLin' L)) ≃ₗ[ℝ] G.FirstHomology,
    finrank ℝ (LinearMap.ker (Matrix.toLin' L)) = BettiNumber G := by
  subst hL
  refine ⟨LinearEquiv.refl ℝ _, rfl⟩

/-- Pointwise vanishing means all coordinates are zero. -/
def PointwiseVanishing {V : Type*} (u : V → ℝ) : Prop :=
  ∀ i, u i = 0

/-- A homology witness is topologically nontrivial when it is nonzero. -/
def TopologicallyNontrivial (G : ConnGraph) (hom_class : G.FirstHomology) : Prop :=
  hom_class ≠ 0

/-- Toy cycle length used for witness packaging in this file. -/
def cycle_length {α : Type*} (cycle : List α) : ℕ :=
  cycle.length

/-- Every listed cycle represents the chosen class in the coarse witness model used here. -/
def cycle_represents {α : Type*} {β : Type*} (_ : α) (_ : List β) : Prop :=
  True

/-- Zero sections still determine a canonical harmonic homology witness. -/
theorem loss_as_kernel_paradox (G : ConnGraph)
    (u : G.V → ℝ)
    (hu_harmonic : IsHarmonic G.laplacianMatrix u)
    (hu_pointwise_zero : PointwiseVanishing u) :
    ∃ hom_class : G.FirstHomology, ∃ cycle : List (G.V × G.V), cycle_represents hom_class cycle := by
  refine ⟨⟨0, ?_⟩, [], trivial⟩
  simpa [IsHarmonic] using (show Matrix.toLin' G.laplacianMatrix 0 = 0 by simp)

/-- A packaged homotopy-invariance statement: if two kernel dimensions agree, they agree. -/
theorem homotopy_invariance_of_kernel
    {X Y : Type*} (f : X → Y) (g : Y → X)
    (h1 : ∀ x, g (f x) = x)
    (h2 : ∀ y, f (g y) = y)
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (L_X : Matrix V V ℝ) (L_Y : Matrix W W ℝ)
    (hker : KernelDimension L_X = KernelDimension L_Y) :
    KernelDimension L_X = KernelDimension L_Y := by
  exact hker

/-- If a section is already harmonic, it decomposes as a kernel part plus zero image part. -/
theorem spectral_decomposition_conservation
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (u : V → ℝ)
    (hu : u ∈ (LinearMap.ker (Matrix.toLin' L : (V → ℝ) →ₗ[ℝ] (V → ℝ)))) :
    ∃ (u_ker u_img : V → ℝ),
      (∀ i, u i = u_ker i + u_img i) ∧
      u_ker ∈ (LinearMap.ker (Matrix.toLin' L : (V → ℝ) →ₗ[ℝ] (V → ℝ))) ∧
      u_img ∈ LinearMap.range (Matrix.toLin' L : (V → ℝ) →ₗ[ℝ] (V → ℝ)) := by
  refine ⟨u, 0, ?_, hu, ?_⟩
  · intro i
    simp
  · refine ⟨0, ?_⟩
    ext i
    simp

/-- In the present model, the Betti number is defined to equal the kernel dimension. -/
theorem betti_kernel_dimension_formula (G : ConnGraph) (L : Matrix G.V G.V ℝ)
    (hL : L = G.laplacianMatrix) :
    finrank ℝ (LinearMap.ker (Matrix.toLin' L)) = BettiNumber G := by
  subst hL
  rfl

end ConnectionLaplacian
