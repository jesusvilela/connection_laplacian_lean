import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Matrix.Basic

/-!
An algebraic bridge to an arbitrary finite-dimensional, possibly indefinite
fiber metric. Unlike Hilbert-space/positive-energy Riesz theory, the
signature-(2,2) example below has timelike and spacelike directions.

Transport is a Q-isometry when U.transpose * Q * U = Q.
The theorem is valid for noncommuting transports, without reducing to
rank-one phase factors. It does *not* prove a hyperbolic geometry,
positivity, or a computational hardness claim.
-/

namespace ConnectionLaplacian
namespace IndefiniteFiber

open Matrix

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- The fiber form is preserved by U; Q may be indefinite or degenerate.
Only an explicitly nondegenerate, symmetric Q describes a pseudo-orthogonal
structure, and those additional hypotheses are not silently assumed. -/
def preservesForm (Q U : Matrix F F ℝ) : Prop :=
  U.transpose * Q * U = Q

/-- Form preservation is closed under ordered composition of transports,
regardless of whether the transports commute. -/
theorem preservesForm_mul (Q U W : Matrix F F ℝ)
    (hU : preservesForm Q U) (hW : preservesForm Q W) :
    preservesForm Q (U * W) := by
  unfold preservesForm at *
  calc
    (U * W).transpose * Q * (U * W) =
        W.transpose * (U.transpose * Q * U) * W := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
    _ = W.transpose * Q * W := by rw [hU]
    _ = Q := hW

/-- The identity transport preserves every form, including split ones. -/
theorem preservesForm_one (Q : Matrix F F ℝ) :
    preservesForm Q (1 : Matrix F F ℝ) := by
  simp [preservesForm]

/-- A concrete split form with signature (2,2). This is a *fiber form*,
not a two-dimensional scalar or a claim of curvature. -/
def split22 : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = j then (if i = 0 ∨ i = 1 then 1 else -1) else 0

theorem split22_positive_direction : split22 0 0 = 1 := by
  simp [split22]

theorem split22_negative_direction : split22 2 2 = -1 := by
  simp [split22]

/-- Heterogeneous metric transport: the three fibers need not have the
same rank, and their local bilinear forms need not be equal.

A rectangular U transports from the B-fiber into the A-fiber; W transports
from C into B. This is an implication under explicit compatibility laws,
not a claim that such maps exist for arbitrary dimensions or signatures. -/
theorem compatibleLocalForms_compose
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (QA : Matrix A A ℝ) (QB : Matrix B B ℝ) (QC : Matrix C C ℝ)
    (U : Matrix A B ℝ) (W : Matrix B C ℝ)
    (hU : U.transpose * QA * U = QB)
    (hW : W.transpose * QB * W = QC) :
    (U * W).transpose * QA * (U * W) = QC := by
  calc
    (U * W).transpose * QA * (U * W) =
        W.transpose * (U.transpose * QA * U) * W := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
    _ = W.transpose * QB * W := by rw [hU]
    _ = QC := hW

end IndefiniteFiber
end ConnectionLaplacian
