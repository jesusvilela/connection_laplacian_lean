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

end IndefiniteFiber
end ConnectionLaplacian
