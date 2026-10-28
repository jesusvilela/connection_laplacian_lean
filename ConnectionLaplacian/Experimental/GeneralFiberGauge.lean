import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Matrix.Basic

/-!
Arbitrary finite real fibers, not a disguised rank-two scalar cycle.

This is an experimental bridge for *noncommuting* matrix-valued
parallel transport. Gauge covariance is checked at the fiber level.
No holonomy or hardness claim follows without specifying a graph,
a representation, and an observable.
-/

namespace ConnectionLaplacian
namespace GeneralFiberGauge

open Matrix

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- A covariant difference in a fiber of arbitrary finite rank. -/
noncomputable def difference (U : Matrix F F ℝ)
    (x y : F → ℝ) : F → ℝ :=
  fun i => x i - (U.mulVec y) i

/-- Transport in two vertex frames. The order matters: there is no
commutativity hypothesis on the matrices. -/
noncomputable def inGauge (P Q U : Matrix F F ℝ) :
    Matrix F F ℝ :=
  P * U * Q.transpose

/-- Internal frame cancellation along a two-step path: a true
nonabelian transport identity, valid for every finite fiber rank. -/
theorem transport_composes_in_gauge (P Q T U W : Matrix F F ℝ)
    (hQ : Q.transpose * Q = 1) :
    inGauge P Q U * inGauge Q T W =
      inGauge P T (U * W) := by
  unfold inGauge
  calc
    (P * U * Q.transpose) * (Q * W * T.transpose) =
        P * U * (Q.transpose * Q) * W * T.transpose := by
          simp only [Matrix.mul_assoc]
    _ = P * (U * W) * T.transpose := by
          rw [hQ]
          simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- A matrix sends a difference of fiber sections to the
difference of their transported sections. -/
private theorem mulVec_sub (P : Matrix F F ℝ) (x y : F → ℝ) :
    P.mulVec (fun i => x i - y i) =
      fun i => (P.mulVec x) i - (P.mulVec y) i := by
  ext i
  simp [Matrix.mulVec, Matrix.dotProduct, Finset.sum_sub_distrib, mul_sub]

/-- Covariant differences transform at the source fiber.
In particular the intermediate vertex gauge cancels without
assuming either the edge transport or the gauge matrices commute. -/
theorem difference_gauge_covariant
    (P Q U : Matrix F F ℝ) (hQ : Q.transpose * Q = 1)
    (x y : F → ℝ) :
    difference (inGauge P Q U) (P.mulVec x) (Q.mulVec y) =
      P.mulVec (difference U x y) := by
  have hcancel : Q.transpose.mulVec (Q.mulVec y) = y := by
    rw [← Matrix.mulVec_mulVec, hQ]
    simp
  have htransport :
      (inGauge P Q U).mulVec (Q.mulVec y) =
        P.mulVec (U.mulVec y) := by
    unfold inGauge
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcancel]
  unfold difference
  rw [htransport, mulVec_sub]

end GeneralFiberGauge
end ConnectionLaplacian
