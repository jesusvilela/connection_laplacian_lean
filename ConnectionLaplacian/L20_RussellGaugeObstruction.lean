/-
L20: R17 covariance path-defect naturality and its rank invariant.

This is the REAL cross-covariance convention C_ij' = F_i C_ij F_j^T,
not an assumed transport rule for arbitrary GL(d) connection arrows.

Proved here: exact path-defect transport and rank invariance at any finite
index type. The complete whitened singular-value ORBIT classification has
a separate pen-and-paper SVD proof and is not claimed to be formalized here.

No matrix-valued factor-analysis identification, noisy-sample inference,
or exact R14/R15 equivalence is established by this module.
-/

import ConnectionLaplacian.L19_RussellMovingFrame
import Mathlib.Tactic

namespace ConnectionLaplacian
namespace RussellGaugeObstruction

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Four-edge covariance path defect for invertible C32. -/
noncomputable def obstruction
    (C12 C32 C34 C14 : Matrix n n ℝ) : Matrix n n ℝ :=
  C12 * C32⁻¹ * C34 - C14

/-- A single cross-covariance's local observation-frame transformation. -/
def changeCovariance
    (Fi : Matrix n n ℝ) (Cij : Matrix n n ℝ)
    (Fj : Matrix n n ℝ) : Matrix n n ℝ :=
  Fi * Cij * Fj.transpose

/-- The inverse of the transformed middle block, without presupposing
    that the whole transformed covariance system is factorable. -/
theorem inverse_middle_block
    (F2 F3 C32 : Matrix n n ℝ) :
    (changeCovariance F3 C32 F2)⁻¹ =
      (F2.transpose)⁻¹ * C32⁻¹ * F3⁻¹ := by
  simp only [changeCovariance, Matrix.mul_inv_rev]

/-- Under independent frames at all four sensors, all internal frames
    cancel in the path defect. No matrix commutation is used. -/
theorem obstruction_natural
    (C12 C32 C34 C14 F1 F2 F3 F4 : Matrix n n ℝ)
    (hF2 : IsUnit F2.det) (hF3 : IsUnit F3.det) :
    obstruction
      (changeCovariance F1 C12 F2)
      (changeCovariance F3 C32 F2)
      (changeCovariance F3 C34 F4)
      (changeCovariance F1 C14 F4)
      =
    changeCovariance F1 (obstruction C12 C32 C34 C14) F4 := by
  let B := F2.transpose
  have hBdet : IsUnit B.det := by
    simpa only [B, Matrix.det_transpose] using hF2
  have hB : B * B⁻¹ = (1 : Matrix n n ℝ) := Matrix.mul_nonsing_inv B hBdet
  have hF3inv : F3⁻¹ * F3 = (1 : Matrix n n ℝ) := Matrix.nonsing_inv_mul F3 hF3
  have hpath :
      (F1 * C12 * B) * (B⁻¹ * C32⁻¹ * F3⁻¹) * (F3 * C34 * F4.transpose) =
        F1 * C12 * C32⁻¹ * C34 * F4.transpose := by
    calc
      _ = F1 * C12 * (B * B⁻¹) * C32⁻¹ * (F3⁻¹ * F3) *
          C34 * F4.transpose := by noncomm_ring
      _ = F1 * C12 * C32⁻¹ * C34 * F4.transpose := by
        simp only [hB, hF3inv, Matrix.mul_one, Matrix.one_mul]
  simp only [obstruction, changeCovariance, inverse_middle_block]
  dsimp [changeCovariance] at hpath
  rw [hpath]
  noncomm_ring

/-- The rank is invariant under invertible endpoint observation frames.
    The internal frames play no role after naturality is established. -/
theorem rank_covariant
    (R F1 F4 : Matrix n n ℝ)
    (hF1 : IsUnit F1.det) (hF4 : IsUnit F4.det) :
    (changeCovariance F1 R F4).rank = R.rank := by
  have hF4T : IsUnit F4.transpose.det := by
    simpa only [Matrix.det_transpose] using hF4
  unfold changeCovariance
  calc
    (F1 * R * F4.transpose).rank =
      (F1 * R).rank := Matrix.rank_mul_eq_left_of_isUnit_det
        F4.transpose (F1 * R) hF4T
    _ = R.rank := Matrix.rank_mul_eq_right_of_isUnit_det F1 R hF1

/-- Rank invariant of the four-edge obstruction, valid for arbitrary
    finite-dimensional matrix size n, including n = 1. -/
theorem obstruction_rank_invariant
    (C12 C32 C34 C14 F1 F2 F3 F4 : Matrix n n ℝ)
    (hF1 : IsUnit F1.det) (hF2 : IsUnit F2.det)
    (hF3 : IsUnit F3.det) (hF4 : IsUnit F4.det) :
    (obstruction
      (changeCovariance F1 C12 F2)
      (changeCovariance F3 C32 F2)
      (changeCovariance F3 C34 F4)
      (changeCovariance F1 C14 F4)).rank =
    (obstruction C12 C32 C34 C14).rank := by
  rw [obstruction_natural C12 C32 C34 C14 F1 F2 F3 F4 hF2 hF3]
  exact rank_covariant (obstruction C12 C32 C34 C14) F1 F4 hF1 hF4

end RussellGaugeObstruction
end ConnectionLaplacian
