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

/-- In the pinned Mathlib/Lean v4.11 toolchain, define matrix rank via
    the finrank of the image of the corresponding linear map. -/
noncomputable def observableRank (R : Matrix n n ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.range (Matrix.toLin' R))

private theorem rank_left_invariant (R F : Matrix n n ℝ)
    (hF : IsUnit F.det) :
    observableRank (F * R) = observableRank R := by
  have hUnit : IsUnit F := (Matrix.isUnit_iff_isUnit_det).2 hF
  have hinj : Function.Injective (Matrix.toLin' F) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hUnit
  unfold observableRank
  rw [Matrix.toLin'_mul, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective (Matrix.toLin' F) hinj
    (LinearMap.range (Matrix.toLin' R))).finrank_eq.symm

private theorem rank_right_invariant (R F : Matrix n n ℝ)
    (hF : IsUnit F.det) :
    observableRank (R * F) = observableRank R := by
  have hUnit : IsUnit F := (Matrix.isUnit_iff_isUnit_det).2 hF
  have hsur : Function.Surjective (Matrix.toLin' F) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hUnit
  have heq :
      LinearMap.range (Matrix.toLin' (R * F)) =
        LinearMap.range (Matrix.toLin' R) := by
    ext y
    simp only [Matrix.toLin'_mul, LinearMap.mem_range, LinearMap.comp_apply]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(Matrix.toLin' F) x, hx⟩
    · rintro ⟨x, hx⟩
      rcases hsur x with ⟨z, hz⟩
      exact ⟨z, by simpa only [hz] using hx⟩
  exact congrArg (Module.finrank ℝ) heq

/-- The image dimension is invariant under invertible endpoint observation
    frames. This is precisely ordinary matrix rank over ℝ. -/
theorem rank_covariant
    (R F1 F4 : Matrix n n ℝ)
    (hF1 : IsUnit F1.det) (hF4 : IsUnit F4.det) :
    observableRank (changeCovariance F1 R F4) = observableRank R := by
  have hF4T : IsUnit F4.transpose.det := by
    simpa only [Matrix.det_transpose] using hF4
  unfold changeCovariance
  calc
    observableRank (F1 * R * F4.transpose) =
      observableRank (F1 * R) := rank_right_invariant (F1 * R) F4.transpose hF4T
    _ = observableRank R := rank_left_invariant R F1 hF1

/-- Rank invariant of the four-edge obstruction, valid for arbitrary finite
    index types (including one-dimensional matrices). -/
theorem obstruction_rank_invariant
    (C12 C32 C34 C14 F1 F2 F3 F4 : Matrix n n ℝ)
    (hF1 : IsUnit F1.det) (hF2 : IsUnit F2.det)
    (hF3 : IsUnit F3.det) (hF4 : IsUnit F4.det) :
    observableRank (obstruction
      (changeCovariance F1 C12 F2)
      (changeCovariance F3 C32 F2)
      (changeCovariance F3 C34 F4)
      (changeCovariance F1 C14 F4)) =
    observableRank (obstruction C12 C32 C34 C14) := by
  rw [obstruction_natural C12 C32 C34 C14 F1 F2 F3 F4 hF2 hF3]
  exact rank_covariant (obstruction C12 C32 C34 C14) F1 F4 hF1 hF4

end RussellGaugeObstruction
end ConnectionLaplacian
