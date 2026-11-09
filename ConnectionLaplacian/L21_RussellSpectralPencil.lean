/-
L21: R17 spectral pencil covariance under independent observation frames.

The matrix B := V4^-1 * R^T * V1^-1 * R transforms by similarity
under independently moving local frames. This algebraic result does not
require positivity; interpreting its eigenvalues as squared whitened
singular values DOES require SPD endpoint covariances.

Mathematical scope: characteristic polynomial of the ENDPOINT pencil,
not the classification of the complete graph covariance orbit.
-/
import ConnectionLaplacian.L20_RussellGaugeObstruction
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace ConnectionLaplacian
namespace RussellGaugeObstruction

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The right-endpoint inverse-metric Gram endomorphism.
    On SPD endpoints, its eigenvalues are squared singular values of the
    whitened residual, counted with multiplicity. -/
noncomputable def spectralPencil
    (V1 V4 R : Matrix n n ℝ) : Matrix n n ℝ :=
  V4⁻¹ * R.transpose * V1⁻¹ * R

/-- Full local-frame covariance of the spectral pencil,
    a similarity at the RIGHT observation endpoint. -/
theorem spectralPencil_covariant
    (V1 V4 R F1 F4 : Matrix n n ℝ)
    (hF1 : IsUnit F1.det) (hF4 : IsUnit F4.det) :
    spectralPencil
      (changeCovariance F1 V1 F1)
      (changeCovariance F4 V4 F4)
      (changeCovariance F1 R F4) =
    (F4.transpose)⁻¹ * spectralPencil V1 V4 R * F4.transpose := by
  have hF4inv : F4⁻¹ * F4 = (1 : Matrix n n ℝ) :=
    Matrix.nonsing_inv_mul F4 hF4
  have hF1inv : F1⁻¹ * F1 = (1 : Matrix n n ℝ) :=
    Matrix.nonsing_inv_mul F1 hF1
  have hF1trans : IsUnit F1.transpose.det := by
    simpa only [Matrix.det_transpose] using hF1
  have hF1tinv : F1.transpose * (F1.transpose)⁻¹ = (1 : Matrix n n ℝ) :=
    Matrix.mul_nonsing_inv F1.transpose hF1trans
  unfold spectralPencil changeCovariance
  simp only [Matrix.mul_inv_rev, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  calc
    _ = (F4.transpose)⁻¹ * V4⁻¹ * (F4⁻¹ * F4) * R.transpose *
      (F1.transpose * (F1.transpose)⁻¹) * V1⁻¹ *
      (F1⁻¹ * F1) * R * F4.transpose := by noncomm_ring
    _ = (F4.transpose)⁻¹ * (V4⁻¹ * R.transpose * V1⁻¹ * R) *
      F4.transpose := by
        simp only [hF4inv, hF1tinv, hF1inv,
          Matrix.one_mul, Matrix.mul_one]
        noncomm_ring

/-- Over any invertible real matrix, similarity preserves the characteristic
    polynomial. Proof by polynomial-matrix conjugation and determinant. -/
theorem charpoly_inverse_conjugate
    (A P : Matrix n n ℝ) (hP : IsUnit P.det) :
    (P⁻¹ * A * P).charpoly = A.charpoly := by
  let Q : Matrix n n ℝ[X] := (Polynomial.C : ℝ →+* ℝ[X]).mapMatrix P⁻¹
  let S : Matrix n n ℝ[X] := (Polynomial.C : ℝ →+* ℝ[X]).mapMatrix P
  have hQS : Q * S = 1 := by
    dsimp [Q, S]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul P hP]
    simp
  have hmap :
      (Polynomial.C : ℝ →+* ℝ[X]).mapMatrix (P⁻¹ * A * P) =
        Q * (Polynomial.C : ℝ →+* ℝ[X]).mapMatrix A * S := by
    dsimp [Q, S]
    rw [← Matrix.map_mul, ← Matrix.map_mul]
  have hcomm :
      (Matrix.scalar n (Polynomial.X : ℝ[X])) * Q =
        Q * (Matrix.scalar n (Polynomial.X : ℝ[X])) := by
    rw [Matrix.scalar_commute _ commute_X]
  have hscalar :
      Q * (Matrix.scalar n (Polynomial.X : ℝ[X])) * S =
        Matrix.scalar n (Polynomial.X : ℝ[X]) := by
    calc
      Q * (Matrix.scalar n (Polynomial.X : ℝ[X])) * S =
          ((Matrix.scalar n Polynomial.X) * Q) * S := by rw [hcomm]
      _ = Matrix.scalar n Polynomial.X * (Q * S) := by rw [Matrix.mul_assoc]
      _ = Matrix.scalar n Polynomial.X := by rw [hQS, Matrix.mul_one]
  have hcharmatrix :
      Matrix.charmatrix (P⁻¹ * A * P) =
        Q * Matrix.charmatrix A * S := by
    unfold Matrix.charmatrix
    rw [hmap]
    calc
      (Matrix.scalar n Polynomial.X) - (Q * (Polynomial.C : ℝ →+* ℝ[X]).mapMatrix A * S) =
          Q * (Matrix.scalar n Polynomial.X) * S -
            (Q * (Polynomial.C : ℝ →+* ℝ[X]).mapMatrix A * S) := by rw [hscalar]
      _ = Q * ((Matrix.scalar n Polynomial.X) -
          (Polynomial.C : ℝ →+* ℝ[X]).mapMatrix A) * S := by noncomm_ring
  calc
    (P⁻¹ * A * P).charpoly = (Matrix.charmatrix (P⁻¹ * A * P)).det := rfl
    _ = (Q * Matrix.charmatrix A * S).det := by rw [hcharmatrix]
    _ = Q.det * (Matrix.charmatrix A).det * S.det := by
      rw [Matrix.det_mul, Matrix.det_mul]
    _ = Q.det * S.det * (Matrix.charmatrix A).det := by ring
    _ = (Q * S).det * (Matrix.charmatrix A).det := by rw [Matrix.det_mul]
    _ = A.charpoly := by rw [hQS, Matrix.det_one, one_mul]; rfl

/-- The full characteristic polynomial of the covariance spectral pencil
    is invariant under independently moving endpoint frames. -/
theorem spectralPencil_charpoly_invariant
    (V1 V4 R F1 F4 : Matrix n n ℝ)
    (hF1 : IsUnit F1.det) (hF4 : IsUnit F4.det) :
    (spectralPencil
      (changeCovariance F1 V1 F1)
      (changeCovariance F4 V4 F4)
      (changeCovariance F1 R F4)).charpoly =
    (spectralPencil V1 V4 R).charpoly := by
  rw [spectralPencil_covariant V1 V4 R F1 F4 hF1 hF4]
  apply charpoly_inverse_conjugate
  simpa only [Matrix.det_transpose] using hF4

end RussellGaugeObstruction
end ConnectionLaplacian
