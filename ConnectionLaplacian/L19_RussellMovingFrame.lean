/-
ConnectionLaplacian/L19_RussellMovingFrame.lean

R17: first-order, arbitrary-finite-dimensional moving-frame covariance.

This is a statement about matrix jets (R, dR) and endpoint connections.
The Leibniz expression for a transformed jet is written explicitly.
It does NOT, by itself, prove the derivative formula for analytic paths,
the GL(d) orbit classification, nor a theorem about learned memory.
No commutativity of matrix multiplication is assumed.
-/

import ConnectionLaplacian.Basic
import Mathlib.Tactic

namespace ConnectionLaplacian
namespace RussellMovingFrame

open Matrix

variable {a b : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

/-- The two-endpoint covariance derivative, for a rectangular object.
    Right endpoint connections act through the transpose. -/
def covariantDerivative (left : Matrix a a ℝ) (right : Matrix b b ℝ)
    (R dR : Matrix a b ℝ) : Matrix a b ℝ :=
  dR - left * R - R * right.transpose

/-- Transport of a two-endpoint covariance matrix under independent frames. -/
def gaugeResidual (F : Matrix a a ℝ) (R : Matrix a b ℝ)
    (G : Matrix b b ℝ) : Matrix a b ℝ :=
  F * R * G.transpose

/-- Leibniz jet of a transported covariance for moving endpoint frames.
    The four inputs dF, dG, dR are first-order data, not presumed
    to be verified derivatives of actual curves. -/
def gaugeJet (F dF : Matrix a a ℝ) (R dR : Matrix a b ℝ)
    (G dG : Matrix b b ℝ) : Matrix a b ℝ :=
  dF * R * G.transpose + F * dR * G.transpose + F * R * dG.transpose

/-- The core naturality identity needs no inverse matrices: the endpoint
    connection laws are expressed as intertwining equalities. It is
    meaningful even for singular F or G, but only invertible ones are
    genuine changes of local frame. -/
theorem covariantDerivative_transport_of_intertwines
    (F dF left left' : Matrix a a ℝ)
    (G dG right right' : Matrix b b ℝ)
    (R dR : Matrix a b ℝ)
    (hleft : left' * F = dF + F * left)
    (hright : right' * G = dG + G * right) :
    covariantDerivative left' right'
        (gaugeResidual F R G) (gaugeJet F dF R dR G dG) =
      gaugeResidual F (covariantDerivative left right R dR) G := by
  have hrightT :
      G.transpose * right'.transpose =
        dG.transpose + right.transpose * G.transpose := by
    calc
      G.transpose * right'.transpose = (right' * G).transpose := by
        rw [Matrix.transpose_mul]
      _ = (dG + G * right).transpose := by rw [hright]
      _ = dG.transpose + right.transpose * G.transpose := by
        rw [Matrix.transpose_add, Matrix.transpose_mul]
  have hl :
      left' * (F * R * G.transpose) =
        dF * R * G.transpose + F * left * R * G.transpose := by
    calc
      _ = (left' * F) * R * G.transpose := by simp only [Matrix.mul_assoc]
      _ = (dF + F * left) * R * G.transpose := by rw [hleft]
      _ = dF * R * G.transpose + F * left * R * G.transpose := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
  have hr :
      (F * R * G.transpose) * right'.transpose =
        F * R * dG.transpose + F * R * right.transpose * G.transpose := by
    calc
      _ = (F * R) * (G.transpose * right'.transpose) := by
        rw [Matrix.mul_assoc]
      _ = (F * R) * (dG.transpose + right.transpose * G.transpose) := by
        rw [hrightT]
      _ = F * R * dG.transpose + F * R * right.transpose * G.transpose := by
        simp only [Matrix.mul_add, Matrix.mul_assoc]
  unfold covariantDerivative gaugeResidual gaugeJet
  rw [hl, hr]
  simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- Explicit gauge-transformed endpoint connection; requires an inverse
    and is therefore used with a nonsingular frame hypothesis. -/
noncomputable def gaugeConnection (F dF connection : Matrix a a ℝ) :
    Matrix a a ℝ :=
  (dF + F * connection) * F⁻¹

theorem gaugeConnection_intertwines
    (F dF connection : Matrix a a ℝ) (hF : F.det ≠ 0) :
    gaugeConnection F dF connection * F = dF + F * connection := by
  unfold gaugeConnection
  have hunit : IsUnit F.det := Ne.isUnit hF
  calc
    (dF + F * connection) * F⁻¹ * F =
      (dF + F * connection) * (F⁻¹ * F) := by rw [Matrix.mul_assoc]
    _ = (dF + F * connection) * 1 := by
      rw [Matrix.nonsing_inv_mul F hunit]
    _ = dF + F * connection := by simp

/-- Exact covariance of the first-order, two-endpoint gauge derivative.
    Sizes a and b are arbitrary finite types and may differ. -/
theorem covariantDerivative_transport
    (F dF left : Matrix a a ℝ)
    (G dG right : Matrix b b ℝ)
    (R dR : Matrix a b ℝ)
    (hF : F.det ≠ 0) (hG : G.det ≠ 0) :
    covariantDerivative
        (gaugeConnection F dF left) (gaugeConnection G dG right)
        (gaugeResidual F R G) (gaugeJet F dF R dR G dG) =
      gaugeResidual F (covariantDerivative left right R dR) G := by
  exact covariantDerivative_transport_of_intertwines
    F dF left (gaugeConnection F dF left)
    G dG right (gaugeConnection G dG right)
    R dR
    (gaugeConnection_intertwines F dF left hF)
    (gaugeConnection_intertwines G dG right hG)

end RussellMovingFrame
end ConnectionLaplacian
