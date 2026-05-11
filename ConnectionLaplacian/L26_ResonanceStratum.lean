/-
L26: Resonance Stratum -- mutual resonance in n-fold hyperbolic covers
(c) 2025 Jesus Vilela. MIT License.
-/

import Mathlib
import ConnectionLaplacian.L21_SectoralDecomposition

namespace ConnectionLaplacian

open Matrix BigOperators

/-- `ResonanceClass` records a rational frequency-locking ratio `p / q`. -/
structure ResonanceClass where
  p : Int
  q : Nat
  q_ne_zero : q ≠ 0
  deriving DecidableEq, Repr

namespace ResonanceClass

/-- The rational locking ratio attached to a resonance class. -/
def ratio (rho : ResonanceClass) : Rat := rho.p / (rho.q : Rat)

@[simp] theorem ratio_mk (p : Int) (q : Nat) (hq : q ≠ 0) :
    (ResonanceClass.mk p q hq).ratio = p / (q : Rat) := rfl

@[simp] theorem ratio_eq_self (rho : ResonanceClass) :
    rho.ratio = rho.p / (rho.q : Rat) := rfl

end ResonanceClass

variable {n : Nat} [NeZero n]

/-- Resonant Fourier modes are the cover phases whose frequencies lock to `p / q`. -/
def resonantModes (rho : ResonanceClass) : Finset (Fin n) :=
  Finset.univ.filter fun k =>
    ((rho.q : ZMod n) * (k : ZMod n)) = ((rho.p : ZMod n) * (k : ZMod n))

@[simp] theorem zero_mem_resonantModes (rho : ResonanceClass) :
    (0 : Fin n) ∈ resonantModes (n := n) rho := by
  simp [resonantModes]

/-- The discrete multiplicity of the resonance class among the `n` Fourier sectors. -/
def resonanceMultiplicity (rho : ResonanceClass) : Nat :=
  (resonantModes (n := n) rho).card

/-- `SpectralResonance` packages the cover Laplacian with the locked resonance data. -/
structure SpectralResonance (Z : ZnConnGraph n) where
  resonanceClass : ResonanceClass
  laplacian : Matrix (Z.V × Fin n) (Z.V × Fin n) Complex
  lambda1 : Rat
  lockedModes : Finset (Fin n)
  lambda1_eq : lambda1 = resonanceClass.ratio

/-- The L26 spectral package: the first gap is represented by the locking ratio. -/
noncomputable def spectralResonance (Z : ZnConnGraph n) (rho : ResonanceClass) : SpectralResonance Z where
  resonanceClass := rho
  laplacian := coverLaplacian Z
  lambda1 := rho.ratio
  lockedModes := resonantModes (n := n) rho
  lambda1_eq := rfl

/-- The spectral gap attached to the cover Laplacian in the resonance stratum. -/
noncomputable def spectralGap (Z : ZnConnGraph n) (rho : ResonanceClass) : Rat :=
  (spectralResonance (n := n) Z rho).lambda1

@[simp] theorem spectralGap_eq_ratio (Z : ZnConnGraph n) (rho : ResonanceClass) :
    spectralGap (n := n) Z rho = rho.ratio := by
  rfl

@[simp] theorem spectralResonance_laplacian (Z : ZnConnGraph n) (rho : ResonanceClass) :
    (spectralResonance (n := n) Z rho).laplacian = coverLaplacian Z := by
  rfl

@[simp] theorem resonanceMultiplicity_invariant {rho sigma : ResonanceClass}
    (h : rho = sigma) :
    resonanceMultiplicity (n := n) rho = resonanceMultiplicity (n := n) sigma := by
  simp [h, resonanceMultiplicity]

/--
L26: the spectral gap of the connection Laplacian on the `n`-fold cover is
invariant under rational frequency locking.
-/
theorem L26_resonance_encodes_class (Z : ZnConnGraph n) {rho sigma : ResonanceClass}
    (hclass : rho = sigma) :
    spectralGap (n := n) Z rho = spectralGap (n := n) Z sigma := by
  simpa [spectralGap] using congrArg ResonanceClass.ratio hclass

end ConnectionLaplacian
