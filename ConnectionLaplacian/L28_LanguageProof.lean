/-
L28: Language-as-Proof Stratum
"To speak is to let the river find a mouth." — J. Vilela
© 2025 Jesús Vilela. MIT License.
-/

import Mathlib
import ConnectionLaplacian.L27_Holoportation

namespace ConnectionLaplacian

universe u

/-- A type-theory term viewed as a hyperbolic geodesic issuing from the stratum `T`. -/
structure LanguageTerm (T : Type u) where
  geodesic : T

/-- The starting stratum of a language term is its ambient type. -/
abbrev startingStratum (T : Type u) : Type u := T

/-- In the L28 scaffold, a geodesic is just an inhabited path through the stratum `T`. -/
abbrev HyperdimGeodesic (T : Type u) : Type u := LanguageTerm T

/-- Proposition-level geodesics are lifted into `Type` to expose Curry-Howard data. -/
abbrev ProofGeodesic (T : Prop) : Type := LanguageTerm (PLift T)

/-- The holonomy of the geodesic is the witness that the term inhabits its type. -/
def holonomyWitness {T : Type u} (γ : HyperdimGeodesic T) : T :=
  γ.geodesic

/-- Every term is equivalent to its geodesic presentation in the n-cosmos. -/
def languageTermEquiv (T : Type u) : HyperdimGeodesic T ≃ T where
  toFun := holonomyWitness
  invFun := LanguageTerm.mk
  left_inv γ := by
    cases γ
    rfl
  right_inv t := by
    rfl

/-- Recasting a term as a geodesic and back leaves its holonomy unchanged. -/
@[simp] theorem holonomyWitness_mk {T : Type u} (t : T) :
    holonomyWitness (LanguageTerm.mk t) = t := rfl

/--
L28 theorem: for propositions, language, proof, and hyperbolic transformation coincide.
A proof of `T` is exactly a geodesic whose holonomy lands in the stratum `T`.
-/
theorem L28_curry_howard_hyperdim (T : Prop) : Nonempty (ProofGeodesic T) ↔ T := by
  constructor
  · intro h
    rcases h with ⟨γ⟩
    exact γ.geodesic.down
  · intro h
    exact ⟨LanguageTerm.mk ⟨h⟩⟩

/-- Type-level version of L28: every term `t : T` determines a unique geodesic witness. -/
theorem term_encodes_geodesic (T : Type u) (t : T) :
    ∃! γ : HyperdimGeodesic T, holonomyWitness γ = t := by
  refine ⟨LanguageTerm.mk t, rfl, ?_⟩
  intro γ hγ
  cases γ
  simp at hγ
  cases hγ
  rfl

/-- Language = proof = transformation, expressed as an equivalence of data. -/
def language_proof_transformation (T : Type u) : HyperdimGeodesic T ≃ startingStratum T :=
  languageTermEquiv T

end ConnectionLaplacian
