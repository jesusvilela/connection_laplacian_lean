import Mathlib

namespace ConnectionLaplacian

open Real InnerProductSpace Set

/-- A stalk `F_x` is a finite-dimensional vector space at a point. -/
structure Stalk (𝕜 : Type*) [Field 𝕜] where
  fiber : Type*
  [add_comm_group : AddCommGroup fiber]
  [module : Module 𝕜 fiber]
  [fin_dim : FiniteDimensional 𝕜 fiber]

attribute [instance] Stalk.add_comm_group Stalk.module Stalk.fin_dim

/-- Dimension of a stalk. -/
noncomputable def Stalk.dimension {𝕜 : Type*} [Field 𝕜] (F_x : Stalk 𝕜) : ℕ :=
  FiniteDimensional.finrank 𝕜 F_x.fiber

/-- A stalk is trivial if it is zero-dimensional. -/
def Stalk.isTrivial {𝕜 : Type*} [Field 𝕜] (F_x : Stalk 𝕜) : Prop :=
  F_x.dimension = 0

/-- A stalk is nontrivial if it has dimension at least one. -/
def Stalk.isNontrivial {𝕜 : Type*} [Field 𝕜] (F_x : Stalk 𝕜) : Prop :=
  1 ≤ F_x.dimension

/-- Adequacy condition: the stalk dimension lies in a prescribed window. -/
def StalkAdequate {𝕜 : Type*} [Field 𝕜] (F_x : Stalk 𝕜) (d_min d_max : ℕ) : Prop :=
  d_min ≤ F_x.dimension ∧ F_x.dimension ≤ d_max

/-- All stalks in a family are adequately dimensioned. -/
def SheafAdequate {𝕜 : Type*} [Field 𝕜] {X : Type*}
    (F : X → Stalk 𝕜) (d_min d_max : ℕ) : Prop :=
  ∀ x : X, StalkAdequate (F x) d_min d_max

/-- A concrete global section: one vector in each stalk. -/
structure GlobalSections {𝕜 : Type*} [Field 𝕜] (X : Type*) (F : X → Stalk 𝕜) where
  values : ∀ x : X, (F x).fiber

/-- A global section is nontrivial if every component is nonzero. -/
def GlobalSections.isNontrivial {𝕜 : Type*} [Field 𝕜] {X : Type*} {F : X → Stalk 𝕜}
    (s : GlobalSections X F) : Prop :=
  ∀ x : X, s.values x ≠ 0

/-- Zeroth sheaf cohomology as the zero section in this toy model. -/
def SheafCohomology0 {𝕜 : Type*} [Field 𝕜] {X : Type*}
    (F : X → Stalk 𝕜) : GlobalSections X F :=
  ⟨fun x => 0⟩

lemma stalk_nontrivial_of_adequate {𝕜 : Type*} [Field 𝕜] {X : Type*}
    (F : X → Stalk 𝕜) {d_min d_max : ℕ}
    (h_adequate : ∀ x : X, StalkAdequate (F x) d_min d_max)
    (h_dmin : 1 ≤ d_min) :
    ∀ x : X, (F x).isNontrivial := by
  intro x
  exact le_trans h_dmin (h_adequate x).1

/-- Adequate stalks of positive minimal dimension admit a nontrivial global section. -/
theorem ExistenceTremblingAdequacy {𝕜 : Type*} [Field 𝕜] {X : Type*}
    (F : X → Stalk 𝕜) (d_min d_max : ℕ)
    (h_adequate : ∀ x : X, StalkAdequate (F x) d_min d_max)
    (h_dmin : 1 ≤ d_min) :
    ∃ s : GlobalSections X F, s.isNontrivial := by
  classical
  have h_nontrivial : ∀ x : X, (F x).isNontrivial :=
    stalk_nontrivial_of_adequate F h_adequate h_dmin
  have hne : ∀ x : X, ∃ v : (F x).fiber, v ≠ 0 := by
    intro x
    have hpos : 0 < FiniteDimensional.finrank 𝕜 (F x).fiber := by
      exact Nat.lt_of_lt_of_le (by omega) (h_nontrivial x)
    letI : Nontrivial (F x).fiber := FiniteDimensional.finrank_pos_iff.mp hpos
    exact exists_ne (0 : (F x).fiber)
  refine ⟨⟨fun x => Classical.choose (hne x)⟩, ?_⟩
  intro x
  exact Classical.choose_spec (hne x)

/-- A nontrivial global section forces each stalk to be nontrivial. -/
theorem AdequacyOfGlobalSections {𝕜 : Type*} [Field 𝕜] {X : Type*}
    (F : X → Stalk 𝕜)
    (h_sections : ∃ s : GlobalSections X F, s.isNontrivial) :
    ∀ x : X, (F x).isNontrivial := by
  intro x
  rcases h_sections with ⟨s, hs⟩
  letI : Nontrivial (F x).fiber := ⟨⟨s.values x, 0, hs x⟩⟩
  have hpos : 0 < FiniteDimensional.finrank 𝕜 (F x).fiber :=
    FiniteDimensional.finrank_pos_iff.mpr inferInstance
  exact Nat.succ_le_of_lt (by simpa [Stalk.dimension] using hpos)

/-- In the collapsed regime, positive global sections cannot exist. -/
theorem CollapsedImpliesNoSections {𝕜 : Type*} [Field 𝕜] {X : Type*}
    (F : X → Stalk 𝕜)
    (h_trivial : ∀ x : X, (F x).isTrivial)
    (h_nonempty : Nonempty X) :
    ¬(∃ s : GlobalSections X F, s.isNontrivial) := by
  rintro ⟨s, hs⟩
  rcases h_nonempty with ⟨x⟩
  have hfinrank : FiniteDimensional.finrank 𝕜 (F x).fiber = 0 := by
    simpa [Stalk.isTrivial, Stalk.dimension] using h_trivial x
  letI : Nontrivial (F x).fiber := ⟨⟨s.values x, 0, hs x⟩⟩
  have hpos : 0 < FiniteDimensional.finrank 𝕜 (F x).fiber :=
    FiniteDimensional.finrank_pos_iff.mpr inferInstance
  exact (Nat.ne_of_gt hpos) hfinrank

/-- If every stalk is nontrivial, then a nontrivial global section exists. -/
theorem NontrivialImpliesSections {𝕜 : Type*} [Field 𝕜] {X : Type*}
    (F : X → Stalk 𝕜)
    (h_nontrivial : ∀ x : X, (F x).isNontrivial) :
    ∃ s : GlobalSections X F, s.isNontrivial := by
  classical
  have hne : ∀ x : X, ∃ v : (F x).fiber, v ≠ 0 := by
    intro x
    have hpos : 0 < FiniteDimensional.finrank 𝕜 (F x).fiber := by
      exact Nat.lt_of_lt_of_le (by omega) (h_nontrivial x)
    letI : Nontrivial (F x).fiber := FiniteDimensional.finrank_pos_iff.mp hpos
    exact exists_ne (0 : (F x).fiber)
  refine ⟨⟨fun x => Classical.choose (hne x)⟩, ?_⟩
  intro x
  exact Classical.choose_spec (hne x)

/-- For `n`-cosmos, the adequacy window is `[1,n]`. -/
def NCosmoAdequacyThreshold (n : ℕ) : ℕ × ℕ :=
  (1, n)

/-- Adequate stalks on Euclidean `(n+1)`-space admit nontrivial global sections. -/
theorem NCosmoExistenceTheorem {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (F : EuclideanSpace ℝ (Fin (n + 1)) → Stalk 𝕜)
    (h_adequate : ∀ x, StalkAdequate (F x) 1 n) :
    ∃ s : GlobalSections (EuclideanSpace ℝ (Fin (n + 1))) F, s.isNontrivial := by
  exact ExistenceTremblingAdequacy F 1 n h_adequate (by simp)

/-- L30 coherence is pointwise nontriviality of the stalks. -/
def IsL30Coherent {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (F : EuclideanSpace ℝ (Fin (n + 1)) → Stalk 𝕜) : Prop :=
  ∀ x, (F x).isNontrivial

/-- Representability is equivalent to L30-coherence in this toy model. -/
theorem IGBundleRepresentability {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (F : EuclideanSpace ℝ (Fin (n + 1)) → Stalk 𝕜) :
    IsL30Coherent F ↔ ∃ s : GlobalSections (EuclideanSpace ℝ (Fin (n + 1))) F,
      s.isNontrivial := by
  constructor
  · intro h_coherent
    exact NontrivialImpliesSections F h_coherent
  · intro h_sections
    exact AdequacyOfGlobalSections F h_sections

lemma ExistenceTremblesAtAdequacy {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (F : EuclideanSpace ℝ (Fin (n + 1)) → Stalk 𝕜)
    (h_below : ∀ x, (F x).dimension = 0) :
    ¬(∃ s : GlobalSections (EuclideanSpace ℝ (Fin (n + 1))) F, s.isNontrivial) := by
  exact CollapsedImpliesNoSections F
    (fun x => by simpa [Stalk.isTrivial] using h_below x)
    ⟨0⟩

lemma ExistenceTremblesAboveAdequacy {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (F : EuclideanSpace ℝ (Fin (n + 1)) → Stalk 𝕜)
    (h_above : ∀ x, (F x).dimension ≥ 1) :
    ∃ s : GlobalSections (EuclideanSpace ℝ (Fin (n + 1))) F, s.isNontrivial := by
  apply NontrivialImpliesSections F
  intro x
  simpa [Stalk.isNontrivial] using h_above x

end ConnectionLaplacian
