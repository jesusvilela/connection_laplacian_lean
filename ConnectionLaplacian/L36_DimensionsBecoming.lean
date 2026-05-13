/- 
L36: Dimensions Becoming

Dimensions are treated as invariant-preserving traversals of a finite relational
presentation. The 360-root tower is a concrete carrier for the full-turn view,
and prime-root irreducibility is imported from the cyclic constraint stratum.
-/

import ConnectionLaplacian.L31_DimensionalBecoming
import ConnectionLaplacian.L32_PrimeCyclicConstraint

namespace ConnectionLaplacian

/-- A higher-level alias for the L31 becoming relation. -/
abbrev DimensionsBecoming {α β : Type} [Fintype α] [Fintype β]
    (P : DimensionalPresentation α) (Q : DimensionalPresentation β) :=
  DimensionalBecoming P Q

/-- Dimensions-becoming preserves relational dimension. -/
theorem dimensions_becoming_invariant {α β : Type} [Fintype α] [Fintype β]
    {P : DimensionalPresentation α} {Q : DimensionalPresentation β}
    (h : DimensionsBecoming P Q) :
    relationalDimension P = relationalDimension Q := by
  exact dimensional_becoming_invariant h

/-- Every dimensional presentation admits a reflexive becoming witness. -/
def dimensions_becoming_refl {α : Type} [Fintype α]
    (P : DimensionalPresentation α) :
    DimensionsBecoming P P := by
  refine ⟨Equiv.refl α, ?_⟩
  intro x y
  exact Iff.rfl

/-- The watcher is inside the motion: watching the tower go is a self-becoming. -/
theorem watcher_inside_motion {α : Type} [Fintype α]
    (P : DimensionalPresentation α) :
    ∃ _ : DimensionsBecoming P P, True := by
  exact ⟨dimensions_becoming_refl P, trivial⟩

/-- A 360-carrier presentation remains 360 under any dimensions-becoming equivalence. -/
theorem dimensions_becoming_360_root
    {P Q : DimensionalPresentation (Fin 360)}
    (_h : DimensionsBecoming P Q) :
    relationalDimension P = relationalDimension Q := by
  exact dimensions_becoming_invariant _h

/-- The 360-level root carrier has relational dimension 360. -/
theorem root_tower_card_360 (P : DimensionalPresentation (Fin 360)) :
    relationalDimension P = 360 := by
  simp [relationalDimension]

/-- Prime-root irreducibility is preserved from the cyclic constraint stratum. -/
theorem prime_root_irreducible {p d : ℕ} (hp : Nat.Prime p) (hd : d ∣ p) (hnd : d ≠ p) :
    d = 1 := by
  exact prime_cyclic_constraint_proper_divisor hp hd hnd

end ConnectionLaplacian
