/- 
L31: Dimensional Becoming

This file treats dimension as a structural invariant of a presentation,
rather than as a fixed ambient axis.
-/

import Mathlib

namespace ConnectionLaplacian

/-- A dimensional presentation is a finite carrier equipped with a relation. -/
structure DimensionalPresentation (α : Type) [Fintype α] where
  relation : α → α → Prop

/-- Relational dimension is the size of the structural presentation carrier. -/
def relationalDimension {α : Type} [Fintype α] (_ : DimensionalPresentation α) : ℕ :=
  Fintype.card α

/-- An invariance-preserving map between two dimensional presentations. -/
structure DimensionalBecoming {α β : Type} [Fintype α] [Fintype β]
    (P : DimensionalPresentation α) (Q : DimensionalPresentation β) where
  equiv : α ≃ β
  preserves : ∀ x y, P.relation x y ↔ Q.relation (equiv x) (equiv y)

/-- Dimensional becoming preserves relational dimension. -/
theorem dimensional_becoming_invariant {α β : Type} [Fintype α] [Fintype β]
    {P : DimensionalPresentation α} {Q : DimensionalPresentation β}
    (h : DimensionalBecoming P Q) :
    relationalDimension P = relationalDimension Q := by
  simpa [relationalDimension] using (Fintype.card_congr h.equiv)

/-- The 360-level root of the tower is dimensionally rigid under becoming. -/
theorem dimensional_becoming_360_root
    {P Q : DimensionalPresentation (Fin 360)}
    (h : DimensionalBecoming P Q) :
    relationalDimension P = relationalDimension Q := by
  exact dimensional_becoming_invariant h

/-- A 360-carrier presentation has relational dimension 360. -/
theorem relational_dimension_fin_360 (P : DimensionalPresentation (Fin 360)) :
    relationalDimension P = 360 := by
  simp [relationalDimension]

/-- The relation itself is preserved under the becoming equivalence. -/
theorem dimensional_becoming_relation {α β : Type} [Fintype α] [Fintype β]
    {P : DimensionalPresentation α} {Q : DimensionalPresentation β}
    (h : DimensionalBecoming P Q) (x y : α) :
    P.relation x y ↔ Q.relation (h.equiv x) (h.equiv y) :=
  h.preserves x y

end ConnectionLaplacian
