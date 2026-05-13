import Mathlib

namespace ConnectionLaplacian

/-- A finite relational presentation: a carrier equipped with a binary relation. -/
structure RelationalPresentation (α : Type*) [Fintype α] where
  relation : α → α → Prop

/-- The relational dimension is the size of the underlying carrier. -/
def relationalDimension {α : Type*} [Fintype α] (_ : RelationalPresentation α) : ℕ :=
  Fintype.card α

/-- An equivalence of presentations preserves the underlying relation. -/
structure PresentationEquiv {α β : Type*} [Fintype α] [Fintype β]
    (P : RelationalPresentation α) (Q : RelationalPresentation β) where
  equiv : α ≃ β
  preserves : ∀ x y, P.relation x y ↔ Q.relation (equiv x) (equiv y)

/-- Equivalent presentations have the same relational dimension. -/
theorem relationalDimension_eq {α β : Type*} [Fintype α] [Fintype β]
    {P : RelationalPresentation α} {Q : RelationalPresentation β}
    (h : PresentationEquiv P Q) :
    relationalDimension P = relationalDimension Q := by
  simpa [relationalDimension] using (Fintype.card_congr h.equiv)

/-- A linear equivalence preserves finrank, so dimension is functorial under isomorphism. -/
theorem finrank_eq_of_linearEquiv
    {R : Type*} [Ring R]
    {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module R E] [Module R F]
    (e : E ≃ₗ[R] F) :
    FiniteDimensional.finrank R E = FiniteDimensional.finrank R F := by
  exact LinearEquiv.finrank_eq e

end ConnectionLaplacian
