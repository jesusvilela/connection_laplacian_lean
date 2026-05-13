/- 
L37: Center Fold

Formalizes a minimal finite model of the statement:
"All cardinal directions fold back to the center."
-/

import ConnectionLaplacian.L36_DimensionsBecoming

namespace ConnectionLaplacian

/-- Four cardinal directions. -/
inductive CardinalDirection where
  | north
  | south
  | east
  | west
  deriving DecidableEq, Repr, Fintype

/-- A finite center-fold system: every direction folds to `center`. -/
structure FiniteCenterFold (α : Type) [Fintype α] where
  center : α
  fold : CardinalDirection → α
  fold_center : ∀ d, fold d = center

/-- Minimal singleton center-fold model. -/
def singletonCenterFold : FiniteCenterFold (Fin 1) where
  center := 0
  fold := fun _ => 0
  fold_center := by
    intro d
    cases d <;> rfl

/-- Cardinal-direction fold map always lands at center. -/
theorem cardinal_fold_lands_at_center
    (d : CardinalDirection) :
    singletonCenterFold.fold d = singletonCenterFold.center := by
  exact singletonCenterFold.fold_center d

/-- Center stability under dimension-preserving becoming on the singleton carrier. -/
theorem center_stability_under_dimensions_becoming
    {P Q : DimensionalPresentation (Fin 1)}
    (h : DimensionsBecoming P Q) :
    relationalDimension P = relationalDimension Q ∧
      h.equiv singletonCenterFold.center = singletonCenterFold.center := by
  refine ⟨dimensions_becoming_invariant h, ?_⟩
  exact Fin.eq_zero (h.equiv singletonCenterFold.center)

/-- Fold invariance under equivalence/isomorphism of center-fold systems. -/
theorem fold_invariant_under_equiv
    {α β : Type} [Fintype α] [Fintype β]
    (F : FiniteCenterFold α) (G : FiniteCenterFold β)
    (e : α ≃ β)
    (hfold : ∀ d, e (F.fold d) = G.fold d)
    (d : CardinalDirection) :
    e (F.fold d) = G.center := by
  calc
    e (F.fold d) = G.fold d := hfold d
    _ = G.center := G.fold_center d

end ConnectionLaplacian
