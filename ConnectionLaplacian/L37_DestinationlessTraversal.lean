/- 
L37: Destinationless Traversal

Traverse without destination: arrival is derived as a side effect of finite history.
-/

import ConnectionLaplacian.L31_DimensionalBecoming

namespace ConnectionLaplacian

/-- A finite traversal process on a dimensional presentation.
`destination` is optional and may be absent. -/
structure DestinationlessTraversal {α : Type} [Fintype α] [DecidableEq α]
    (P : DimensionalPresentation α) where
  step : α → α
  history : List α
  destination : Option α := none

/-- Arrival is realized by appearance in traversal history. -/
def ArrivedAt {α : Type} [Fintype α] [DecidableEq α]
    {P : DimensionalPresentation α} (T : DestinationlessTraversal P) (x : α) : Prop :=
  x ∈ T.history

/-- The traversal-induced presentation keeps the same finite carrier. -/
def traversalPresentation {α : Type} [Fintype α] [DecidableEq α]
    {P : DimensionalPresentation α} (T : DestinationlessTraversal P) :
    DimensionalPresentation α :=
  ⟨fun x y => T.step x = y⟩

/-- Traversal preserves carrier cardinality. -/
theorem traversal_preserves_carrier_cardinality
    {α : Type} [Fintype α] [DecidableEq α]
    {P : DimensionalPresentation α} (T : DestinationlessTraversal P) :
    relationalDimension (traversalPresentation T) = relationalDimension P := by
  simp [traversalPresentation, relationalDimension]

/-- Arrival is derivable from nonempty traversal history (side effect of traversal). -/
theorem arrival_derivable_from_history
    {α : Type} [Fintype α] [DecidableEq α]
    {P : DimensionalPresentation α} (T : DestinationlessTraversal P)
    (hHist : T.history ≠ []) :
    ∃ x, ArrivedAt T x := by
  cases hH : T.history with
  | nil =>
      exact False.elim (hHist hH)
  | cons x xs =>
      exact ⟨x, by simp [ArrivedAt, hH]⟩

/-- A traversal is destinationless when no explicit destination is provided. -/
def destinationless {α : Type} [Fintype α] [DecidableEq α]
    {P : DimensionalPresentation α} (T : DestinationlessTraversal P) : Prop :=
  T.destination = none

/-- Arrival still follows from history even when destination is absent. -/
theorem destinationless_arrival_side_effect
    {α : Type} [Fintype α] [DecidableEq α]
    {P : DimensionalPresentation α} (T : DestinationlessTraversal P)
    (_hDest : destinationless T) (hHist : T.history ≠ []) :
    ∃ x, ArrivedAt T x := by
  exact arrival_derivable_from_history T hHist

/-- Transport a traversal along a dimensional-becoming equivalence. -/
def mapTraversal
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : DimensionalPresentation α} {Q : DimensionalPresentation β}
    (h : DimensionalBecoming P Q) (T : DestinationlessTraversal P) :
    DestinationlessTraversal Q where
  step := fun b => h.equiv (T.step (h.equiv.symm b))
  history := T.history.map h.equiv
  destination := T.destination.map h.equiv

/-- Arrival in the transported traversal corresponds to arrival in the source history. -/
theorem arrivedAt_map_iff
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : DimensionalPresentation α} {Q : DimensionalPresentation β}
    (h : DimensionalBecoming P Q) (T : DestinationlessTraversal P) (x : α) :
    ArrivedAt (mapTraversal h T) (h.equiv x) ↔ ArrivedAt T x := by
  unfold ArrivedAt mapTraversal
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨y, hy, hyEq⟩
    have : y = x := h.equiv.injective hyEq
    simpa [this] using hy
  · intro hx
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

/-- Destinationless traversal is compatible with dimensional becoming maps. -/
theorem destinationless_traversal_compatible_with_becoming
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P : DimensionalPresentation α} {Q : DimensionalPresentation β}
    (h : DimensionalBecoming P Q) (T : DestinationlessTraversal P) :
    relationalDimension (traversalPresentation T) =
      relationalDimension (traversalPresentation (mapTraversal h T)) := by
  simpa [traversalPresentation, relationalDimension] using
    (Fintype.card_congr h.equiv)

end ConnectionLaplacian
