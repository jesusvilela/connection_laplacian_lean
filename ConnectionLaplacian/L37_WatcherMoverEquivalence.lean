/- 
L37: Watcher-Mover Equivalence

The watcher and mover are two chart views of one relational transition:
watching is relation-level equivalence, moving is forward/backward transport.
-/

import ConnectionLaplacian.L36_DimensionsBecoming

namespace ConnectionLaplacian

/-- A shared state transition between two finite relational presentations. -/
structure RelationalTransition (α β : Type) [Fintype α] [Fintype β] where
  source : DimensionalPresentation α
  target : DimensionalPresentation β
  becoming : DimensionalBecoming source target

variable {α β : Type} [Fintype α] [Fintype β]

/-- Watcher view: relation equivalence across the becoming chart. -/
def WatcherView (T : RelationalTransition α β) : Prop :=
  ∀ x y, T.source.relation x y ↔ T.target.relation (T.becoming.equiv x) (T.becoming.equiv y)

/-- Mover view: relation transport forward and backward along the transition. -/
def MoverView (T : RelationalTransition α β) : Prop :=
  (∀ x y, T.source.relation x y → T.target.relation (T.becoming.equiv x) (T.becoming.equiv y)) ∧
  (∀ u v, T.target.relation u v →
    T.source.relation (T.becoming.equiv.symm u) (T.becoming.equiv.symm v))

/-- Every becoming witness induces the watcher view. -/
theorem becoming_gives_watcher (T : RelationalTransition α β) : WatcherView T := by
  intro x y
  exact T.becoming.preserves x y

/-- Watcher view implies mover view. -/
theorem watcher_to_mover (T : RelationalTransition α β) :
    WatcherView T → MoverView T := by
  intro h
  constructor
  · intro x y hxy
    exact (h x y).mp hxy
  · intro u v huv
    have hs : T.source.relation (T.becoming.equiv.symm u) (T.becoming.equiv.symm v) :=
      (h (T.becoming.equiv.symm u) (T.becoming.equiv.symm v)).mpr (by simpa using huv)
    simpa using hs

/-- Mover view implies watcher view. -/
theorem mover_to_watcher (T : RelationalTransition α β) :
    MoverView T → WatcherView T := by
  intro h x y
  constructor
  · exact h.1 x y
  · intro hxy
    have hs : T.source.relation
        (T.becoming.equiv.symm (T.becoming.equiv x))
        (T.becoming.equiv.symm (T.becoming.equiv y)) :=
      h.2 (T.becoming.equiv x) (T.becoming.equiv y) hxy
    simpa using hs

/-- Watcher and mover are equivalent chart views of one transition. -/
theorem watcher_mover_equiv (T : RelationalTransition α β) :
    WatcherView T ↔ MoverView T := by
  constructor
  · exact watcher_to_mover T
  · exact mover_to_watcher T

end ConnectionLaplacian
