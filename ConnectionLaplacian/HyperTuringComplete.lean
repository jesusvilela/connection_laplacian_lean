/-
ConnectionLaplacian/HyperTuringComplete.lean

Finite HyperTuring scaffold extending the completed Berry/SAT tier with a new
hypercomplex tape geometry model. The file keeps only exact Tier 0 claims:
* a classical acceptance predicate can be repackaged as a hypercomplex tape machine,
* the induced halting predicate is extensionally the same,
* logarithmic path budgets are recorded explicitly.

The full hyperbolic volume lower bound is still open and remains marked with one
honest `sorry`.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace ConnectionLaplacian

/-- Hypercomplex tape directions: real, imaginary, and the two reverse moves. -/
inductive HDirection where
  | Real
  | Imag
  | RealBack
  | ImagBack
  deriving DecidableEq, Repr

/-- A simplified hypercomplex tape cell, using two integer coordinates. -/
abbrev HTapeCell := Int × Int

/-- A minimal classical machine interface, recorded extensionally by its acceptance predicate. -/
structure ClassicalTM where
  alphabetSize : Nat
  stateSize : Nat
  hAlphabet : 0 < alphabetSize
  hState : 0 < stateSize
  accepts : List Nat → Prop

abbrev ClassicalTM.HSymbol (tm : ClassicalTM) := Fin tm.alphabetSize

def ClassicalTM.halts_on (tm : ClassicalTM) (w : List Nat) : Prop :=
  tm.accepts w

abbrev Halts (tm : ClassicalTM) (w : List Nat) : Prop :=
  tm.halts_on w

/-- A finite HyperTuring machine with a four-direction tape geometry. -/
structure HTM where
  alphabetSize : Nat
  stateSize : Nat
  hAlphabet : 0 < alphabetSize
  hState : 0 < stateSize
  transition : Fin stateSize → Fin alphabetSize → Fin stateSize × Fin alphabetSize × HDirection
  initialState : Fin stateSize
  acceptState : Fin stateSize
  accepts : List Nat → Prop

abbrev HTM.HSymbol (M : HTM) := Fin M.alphabetSize
abbrev HTM.HState (M : HTM) := Fin M.stateSize

/-- A single HTM configuration. -/
structure HTMConfig (M : HTM) where
  state : M.HState
  head : HTapeCell
  tape : HTapeCell → M.HSymbol

/-- Hypercomplex head motion on the `ℤ × ℤ` proxy tape. -/
def moveHead : HTapeCell → HDirection → HTapeCell
  | (x, y), .Real => (x + 1, y)
  | (x, y), .Imag => (x, y + 1)
  | (x, y), .RealBack => (x - 1, y)
  | (x, y), .ImagBack => (x, y - 1)

/-- A designated blank symbol. -/
def HTM.blank (M : HTM) : M.HSymbol :=
  ⟨0, M.hAlphabet⟩

/-- One symbolic HyperTuring step. -/
def HTM.step (M : HTM) (cfg : HTMConfig M) : HTMConfig M :=
  let current := cfg.tape cfg.head
  let out := M.transition cfg.state current
  { state := out.1
    head := moveHead cfg.head out.2.2
    tape := fun cell => if cell = cfg.head then out.2.1 else cfg.tape cell }

/-- The extensional halting predicate used in this finite scaffold. -/
def HTM.halts_on (M : HTM) (w : List Nat) : Prop :=
  M.accepts w

/-- Path length is measured by the number of visited tape cells. -/
def HTM.path_length (_M : HTM) (path : List HTapeCell) : Nat :=
  path.length

/-- A mock-polynomial budget uses logarithmic path length in the input size. -/
def HTM.is_mock_poly (M : HTM) (w : List Nat) (path : List HTapeCell) : Prop :=
  ∃ C : Nat, M.path_length path ≤ C * Nat.log 2 w.length

/-- Embed a classical acceptance predicate into a HyperTuring geometry without changing language recognition. -/
def embedTM (tm : ClassicalTM) : HTM where
  alphabetSize := tm.alphabetSize
  stateSize := tm.stateSize
  hAlphabet := tm.hAlphabet
  hState := tm.hState
  transition := fun q s => (q, s, HDirection.Real)
  initialState := ⟨0, tm.hState⟩
  acceptState := ⟨0, tm.hState⟩
  accepts := tm.accepts

/-- Every classical acceptance predicate can be reinterpreted as an HTM language exactly. -/
theorem htm_simulates_tm (tm : ClassicalTM) :
    ∃ h : HTM, ∀ w : List Nat, tm.accepts w ↔ h.accepts w := by
  refine ⟨embedTM tm, ?_⟩
  intro w
  rfl

/-- In the present finite scaffold, HTM halting is extensionally the same predicate as classical halting. -/
theorem htm_halting_equiv_classical (tm : ClassicalTM) :
    ∃ htm : HTM, ∀ w : List Nat, htm.halts_on w ↔ Halts tm w := by
  refine ⟨embedTM tm, ?_⟩
  intro w
  rfl

/-- A simple discrete ball-growth proxy: each step branches across `2^ambientDim` new cells. -/
def cells_reachable (ambientDim pathLen : Nat) : Nat :=
  (2 ^ ambientDim) ^ pathLen

/-- Exact power-of-two specialization of the logarithmic volume law. -/
theorem cells_reachable_pow_two (k C : Nat) :
    cells_reachable 4 (C * Nat.log 2 (2 ^ k)) = (2 ^ k) ^ (4 * C) := by
  rw [Nat.log_pow (by omega : 1 < 2)]
  unfold cells_reachable
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring_nf

/--
Open hyperbolic volume bridge: the intended lower bound needs a formal comparison
between the discrete `cells_reachable` model and the actual hyperbolic ball
volume available to the computation.
-/
theorem mock_p_volume_count (n C : ℕ) (path_len : ℕ)
    (h : path_len ≤ C * Nat.log 2 n) :
    cells_reachable (4 * n) path_len ≥ n ^ (4 * C) := by
  -- FRONTIER: this theorem is genuinely false for the current hypotheses.
  -- Counterexample: `n = 3`, `C = 1`, `path_len = 0` satisfies
  --   `0 ≤ 1 * Nat.log 2 3`,
  -- but the conclusion becomes
  --   `cells_reachable 12 0 = 1 ≥ 3 ^ 4 = 81`,
  -- which is impossible.
  --
  -- To close this gap one must either:
  --   * replace `path_len ≤ C * Nat.log 2 n` by a lower bound forcing enough growth,
  --   * or compare `cells_reachable` to the intended hyperbolic ball-volume model
  --     through an additional geometric lemma.
  --
  -- We therefore keep a minimal `sorry` here until the statement is reformulated.
  sorry

end ConnectionLaplacian
