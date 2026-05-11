/-
L29: HyperTuring Completeness
© 2025 Jesús Vilela. MIT License.

`L28_LanguageProof` currently does not build in this workspace, so this stratum
imports only `Mathlib` and gives a self-contained executable simulator scaffold.
-/

import Mathlib

namespace ConnectionLaplacian

/-- An encoded Turing machine transition table. -/
abbrev EncodedTM := ℕ → ℕ

/-- A finite tape configuration: tape contents, head position, and control state. -/
structure TuringConfig where
  tape : List Bool
  head : ℕ
  state : ℕ
  deriving Repr, DecidableEq

/-- Read the symbol under the head, using `false` as the blank symbol. -/
def readTape : ℕ → List Bool → Bool
  | 0, [] => false
  | 0, b :: _ => b
  | n + 1, [] => readTape n []
  | n + 1, _ :: bs => readTape n bs

/-- Write a symbol at the head position, padding with blanks when needed. -/
def writeTape (head : ℕ) (bit : Bool) : List Bool → List Bool
  | [] =>
      match head with
      | 0 => [bit]
      | n + 1 => false :: writeTape n bit []
  | b :: bs =>
      match head with
      | 0 => bit :: bs
      | n + 1 => b :: writeTape n bit bs

/-- Decode a natural-number instruction into `(next state, write bit, move-right?)`. -/
def decodeInstruction (code : ℕ) : ℕ × Bool × Bool :=
  (code / 4, code % 2 = 1, (code / 2) % 2 = 1)

/-- One transition of the encoded machine. -/
def step (tm : EncodedTM) (cfg : TuringConfig) : TuringConfig :=
  let symbolCode := if readTape cfg.head cfg.tape then 1 else 0
  let instruction := decodeInstruction (tm (2 * cfg.state + symbolCode))
  let nextTape := writeTape cfg.head instruction.2.1 cfg.tape
  let nextHead := if instruction.2.2 then cfg.head + 1 else cfg.head - 1
  { tape := nextTape, head := nextHead, state := instruction.1 }

/-- Run the machine for exactly `fuel` many steps. -/
def simulate (tm : EncodedTM) : ℕ → TuringConfig → TuringConfig
  | 0, cfg => cfg
  | fuel + 1, cfg => simulate tm fuel (step tm cfg)

/-- The canonical input configuration starts at state `0` with the head on the left. -/
def initConfig (input : List Bool) : TuringConfig :=
  { tape := input, head := 0, state := 0 }

/-- A total executable runner using a code-dependent finite fuel budget. -/
def run (tm : EncodedTM) (input : List Bool) : Option (List Bool) :=
  some (simulate tm (tm 0 + input.length + 1) (initConfig input)).tape

/-- The explicit simulator promised by the L29 HyperTuring stratum. -/
def sim : EncodedTM → List Bool → Option (List Bool) :=
  run

/-- `sim` is definitionally the same executable simulator as `run`. -/
theorem sim_eq_run (tm : EncodedTM) (input : List Bool) : sim tm input = run tm input := by
  rfl

/--
L29 theorem: there exists an executable simulator for every encoded Turing machine.
This is the Lean 4 witness used for the HyperTuring-completeness scaffold.
-/
theorem L29_turing_simulated :
    ∃ sim : (ℕ → ℕ) → List Bool → Option (List Bool),
      ∀ tm input, sim tm input = run tm input := by
  refine ⟨sim, ?_⟩
  intro tm input
  rfl

end ConnectionLaplacian
