import Mathlib

noncomputable section

example : Continuous (fun x : ℝ => 1 / (1 + Real.exp (-x))) := by
  continuity

example : Continuous (fun x : ℝ => 1 / (1 + Real.exp (-x)) - x) := by
  continuity
