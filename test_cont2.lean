import Mathlib

noncomputable section

example : ContinuousOn (fun x : ℝ => (1 + Real.exp (-x))⁻¹ - x) (Set.Icc (0:ℝ) 1) := by
  refine (((continuous_const.add ((Real.continuous_exp.comp (continuous_neg.comp continuous_id')))).continuousOn.inv₀ ?_).sub continuousOn_id)
  intro x hx
  have hpos : 0 < 1 + Real.exp (-x) := by positivity
  exact ne_of_gt hpos
