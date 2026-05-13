import Mathlib

noncomputable section

namespace Scratch

def f (x : ℝ) : ℝ := (1 + Real.exp (-x))⁻¹ - x

example : ∃ x : ℝ, x = 1 / (1 + Real.exp (-x)) := by
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    refine (((continuous_const.add
      (Real.continuous_exp.comp (continuous_neg.comp continuous_id'))).continuousOn.inv₀ ?_).sub
      continuousOn_id)
    intro x hx
    have hpos : 0 < 1 + Real.exp (-x) := by positivity
    exact ne_of_gt hpos
  have hf0 : 0 < f 0 := by
    norm_num [f]
  have hf1 : f 1 < 0 := by
    have hden : 1 < 1 + Real.exp (-1 : ℝ) := by
      have hexp : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
      linarith
    have hinv : (1 + Real.exp (-1 : ℝ))⁻¹ < 1 := inv_lt_one hden
    have : (1 + Real.exp (-1 : ℝ))⁻¹ - 1 < 0 := by linarith
    simpa [f] using this
  have hzero : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
    constructor
    · exact le_of_lt hf1
    · exact le_of_lt hf0
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hcont hzero
  refine ⟨x, ?_⟩
  have hx0' : (1 + Real.exp (-x))⁻¹ - x = 0 := by simpa [f] using hx0
  have hxeq : (1 + Real.exp (-x))⁻¹ = x := sub_eq_zero.mp hx0'
  simpa [one_div] using hxeq.symm

end Scratch
