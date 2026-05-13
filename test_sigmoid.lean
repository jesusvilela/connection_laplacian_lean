import Mathlib

noncomputable section

def g (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

def f (x : ℝ) : ℝ := g x - x

example : Continuous g := by
  continuity

example : Continuous f := by
  unfold f
  exact (by continuity : Continuous fun x : ℝ => g x - x)

example : g 0 = (1:ℝ)/2 := by
  simp [g]

example : g 1 < 1 := by
  have hden : (1:ℝ) < 1 + Real.exp (-1 : ℝ) := by
    have hexp : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
    linarith
  have := one_div_lt_one hden
  simpa [g] using this

example : f 1 < 0 := by
  have hg : g 1 < 1 := by
    have hden : (1:ℝ) < 1 + Real.exp (-1 : ℝ) := by
      have hexp : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
      linarith
    exact one_div_lt_one hden
  have : g 1 - 1 < 0 := by linarith
  simpa [f] using this

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := (show Continuous f by
    unfold f
    continuity).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    constructor
    · simp [f, g]
    · have hf1 : f 1 < 0 := by
        have hg : g 1 < 1 := by
          have hden : (1:ℝ) < 1 + Real.exp (-1 : ℝ) := by
            have hexp : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
            linarith
          exact one_div_lt_one hden
        have : g 1 - 1 < 0 := by linarith
        simpa [f] using this
      linarith
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hcont hmem
  exact ⟨x, hx, hx0⟩
