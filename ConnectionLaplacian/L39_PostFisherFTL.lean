-- Copyright 2025 Jesús Vilela Jato. MIT License.
-- L39 Post-Fisher FTL: hyperbolic geodesic acceleration
-- Mind qualities: geometric_substrate, self_similar_structure, multi_angle_epistemics

import Mathlib

namespace PostFisherFTL

/-- Fisher information for a positive scale parameter. -/
noncomputable def fisherInfo (σ : ℝ) : ℝ := 1 / σ ^ 2

theorem fisher_info_positive {σ : ℝ} (hσ : 0 < σ) : 0 < fisherInfo σ := by
  unfold fisherInfo
  have hpow : 0 < σ ^ 2 := by positivity
  exact one_div_pos.mpr hpow

theorem geometric_series_decay : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (1 / 2 : ℝ) ^ n < ε := by
  intro ε hε
  let r : ℝ := 1 / 2
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (nhds (0 : ℝ)) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · norm_num [r]
    · norm_num [r]
  have hEvent : ∀ᶠ n in Filter.atTop, r ^ n < ε :=
    ht (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEvent
  exact ⟨N, fun n hn => hN n hn⟩

noncomputable def virtualTimeFactor (berry r : ℝ) : ℝ :=
  1 + ((3 : ℝ) / 10) * Real.sin berry + ((1 : ℝ) / 5) * (1 - r)

theorem virtual_time_factor_bounds {berry r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 / 2 : ℝ) ≤ virtualTimeFactor berry r ∧ virtualTimeFactor berry r ≤ 2 := by
  have hsinLower : -1 ≤ Real.sin berry := Real.neg_one_le_sin _
  have hsinUpper : Real.sin berry ≤ 1 := Real.sin_le_one _
  have hradLower : 0 ≤ 1 - r := by linarith
  have hradUpper : 1 - r ≤ 1 := by linarith
  constructor
  · unfold virtualTimeFactor
    nlinarith
  · unfold virtualTimeFactor
    nlinarith

theorem poincare_boundary_approach (n : ℕ) : 1 - (1 / 2 : ℝ) ^ n < 1 := by
  have hpow : 0 < (1 / 2 : ℝ) ^ n := by positivity
  linarith

/-- As `r → 1⁻`, `log ((1+r)/(1-r))` diverges to `+∞`; this is a standard Poincaré disk metric
fact left as a future asymptotic cartridge. -/
theorem hyperbolic_metric_divergence_placeholder : True := by
  trivial

end PostFisherFTL
