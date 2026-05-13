import Mathlib

namespace ConnectionLaplacian

/-- The orbit of a linear isometry under repeated application. -/
def orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E ≃ₗᵢ[ℝ] E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => f (orbit f n x)

/-- Every point on the orbit has the same norm as the initial point. -/
theorem orbit_norm_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E ≃ₗᵢ[ℝ] E) (n : ℕ) (x : E) :
    ‖orbit f n x‖ = ‖x‖ := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [orbit, ih, f.norm_map]

/-- Distances between two orbit trajectories are preserved at every time step. -/
theorem orbit_dist_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E ≃ₗᵢ[ℝ] E) (n : ℕ) (x y : E) :
    dist (orbit f n x) (orbit f n y) = dist x y := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [orbit, ih, f.dist_map]

end ConnectionLaplacian
