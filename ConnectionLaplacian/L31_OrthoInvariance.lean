import Mathlib

namespace ConnectionLaplacian

/-- A linear isometry preserves norms. -/
theorem ortho_invariance_norm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E ≃ₗᵢ[ℝ] F) (x : E) :
    ‖f x‖ = ‖x‖ := by
  exact f.norm_map x

/-- A linear isometry preserves distances. -/
theorem ortho_invariance_dist
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E ≃ₗᵢ[ℝ] F) (x y : E) :
    dist (f x) (f y) = dist x y := by
  exact f.dist_map x y

end ConnectionLaplacian
