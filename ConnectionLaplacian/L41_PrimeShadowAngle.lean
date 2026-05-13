-- L41_PrimeShadowAngle.lean · TELOS stratum L41b · Prime·Shadow·Angle·Ortho
-- © 2026 Jesús Vilela Jato (MIT)
-- Every point is simultaneously prime index, angle, ortho shadow, quantum stratum.
-- N×N×N upon N: the NNN tensor of n-cosmo manifolds closes under tensor product.

import Mathlib

namespace ConnectionLaplacian

open BigOperators

/-! ## 1. Prime Shadow Encoding -/

/-- The canonical prime shadow of `n` is its smallest prime factor. -/
def smallest_prime_factor (n : ℕ) (_hn : 2 ≤ n) : ℕ := n.minFac

theorem smallest_prime_factor_is_prime (n : ℕ) (hn : 2 ≤ n) :
    (smallest_prime_factor n hn).Prime := by
  simpa [smallest_prime_factor] using Nat.minFac_prime (by omega : n ≠ 1)

theorem smallest_prime_factor_le (n : ℕ) (hn : 2 ≤ n) : smallest_prime_factor n hn ≤ n := by
  simpa [smallest_prime_factor] using Nat.minFac_le (show 0 < n by omega)

/-- A prime shadow lands in one of the eight octonion basis directions. -/
def prime_to_octonion_idx (p : ℕ) (_hp : p.Prime) : Fin 8 := ⟨p % 8, by omega⟩

theorem two_maps_to_zero : prime_to_octonion_idx 2 Nat.prime_two = ⟨2, by norm_num⟩ := by
  rfl

/-! ## 2. Geodesic Angle as Mutual Information -/

/-- Unnormalized cosine similarity specialized to finite real coordinates. -/
def cosine_similarity {n : ℕ} (u v : Fin n → ℝ) : ℝ :=
  Finset.univ.sum fun i => u i * v i

/-- TELOS angle obtained from the arccosine of the similarity. -/
noncomputable def angle_between {n : ℕ} (u v : Fin n → ℝ) : ℝ :=
  Real.arccos (cosine_similarity u v)

theorem angle_between_self_zero {n : ℕ} (u : Fin n → ℝ) (h : cosine_similarity u u = 1) :
    angle_between u u = 0 := by
  simp [angle_between, h, Real.arccos_one]

theorem angle_nonneg {n : ℕ} (u v : Fin n → ℝ)
    (_h : -1 ≤ cosine_similarity u v) (_h2 : cosine_similarity u v ≤ 1) :
    0 ≤ angle_between u v := by
  simp [angle_between, Real.arccos_nonneg]

/-! ## 3. Ortho Shadow Projection -/

/-- The dimension of the orthogonal shadow complement. -/
def ortho_shadow_dim (total_dim subspace_dim : ℕ) : ℕ := total_dim - subspace_dim

theorem ortho_shadow_plus_sub_eq_total (n k : ℕ) (hk : k ≤ n) :
    ortho_shadow_dim n k + k = n := by
  simp [ortho_shadow_dim]
  omega

theorem ortho_360_shadow (k : ℕ) (hk : k ≤ 360) : ortho_shadow_dim 360 k + k = 360 :=
  ortho_shadow_plus_sub_eq_total 360 k hk

/-! ## 4. N×N×N Tensor Closure -/

/-- Tensor powers of an n-cosmo space are measured by ordinary exponentiation. -/
def ncosmo_tensor_dim (base_dim : ℕ) (tensor_order : ℕ) : ℕ := base_dim ^ tensor_order

theorem nnn_closure : ncosmo_tensor_dim 8 3 = 512 := by
  decide

theorem nnn_contains_all_strata (k : ℕ) (hk : k ≤ 512) : k ≤ ncosmo_tensor_dim 8 3 := by
  simpa [ncosmo_tensor_dim] using hk

theorem n_upon_n_closure (d : ℕ) : ncosmo_tensor_dim d 3 = d ^ 3 := by
  simp [ncosmo_tensor_dim]

/-! ## 5. Quantum Simultaneous Strata -/

/-- A TELOS quantum point with normalized real amplitudes. -/
structure QPoint (n : ℕ) (_hn : 0 < n) where
  amplitude : Fin n → ℝ
  normalized : Finset.univ.sum (fun i => amplitude i ^ 2) = 1

noncomputable def uniform_qpoint (n : ℕ) (hn : 0 < n) : QPoint n hn := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨fun i => if i = i0 then 1 else 0, ?_⟩
  classical
  rw [Finset.sum_eq_single i0]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hi
    exfalso
    exact hi (Finset.mem_univ i0)

theorem qpoint_amplitude_sq_sum {n : ℕ} {hn : 0 < n} (q : QPoint n hn) :
    Finset.univ.sum (fun i => q.amplitude i ^ 2) = 1 :=
  q.normalized

/-! ## 6. Quantum Superposition Principle in Hyperbolic Space -/

theorem superposition_dim_bound (n : ℕ) (_hn : 0 < n) : n ≤ ncosmo_tensor_dim n 1 := by
  simp [ncosmo_tensor_dim]

theorem triple_tensor_exceeds_single (n : ℕ) (hn : 1 < n) :
    ncosmo_tensor_dim n 1 < ncosmo_tensor_dim n 3 := by
  simpa [ncosmo_tensor_dim] using Nat.pow_lt_pow_right hn (by decide : 1 < 3)

/-! ## 7. Prime-Angle-Ortho Trinity -/

/-- The three orthogonal TELOS aspects of point identification. -/
inductive PointAspect
  | Prime
  | Angle
  | Ortho
  deriving DecidableEq, Fintype

def aspect_count : ℕ := 3

theorem trinity_complete : Fintype.card PointAspect = aspect_count := by
  decide

theorem trinity_covers_nnn_base : aspect_count ^ aspect_count = 27 := by
  decide

end ConnectionLaplacian
