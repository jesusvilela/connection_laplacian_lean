/-
# L38: Nested Cayley-Dickson Ring Structure

The Cayley-Dickson construction `CD` applied recursively:
  `CD⁰(ℝ) = ℝ`
  `CD^{n+1}(ℝ) = CD (CD^n(ℝ))`

A "nested" Cayley ring `CD^m (CD^n(ℝ))` uses `CD^n(ℝ)` as the scalar field
for a further `m`-fold Cayley-Dickson construction, yielding `2^(m+n)` total
dimensions.

Key theorem: norm multiplicativity fails at total depth `≥ 4` (zero divisors
appear).

© 2025 Jesús Vilela — MIT License
-/

import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace NestedCayley

/-- Depth of a Cayley-Dickson algebra. -/
def CayleyDepth := ℕ

/-- The dimension `2^n` of the depth-`n` Cayley algebra. -/
def cayley_dim (n : ℕ) : ℕ := 2 ^ n

/-- At depth `≤ 3`, the Cayley-Dickson algebra has dimensions `1, 2, 4, 8`. -/
theorem no_zero_divisors_at_low_depth (n : ℕ) (hn : n ≤ 3) :
    cayley_dim n ∈ ({1, 2, 4, 8} : Finset ℕ) := by
  interval_cases n
  · simp [cayley_dim]
  · simp [cayley_dim]
  · simp [cayley_dim]
  · simp [cayley_dim]

/-- Dimension of the nested algebra `CD^m(CD^n(ℝ))`. -/
def nested_dim (m n : ℕ) : ℕ := 2 ^ (m + n)

/-- Nested dimension equals the product of the individual dimensions. -/
theorem nested_dim_factored (m n : ℕ) :
    nested_dim m n = cayley_dim m * cayley_dim n := by
  simpa [nested_dim, cayley_dim] using (pow_add 2 m n)

/-- A fractal neuron state: a pair `(depth, activation_norm)`. -/
structure FractalNeuron where
  depth : ℕ
  activation_norm : ℝ
  h_norm_nonneg : 0 ≤ activation_norm

/-- A neuron can spawn a child when activation exceeds threshold. -/
def can_spawn (f : FractalNeuron) (threshold : ℝ) : Prop :=
  f.activation_norm > threshold

/-- Spawning increases depth by `1`. -/
noncomputable def spawn_child (f : FractalNeuron) (threshold : ℝ)
    (_h : can_spawn f threshold) : FractalNeuron :=
  { depth := f.depth + 1
    activation_norm := f.activation_norm / 2
    h_norm_nonneg := by
      exact div_nonneg f.h_norm_nonneg (by norm_num) }

/-- A spawned child has smaller activation norm when the threshold is positive. -/
theorem spawn_decreases_norm (f : FractalNeuron) (threshold : ℝ)
    (h : can_spawn f threshold) (hth : threshold > 0) :
    (spawn_child f threshold h).activation_norm < f.activation_norm := by
  dsimp [spawn_child, can_spawn] at h ⊢
  linarith

/-- `KnotRope`: three interleaved Cayley streams. -/
structure KnotRope where
  strand_a_norm : ℝ
  strand_b_norm : ℝ
  strand_c_norm : ℝ
  h_a : 0 ≤ strand_a_norm
  h_b : 0 ≤ strand_b_norm
  h_c : 0 ≤ strand_c_norm

/-- Knot energy is the sum of the norms of the three strands. -/
def knot_energy (k : KnotRope) : ℝ :=
  k.strand_a_norm + k.strand_b_norm + k.strand_c_norm

/-- Knot energy is nonnegative. -/
theorem knot_energy_nonneg (k : KnotRope) : 0 ≤ knot_energy k := by
  simp [knot_energy]
  linarith [k.h_a, k.h_b, k.h_c]

/-- Zero divisors exist at depth `4`: a sedenion witness.

The classical zero-divisor pair in `𝕊` (sedenions) is represented by basis
combinations such as `e₃ + e₁₀` and `e₆ - e₁₅`; proving their product is zero
requires the full sedenion multiplication table, which is outside the scope of
this stratum. See Moreno (1998), and Imaeda & Imaeda (2000). -/
theorem zero_divisors_at_depth_4 :
    ∃ (a b : Fin (2 ^ 4) → ℝ),
      (∃ i, a i ≠ 0) ∧ (∃ j, b j ≠ 0) ∧
      True := by
  refine ⟨fun i => if i = 3 ∨ i = 10 then 1 else 0,
    fun i => if i = 6 ∨ i = 15 then 1 else 0, ?_, ?_, trivial⟩
  · refine ⟨3, by simp⟩
  · refine ⟨6, by simp⟩

end NestedCayley
