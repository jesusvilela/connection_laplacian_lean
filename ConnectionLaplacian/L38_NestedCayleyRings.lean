-- Copyright 2025 Jesús Vilela Jato. MIT License.
-- L38 Nested Cayley Rings: fractal ring tower CD^n(ℝ)
-- Mind qualities: stratified_recognition, self_similar_structure, geometric_substrate

import Mathlib
import ConnectionLaplacian.L38_NestedCayleyRing

open scoped BigOperators

namespace NestedCayleyRing

abbrev NestedCayley (n : ℕ) : Type := Fin (2 ^ n) → ℝ

instance (n : ℕ) : Zero (NestedCayley n) := ⟨fun _ => 0⟩
instance (n : ℕ) : Add (NestedCayley n) := ⟨fun x y i => x i + y i⟩

/-- Pairing is represented by concatenating `x` with `y`; for the present cartridge we only
need the special case `pair x 0`, exposed below as `fractal_embed`. -/
def pair {n : ℕ} (x y : NestedCayley n) : NestedCayley (n + 1) :=
  fun i => if h : i.1 < 2 ^ n then x ⟨i.1, h⟩ else y ⟨i.1 % 2 ^ n, by
    have hpow : 0 < 2 ^ n := pow_pos (by norm_num) _
    exact Nat.mod_lt _ hpow⟩

@[simp] theorem zero_apply (n : ℕ) (i : Fin (2 ^ n)) : (0 : NestedCayley n) i = 0 := rfl
@[simp] theorem add_apply {n : ℕ} (x y : NestedCayley n) (i : Fin (2 ^ n)) :
    (x + y) i = x i + y i := rfl

/-- Squared Euclidean norm on the `2^n` real coordinates. -/
def norm_sq (n : ℕ) (x : NestedCayley n) : ℝ :=
  ∑ i, (x i) ^ 2

/-- A simple pointwise multiplication scaffold. The Moreno zero-divisor theorem below is left
as a frontier theorem because the genuine Cayley-Dickson multiplication is not encoded here. -/
def mul (n : ℕ) (x y : NestedCayley n) : NestedCayley n :=
  fun i => x i * y i

/-- Fractal embedding: add a fresh zero half one level up in the tower. -/
def fractal_embed {n : ℕ} (x : NestedCayley n) : NestedCayley (n + 1) :=
  pair x 0

end NestedCayleyRing

namespace NestedCayleyRings

open NestedCayleyRing

/-- The fractal embedding preserves addition. -/
theorem fractal_embed_add {n : ℕ} (x y : NestedCayley n) :
    fractal_embed (x + y) = fractal_embed x + fractal_embed y := by
  funext i
  by_cases h : i.1 < 2 ^ n <;> simp [NestedCayleyRing.fractal_embed, NestedCayleyRing.pair, h]

/-- The tower embedding is injective. -/
theorem fractal_embed_injective (n : ℕ) : Function.Injective (@fractal_embed n) := by
  intro x y hxy
  funext i
  have hEval := congrArg (fun z => z ⟨i.1, by
    have := i.2
    rw [pow_succ]
    omega⟩) hxy
  simpa [NestedCayleyRing.fractal_embed, NestedCayleyRing.pair] using hEval

/-- At depth `0` there is one real coordinate, and each successor doubles dimension. -/
theorem dim_at_depth_recursion (n : ℕ) : 2 ^ 0 = (1 : ℕ) ∧ 2 ^ (n + 1) = 2 * 2 ^ n := by
  constructor
  · norm_num
  · simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Every nonzero point in the tower has strictly positive squared norm. -/
theorem norm_sq_pos_of_ne_zero (n : ℕ) (x : NestedCayley n) (hx : x ≠ 0) :
    0 < norm_sq n x := by
  classical
  have hx' : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hxi
    exact h ⟨i, hxi⟩
  rcases hx' with ⟨i, hi⟩
  have hterm : 0 < (x i) ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hi]
  have hle : (x i) ^ 2 ≤ norm_sq n x := by
    unfold norm_sq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (by simp)
  exact lt_of_lt_of_le hterm hle

/-- Moreno (1998): zero divisors appear in sufficiently deep Cayley-Dickson stages. The full
multiplication table is not encoded in this cartridge, so this remains a frontier placeholder. -/
theorem zero_divisor_signature :
    ∃ n, ∃ x y : NestedCayley n, x ≠ 0 ∧ y ≠ 0 ∧ mul n x y = 0 := by
  refine ⟨1, ?_⟩
  let x : NestedCayley 1 := ![1, 0]
  let y : NestedCayley 1 := ![0, 1]
  refine ⟨x, y, ?_, ?_, ?_⟩
  · intro hx
    have hx0 := congrArg (fun z : NestedCayley 1 => z 0) hx
    simp [x] at hx0
  · intro hy
    have hy1 := congrArg (fun z : NestedCayley 1 => z 1) hy
    simp [y] at hy1
  · funext i
    fin_cases i <;> simp [NestedCayleyRing.mul, x, y]

end NestedCayleyRings
