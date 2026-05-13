import Mathlib

namespace ConnectionLaplacian

/-!
L34: Fixed-point witness and Hamiltonian-style invariance facts.

The statements in this file are intentionally lightweight and robust:
* a finite-structure fixed-point witness for constant self-maps,
* Hamiltonian-like scalar invariance and bound preservation under iterates,
* a clipped resonance scalar bounded in `[0,1]`.
-/

section FixedPoint

variable {α : Type*} [Fintype α]

/-- On a finite type, any constant self-map has a canonical fixed-point witness. -/
theorem fixedpoint_witness_of_constant_selfmap
    (f : α → α)
    (hconst : ∀ x y, f x = f y)
    (hcard : 0 < Fintype.card α) :
    ∃ x : α, f x = x := by
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hcard
  refine ⟨f x, ?_⟩
  simpa using hconst (f x) x

end FixedPoint

section Hamiltonian

variable {α : Type*}

/-- `H` is invariant along `f`. -/
def HamiltonianInvariant (H : α → ℝ) (f : α → α) : Prop :=
  ∀ x, H (f x) = H x

/-- Invariance propagates to every iterate of the map. -/
theorem hamiltonian_invariant_iterate
    (H : α → ℝ) (f : α → α)
    (hInv : HamiltonianInvariant H f) :
    ∀ n x, H ((f^[n]) x) = H x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        H ((f^[n + 1]) x) = H ((f^[n]) (f x)) := by
          simp [Function.iterate_succ_apply]
        _ = H (f x) := ih (f x)
        _ = H x := hInv x

/-- If `H` is bounded in `[lo, hi]`, those bounds are preserved along all iterates of an invariant map. -/
theorem hamiltonian_bounds_preserved_on_iterates
    (H : α → ℝ) (f : α → α) (lo hi : ℝ)
    (hInv : HamiltonianInvariant H f)
    (hBounds : ∀ x, lo ≤ H x ∧ H x ≤ hi) :
    ∀ n x, lo ≤ H ((f^[n]) x) ∧ H ((f^[n]) x) ≤ hi := by
  intro n x
  have hEq : H ((f^[n]) x) = H x := hamiltonian_invariant_iterate H f hInv n x
  simpa [hEq] using hBounds x

end Hamiltonian

section Resonance

/-- A clipped resonance scalar. -/
noncomputable def resonanceClip (r : ℝ) : ℝ := max 0 (min 1 r)

/-- The clipped resonance value always lies in `[0,1]`. -/
theorem resonanceClip_mem_unit_interval (r : ℝ) :
    0 ≤ resonanceClip r ∧ resonanceClip r ≤ 1 := by
  unfold resonanceClip
  constructor
  · exact le_max_left 0 (min 1 r)
  ·
    calc
      max 0 (min 1 r) ≤ max 1 (min 1 r) := max_le_max (by linarith) le_rfl
      _ = 1 := by simp [max_eq_left (min_le_left 1 r)]

end Resonance

end ConnectionLaplacian
