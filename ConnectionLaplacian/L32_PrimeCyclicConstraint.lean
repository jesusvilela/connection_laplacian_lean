import Mathlib

namespace ConnectionLaplacian

/-- A prime-indexed cyclic constraint: the index is prime, so its divisors are rigid. -/
structure PrimeCyclicConstraint (p : ℕ) where
  prime : Nat.Prime p

/-- Prime indices are always strictly greater than `1`. -/
theorem prime_cyclic_constraint_one_lt {p : ℕ} (hp : Nat.Prime p) : 1 < p := by
  exact hp.one_lt

/-- A divisor of a prime cycle is either trivial or the whole cycle. -/
theorem prime_cyclic_constraint_divisor {p d : ℕ} (hp : Nat.Prime p) (hd : d ∣ p) :
    d = 1 ∨ d = p := by
  exact hp.eq_one_or_self_of_dvd d hd

/-- Any proper divisor of a prime cycle must be trivial. -/
theorem prime_cyclic_constraint_proper_divisor {p d : ℕ} (hp : Nat.Prime p)
    (hd : d ∣ p) (hnd : d ≠ p) : d = 1 := by
  rcases hp.eq_one_or_self_of_dvd d hd with rfl | rfl
  · rfl
  · exact False.elim (hnd rfl)

end ConnectionLaplacian
