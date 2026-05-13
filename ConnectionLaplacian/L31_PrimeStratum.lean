import Mathlib

namespace ConnectionLaplacian

/-- A prime-indexed stratum is a cyclic layer whose index is prime. -/
structure PrimeStratum (p : ℕ) where
  prime : Nat.Prime p

/-- Prime indices are structurally nontrivial: they are strictly greater than `1`. -/
theorem prime_stratum_one_lt {p : ℕ} (hp : Nat.Prime p) : 1 < p := by
  exact hp.one_lt

/-- A divisor of a prime index is either trivial or the whole index. -/
theorem prime_stratum_divisor_rigid {p d : ℕ} (hp : Nat.Prime p) (hd : d ∣ p) :
    d = 1 ∨ d = p := by
  exact hp.eq_one_or_self_of_dvd d hd

/-- Any instantiated prime stratum has a nontrivial index. -/
theorem prime_stratum_nontrivial_index {p : ℕ} (s : PrimeStratum p) : 1 < p := by
  exact s.prime.one_lt

end ConnectionLaplacian
