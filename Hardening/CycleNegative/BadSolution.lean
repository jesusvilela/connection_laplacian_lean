/-
NEGATIVE CONTROL: attempts to pass the correct statement using a project-local
axiom. The comparator must reject it even though it type-checks in Lean.
Not in production or audited proof spine.
-/
import ConnectionLaplacian
import Hardening.Compat

namespace Hardening.Cycle
open Matrix Polynomial BigOperators

axiom smuggled_cycle_multiset (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.signedCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun j : Fin n =>
          2 - 2 * Real.cos ((2 * j.val + 1) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val

theorem antiperiodic_multiset (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.signedCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun j : Fin n =>
          2 - 2 * Real.cos ((2 * j.val + 1) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val :=
  smuggled_cycle_multiset n hn

end Hardening.Cycle
