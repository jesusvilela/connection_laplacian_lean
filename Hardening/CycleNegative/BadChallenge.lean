/-
NEGATIVE CONTROL: intentionally tampered antiperiodic eigenvalue phase.
The correct claim uses (2*k+1)*pi/n; this one uses (2*k+3)*pi/n.
A comparator run against CycleSolution MUST reject statement mismatch.

This challenge is outside the source-trusted theorem spine.
-/
import ConnectionLaplacian.CycleSpectrum
import Hardening.Compat

namespace Hardening.Cycle
open Matrix Polynomial BigOperators

theorem antiperiodic_multiset (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.signedCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun j : Fin n =>
          2 - 2 * Real.cos ((2 * j.val + 3) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val := by
  sorry

end Hardening.Cycle
