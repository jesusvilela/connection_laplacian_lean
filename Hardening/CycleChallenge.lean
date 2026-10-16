/-
Comparator challenge transcript: complete n-cycle spectra and graph-level
conditional transport.  These formulas were re-stated from the published
spectral identities and explicit matrix correspondence obligations, rather
than depending on the names or statements of the new Lean theorems.

This module intentionally uses sorry as an UNTRUSTED CHALLENGE ONLY.
It is not imported by the production ConnectionLaplacian library.
The comparator compares each elaborated theorem TYPE with CycleSolution
and checks the latter's axioms and transitive proof-term kernel replay.
-/
import ConnectionLaplacian.CycleSpectrum
import Hardening.Compat

namespace Hardening.Cycle

open Matrix Polynomial BigOperators

/-- Periodic flat-cycle spectrum, including ALL eigenvalue factors. -/
theorem periodic_charpoly (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.scalarCycleLaplacian n (by omega)).charpoly =
      ∏ j : Fin n, (Polynomial.X -
        Polynomial.C (2 - 2 * Real.cos (2 * Real.pi * j.val / n))) := by
  sorry

/-- Anti-periodic signed-cycle spectrum, with repeated roots. -/
theorem antiperiodic_charpoly (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.signedCycleLaplacian n (by omega)).charpoly =
      ∏ j : Fin n, (Polynomial.X -
        Polynomial.C (2 - 2 * Real.cos ((2 * j.val + 1) * Real.pi / n))) := by
  sorry

/-- All real eigenvalues, as a multiset rather than its support set. -/
theorem periodic_multiset (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.scalarCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun j : Fin n => 2 - 2 * Real.cos (2 * Real.pi * j.val / n))
        (Finset.univ : Finset (Fin n)).val := by
  sorry

/-- All antiperiodic real eigenvalues, with algebraic multiplicity. -/
theorem antiperiodic_multiset (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.signedCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun j : Fin n =>
          2 - 2 * Real.cos ((2 * j.val + 1) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val := by
  sorry

/-- Full connection graph-level multiset: requires TWO ACTUAL matrix
identifications under a common vertex equivalence, not merely n vertices. -/
theorem mobius_graph_multiset (n : ℕ) (hn : 3 ≤ n)
    (G : ConnectionLaplacian.ConnGraph) (e : G.V ≃ Fin n)
    (hsc : Matrix.reindex e e G.scalarLaplacian =
       ConnectionLaplacian.Cycle.scalarCycleLaplacian n (by omega))
    (hsg : Matrix.reindex e e G.signedLaplacianMobius =
       ConnectionLaplacian.Cycle.signedCycleLaplacian n (by omega)) :
    (G.laplacian true).charpoly.roots =
      Multiset.map
        (fun j : Fin n => 2 - 2 * Real.cos (2 * Real.pi * j.val / n))
        (Finset.univ : Finset (Fin n)).val +
      Multiset.map
        (fun j : Fin n =>
          2 - 2 * Real.cos ((2 * j.val + 1) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val := by
  sorry

end Hardening.Cycle
