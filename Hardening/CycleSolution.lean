/-
Comparator solution transcript for the separately stated cycle challenges.

Delegates to existing Lean-verified theorems. The structural agreement
between this module and the challenge is checked by comparator at the
elaborated-type level, NOT by text matching or by the Lean compiler alone.
-/
import ConnectionLaplacian
import Hardening.Compat

namespace Hardening.Cycle

open Matrix Polynomial BigOperators

theorem periodic_charpoly (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.scalarCycleLaplacian n (by omega)).charpoly =
      ∏ j : Fin n, (Polynomial.X -
        Polynomial.C (2 - 2 * Real.cos (2 * Real.pi * j.val / n))) :=
  ConnectionLaplacian.Cycle.scalarCycle_charpoly_real n hn

theorem antiperiodic_charpoly (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.signedCycleLaplacian n (by omega)).charpoly =
      ∏ j : Fin n, (Polynomial.X -
        Polynomial.C (2 - 2 * Real.cos ((2 * j.val + 1) * Real.pi / n))) :=
  ConnectionLaplacian.Cycle.signedCycle_charpoly_real n hn

theorem periodic_multiset (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.scalarCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun j : Fin n => 2 - 2 * Real.cos (2 * Real.pi * j.val / n))
        (Finset.univ : Finset (Fin n)).val :=
  ConnectionLaplacian.Cycle.scalarCycle_roots_real n hn

theorem antiperiodic_multiset (n : ℕ) (hn : 3 ≤ n) :
    (ConnectionLaplacian.Cycle.signedCycleLaplacian n (by omega)).charpoly.roots =
      Multiset.map
        (fun j : Fin n =>
          2 - 2 * Real.cos ((2 * j.val + 1) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val :=
  ConnectionLaplacian.Cycle.signedCycle_roots_real n hn

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
        (Finset.univ : Finset (Fin n)).val :=
  ConnectionLaplacian.Cycle.mobius_connection_roots_of_cycle_reindex
    n hn G e hsc hsg

end Hardening.Cycle
