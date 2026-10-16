/-
# From explicit cycle matrices to finite connection graphs

A fully checked, *conditional* bridge between the Fourier spectral results
for the concrete Fin n matrices and an arbitrary ConnGraph admitting an
actual vertex reindexing to those matrices.

The hypotheses hscalar and hsigned are intentionally concrete matrix
equalities: they do not purport to prove that every abstract cycle graph
satisfies them. That remaining graph-encoding/permutation proof is a
separate obligation and cannot be inferred just from a graph label.
-/

import ConnectionLaplacian.CycleMultiset
import ConnectionLaplacian.L16_SpectrumUnion

namespace ConnectionLaplacian.Cycle

open Matrix Polynomial BigOperators

/-- A graph whose scalar Laplacian reindexes to the explicit scalar n-cycle
has the *whole* scalar cycle characteristic polynomial (multiplicities
included). The matrix identification is a required hypothesis. -/
theorem scalarCycle_charpoly_of_graph_reindex (n : ℕ) (hn : 3 ≤ n)
    (G : ConnGraph) (e : G.V ≃ Fin n)
    (hscalar : Matrix.reindex e e G.scalarLaplacian =
      scalarCycleLaplacian n (by omega)) :
    G.scalarLaplacian.charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (2 - 2 * Real.cos (2 * Real.pi * k.val / n))) := by
  calc
    G.scalarLaplacian.charpoly =
        (Matrix.reindex e e G.scalarLaplacian).charpoly :=
          (Matrix.charpoly_reindex e G.scalarLaplacian).symm
    _ = _ := by
      rw [hscalar]
      exact scalarCycle_charpoly_real n hn

/-- The signed graph matrix must reindex to the one-wrap signed cycle,
not merely to an arbitrary graph with n vertices. -/
theorem signedCycle_charpoly_of_graph_reindex (n : ℕ) (hn : 3 ≤ n)
    (G : ConnGraph) (e : G.V ≃ Fin n)
    (hsigned : Matrix.reindex e e G.signedLaplacianMobius =
      signedCycleLaplacian n (by omega)) :
    G.signedLaplacianMobius.charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (2 - 2 * Real.cos ((2 * k.val + 1) * Real.pi / n))) := by
  calc
    G.signedLaplacianMobius.charpoly =
        (Matrix.reindex e e G.signedLaplacianMobius).charpoly :=
          (Matrix.charpoly_reindex e G.signedLaplacianMobius).symm
    _ = _ := by
      rw [hsigned]
      exact signedCycle_charpoly_real n hn

/-- Transfer the exact scalar eigenvalue **multiset** under a proved
vertex-index permutation. -/
theorem scalarCycle_roots_of_graph_reindex (n : ℕ) (hn : 3 ≤ n)
    (G : ConnGraph) (e : G.V ≃ Fin n)
    (hscalar : Matrix.reindex e e G.scalarLaplacian =
      scalarCycleLaplacian n (by omega)) :
    G.scalarLaplacian.charpoly.roots =
      Multiset.map
        (fun k : Fin n => 2 - 2 * Real.cos (2 * Real.pi * k.val / n))
        (Finset.univ : Finset (Fin n)).val := by
  rw [← Matrix.charpoly_reindex e G.scalarLaplacian, hscalar]
  exact scalarCycle_roots_real n hn

/-- Transfer the exact one-wrap signed eigenvalue **multiset**. -/
theorem signedCycle_roots_of_graph_reindex (n : ℕ) (hn : 3 ≤ n)
    (G : ConnGraph) (e : G.V ≃ Fin n)
    (hsigned : Matrix.reindex e e G.signedLaplacianMobius =
      signedCycleLaplacian n (by omega)) :
    G.signedLaplacianMobius.charpoly.roots =
      Multiset.map
        (fun k : Fin n =>
          2 - 2 * Real.cos ((2 * k.val + 1) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val := by
  rw [← Matrix.charpoly_reindex e G.signedLaplacianMobius, hsigned]
  exact signedCycle_roots_real n hn

/-- The *full connection* Laplacian's spectrum is the sum of both cycle
spectral multisets whenever both graph-to-matrix reindexings are proved.
This assembles the established arbitrary-ConnGraph spectral splitting
with the specialised full Fourier spectrum without dropping multiplicity. -/
theorem mobius_connection_roots_of_cycle_reindex (n : ℕ) (hn : 3 ≤ n)
    (G : ConnGraph) (e : G.V ≃ Fin n)
    (hscalar : Matrix.reindex e e G.scalarLaplacian =
      scalarCycleLaplacian n (by omega))
    (hsigned : Matrix.reindex e e G.signedLaplacianMobius =
      signedCycleLaplacian n (by omega)) :
    (G.laplacian true).charpoly.roots =
      Multiset.map
        (fun k : Fin n => 2 - 2 * Real.cos (2 * Real.pi * k.val / n))
        (Finset.univ : Finset (Fin n)).val +
      Multiset.map
        (fun k : Fin n =>
          2 - 2 * Real.cos ((2 * k.val + 1) * Real.pi / n))
        (Finset.univ : Finset (Fin n)).val := by
  rw [G.mobius_charpoly_roots_eq_union,
    scalarCycle_roots_of_graph_reindex n hn G e hscalar,
    signedCycle_roots_of_graph_reindex n hn G e hsigned]

end ConnectionLaplacian.Cycle
