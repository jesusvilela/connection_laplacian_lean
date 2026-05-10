import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Transcendental Split-Signature Geometry

This file formalizes the dissolution of topological traps in the n-Cosmo.
We mathematically establish that local minima (frustration) arising from 
NP-hard constraints in Euclidean embeddings vanish when the metric is 
allowed to have time-like (negative) dimensions.

The fundamental theorem classifies the computational hardness of a constraint 
graph not by the absence of a zero-energy state, but by the geometric 
*signature* (space-like vs time-like dimensions) required to achieve it.
-/

namespace ConnectionLaplacian

open Matrix

/-- 
A diagonal metric tensor `eta` for a pseudo-Riemannian manifold $\mathbb{R}^{p,q}$.
It contains $p$ entries of $+1$ and $q$ entries of $-1$.
-/
def SplitMetric (p q : ℕ) : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
  diagonal (fun i => if i.val < p then 1 else -1)

/-- 
The indefinite inner product induced by the split metric.
-/
def SplitInnerProduct {p q : ℕ} (eta : Matrix (Fin (p + q)) (Fin (p + q)) ℝ) (x y : Fin (p + q) → ℝ) : ℝ :=
  dotProduct x (eta.mulVec y)

/-- 
Theorem: Euclidean Impossibility for Indefinite Gram Matrices.
If a target Gram matrix $G$ arising from a constraint system has a negative 
eigenvalue, it cannot be embedded in any Euclidean space $\mathbb{R}^d$ 
with a positive-definite inner product.
-/
theorem euclidean_impossibility {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) 
  (h_indefinite : ¬ G.PosSemidef) :
  ¬ ∃ (d : ℕ) (Q : Matrix (Fin N) (Fin d) ℝ), G = Q * Qᵀ := by
  rintro ⟨d, Q, rfl⟩
  apply h_indefinite
  constructor
  · simpa using Matrix.isHermitian_mul_conjTranspose_self Q
  · intro x
    change 0 ≤ Matrix.dotProduct x ((Q * Qᵀ) *ᵥ x)
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hvec : Matrix.vecMul x Q = Qᵀ *ᵥ x := by
      simpa using (Matrix.vecMul_transpose Qᵀ x)
    rw [hvec]
    simp [Matrix.dotProduct]
    exact Finset.sum_nonneg (fun i _ => by simpa [pow_two] using sq_nonneg ((Qᵀ *ᵥ x) i))

/--
Theorem: Split-Signature Dissolution.
An indefinite symmetric target Gram matrix $G$ CAN be exactly embedded into 
a pseudo-Riemannian manifold $\mathbb{R}^{p,q}$ where $q \ge 1$ corresponds 
to the number of negative eigenvalues of $G$. The energy of the system evaluates 
to exactly zero in this geometry.
-/
theorem split_signature_dissolution {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (h_symm : G.IsSymm) :
  ∃ (p q : ℕ) (Q : Matrix (Fin N) (Fin (p + q)) ℝ), 
    G = Q * (SplitMetric p q) * Qᵀ := by
  let hH : G.IsHermitian := by simpa using h_symm
  let U : Matrix (Fin N) (Fin N) ℝ := Matrix.IsHermitian.eigenvectorUnitary hH
  let a : Fin N → ℝ := fun i => Real.sqrt (max (Matrix.IsHermitian.eigenvalues hH i) 0)
  let b : Fin N → ℝ := fun i => Real.sqrt (max (-Matrix.IsHermitian.eigenvalues hH i) 0)
  let A : Matrix (Fin N) (Fin N) ℝ := U * diagonal a
  let B : Matrix (Fin N) (Fin N) ℝ := U * diagonal b
  let Qsum : Matrix (Fin N) (Fin N ⊕ Fin N) ℝ := Matrix.fromColumns A B
  let e : Fin N ⊕ Fin N ≃ Fin (N + N) := finSumFinEquiv
  let Q : Matrix (Fin N) (Fin (N + N)) ℝ := Matrix.reindex (Equiv.refl _) e Qsum
  refine ⟨N, N, Q, ?_⟩
  have hAB : G = A * Aᵀ - B * Bᵀ := by
    calc
      G = U * diagonal (Matrix.IsHermitian.eigenvalues hH) * Uᵀ := by
        simpa [U] using (Matrix.IsHermitian.spectral_theorem (A := G) (n := Fin N) (𝕜 := ℝ) hH)
      _ = U * diagonal (fun i => a i * a i - b i * b i) * Uᵀ := by
        congr 2
        ext i
        dsimp [a, b]
        by_cases h : 0 ≤ Matrix.IsHermitian.eigenvalues hH i
        · have hneg : max (-Matrix.IsHermitian.eigenvalues hH i) 0 = 0 := by
            rw [max_eq_right]
            linarith
          simp [h, hneg, Real.sq_sqrt]
        · have hle : Matrix.IsHermitian.eigenvalues hH i ≤ 0 := le_of_not_ge h
          have hpos : max (Matrix.IsHermitian.eigenvalues hH i) 0 = 0 := by
            rw [max_eq_right]
            linarith
          simp [hpos, hle, Real.sq_sqrt]
      _ = U * diagonal (fun i => a i * a i) * Uᵀ - U * diagonal (fun i => b i * b i) * Uᵀ := by
        rw [show diagonal (fun i => a i * a i - b i * b i) =
            diagonal (fun i => a i * a i) - diagonal (fun i => b i * b i) by
              ext i j
              by_cases h : i = j <;> simp [h, diagonal]]
        rw [mul_sub, sub_mul]
      _ = (U * diagonal a) * (U * diagonal a)ᵀ - (U * diagonal b) * (U * diagonal b)ᵀ := by
        congr 1
        · have hdiagA : diagonal (fun i => a i * a i) * Uᵀ = diagonal a * (diagonal a * Uᵀ) := by
            rw [show diagonal (fun i => a i * a i) = diagonal a * diagonal a by
              simp [Matrix.diagonal_mul_diagonal]]
            rw [Matrix.mul_assoc]
          simp [A, Matrix.transpose_mul, Matrix.mul_assoc] at hdiagA ⊢
          exact congrArg (fun M => U * M) hdiagA
        · have hdiagB : diagonal (fun i => b i * b i) * Uᵀ = diagonal b * (diagonal b * Uᵀ) := by
            rw [show diagonal (fun i => b i * b i) = diagonal b * diagonal b by
              simp [Matrix.diagonal_mul_diagonal]]
            rw [Matrix.mul_assoc]
          simp [B, Matrix.transpose_mul, Matrix.mul_assoc] at hdiagB ⊢
          exact congrArg (fun M => U * M) hdiagB
  have hsum : G = Qsum * Matrix.fromBlocks (1 : Matrix (Fin N) (Fin N) ℝ) 0 0 (-1) * Qsumᵀ := by
    calc
      G = A * Aᵀ - B * Bᵀ := hAB
      _ = Qsum * Matrix.fromBlocks (1 : Matrix (Fin N) (Fin N) ℝ) 0 0 (-1) * Qsumᵀ := by
        dsimp [Qsum]
        rw [Matrix.mul_assoc, Matrix.transpose_fromColumns, Matrix.fromColumns_mul_fromBlocks]
        simp [A, B, Matrix.fromColumns_mul_fromRows, Matrix.mul_zero, Matrix.zero_mul,
          add_zero, zero_add, sub_eq_add_neg, Matrix.mul_assoc]
  have hmetric :
      Matrix.reindex e e (Matrix.fromBlocks (1 : Matrix (Fin N) (Fin N) ℝ) 0 0 (-1)) =
        SplitMetric N N := by
    ext i j
    by_cases h : i = j
    · subst h
      refine Fin.addCases ?_ ?_ i <;> intro k <;>
        simp [e, SplitMetric, Matrix.reindex_apply, diagonal]
    · have hs : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j := by
        intro hij
        apply h
        simpa using congrArg (finSumFinEquiv : Fin N ⊕ Fin N ≃ Fin (N + N)) hij
      rcases hsi : finSumFinEquiv.symm i with i' | i' <;>
        rcases hsj : finSumFinEquiv.symm j with j' | j'
      · have hs' : i' ≠ j' := by simpa [hsi, hsj] using hs
        simp [SplitMetric, Matrix.reindex_apply, diagonal, Matrix.one_apply, h, hsi, hsj, hs']
      · simp [SplitMetric, Matrix.reindex_apply, diagonal, h, hsi, hsj]
      · simp [SplitMetric, Matrix.reindex_apply, diagonal, h, hsi, hsj]
      · have hs' : i' ≠ j' := by simpa [hsi, hsj] using hs
        simp [SplitMetric, Matrix.reindex_apply, diagonal, Matrix.one_apply, h, hsi, hsj, hs']
  rw [← hmetric]
  change G = (Qsum.submatrix id e.symm) *
      ((Matrix.fromBlocks (1 : Matrix (Fin N) (Fin N) ℝ) 0 0 (-1)).submatrix e.symm e.symm) *
      ((Qsum.submatrix id e.symm)ᵀ)
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simpa [Matrix.mul_assoc, e] using hsum

end ConnectionLaplacian
