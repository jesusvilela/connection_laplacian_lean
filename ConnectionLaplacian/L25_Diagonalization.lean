/-
ConnectionLaplacian/L25_Diagonalization.lean

**Stratum L25 — Block Diagonalization via DFT.**

This file contains the typed L25 statement for DFT diagonalization. The earlier
version mixed `ZMod n` and `Fin n` indices, so it did not elaborate. The present
version keeps the explicit DFT matrices but writes them with `Fin n` indices to
match `coverLaplacian`.
-/

import ConnectionLaplacian.L21_SectoralDecomposition
import ConnectionLaplacian.L23_DFT
import Mathlib.Data.Matrix.Kronecker

namespace ConnectionLaplacian

open Matrix BigOperators Complex
open scoped Kronecker

variable {n : Nat} [NeZero n] (Z : ZnConnGraph n)

/-- Fin-indexed DFT matrix, matching the positive-exponent convention from L21. -/
noncomputable def dftMatrixFin (n : Nat) [NeZero n] : Matrix (Fin n) (Fin n) ℂ := fun k x =>
  (ZnConnGraph.ω n) ^ ((k.val * x.val : ℤ))

/-- Fin-indexed inverse DFT matrix, matching the negative-exponent convention from L21. -/
noncomputable def dftInverseFin (n : Nat) [NeZero n] : Matrix (Fin n) (Fin n) ℂ := fun x k =>
  (ZnConnGraph.ω n) ^ (-((k.val * x.val : ℤ)))

/--
The block diagonal matrix of sectoral Laplacians.

`Matrix.blockDiagonal` already uses the `(u, k)` convention on indices, so this
is exactly the direct sum of the matrices `sectoralLaplacian Z k`.
-/
noncomputable def sectoralBlocks : Matrix (Z.V × Fin n) (Z.V × Fin n) ℂ :=
  Matrix.blockDiagonal (fun k : Fin n => sectoralLaplacian Z k)

@[simp] lemma sectoralBlocks_apply (u v : Z.V) (k l : Fin n) :
    sectoralBlocks Z (u, k) (v, l) = if k = l then sectoralLaplacian Z k u v else 0 := by
  by_cases h : k = l
  · subst h
    simp [sectoralBlocks, Matrix.reindex_apply, Matrix.blockDiagonal_apply_eq]
  · simp [sectoralBlocks, Matrix.reindex_apply, Matrix.blockDiagonal_apply_ne, h]

/--
THEOREM: the cover Laplacian is similar to the direct sum of the sectoral
Laplacians via the finite Fourier transform.

The L21 file already proves the same statement existentially using the auxiliary
matrices `Pmat` / `PmatInv`. The remaining work here is a pure algebraic bridge:
identify those matrices with `dftMatrixFin` / `dftInverseFin` and rewrite the
existing intertwining proof in these explicit DFT coordinates.
-/
lemma dftMatrixFin_mul_dftInverseFin :
    dftMatrixFin n * dftInverseFin n = (n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  calc
    ∑ k : Fin n, dftMatrixFin n i k * dftInverseFin n k j
        = ∑ k : Fin n, (ZnConnGraph.ω n) ^ (((i.val : ℤ) - j.val) * k.val : ℤ) := by
            refine Finset.sum_congr rfl ?_
            intro k _
            dsimp [dftMatrixFin, dftInverseFin]
            rw [← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
            congr 1
            ring
    _ = if (n : ℤ) ∣ ((i.val : ℤ) - j.val) then (n : ℂ) else 0 :=
          sum_fin_omega_mul (n := n) (((i.val : ℤ) - j.val))
    _ = if i = j then (n : ℂ) else 0 := by
          by_cases hij : i = j
          · simp [hij]
          · have hji : j ≠ i := by
              intro h
              exact hij h.symm
            simp [hij, hji, fin_sub_dvd_iff_eq (n := n) j i]
    _ = (n : ℂ) * (if i = j then 1 else 0) := by
          split_ifs <;> simp

lemma dftMatrixFin_mul_dftInverseFin_kronecker :
    (((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftMatrixFin n) *
      ((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n))) = 1 := by
  rw [Matrix.mul_smul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    dftMatrixFin_mul_dftInverseFin, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp [hn0]

theorem laplacian_dft_diagonalization :
    let P := (1 : Matrix Z.V Z.V ℂ) ⊗ₖ (dftMatrixFin n)
    let P_inv := (1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ (dftInverseFin n))
    P * (coverLaplacian Z) * P_inv = sectoralBlocks Z := by
  dsimp
  have hinter :
      (coverLaplacian Z) * ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n) =
        ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n) * sectoralBlocks Z := by
    simpa [dftInverseFin, sectoralBlocks] using (ConnectionLaplacian.intertwining (n := n) Z)
  have hscaled :
      (coverLaplacian Z) * ((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n)) =
        ((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n)) * sectoralBlocks Z := by
    calc
      (coverLaplacian Z) * ((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n))
          = (1 / (n : ℂ)) • ((coverLaplacian Z) * ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n)) := by
              rw [Matrix.mul_smul]
      _ = (1 / (n : ℂ)) • (((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n) * sectoralBlocks Z) := by
            rw [hinter]
      _ = ((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n)) * sectoralBlocks Z := by
            rw [Matrix.smul_mul]
  calc
    (((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftMatrixFin n) * coverLaplacian Z) *
        ((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n))
        = ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftMatrixFin n) *
            ((coverLaplacian Z) * ((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n))) := by
            rw [Matrix.mul_assoc]
    _ = ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftMatrixFin n) *
          (((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n)) * sectoralBlocks Z) := by
            rw [hscaled]
    _ = ((((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftMatrixFin n) *
          ((1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ dftInverseFin n))) * sectoralBlocks Z) := by
            rw [← Matrix.mul_assoc]
    _ = sectoralBlocks Z := by
          rw [dftMatrixFin_mul_dftInverseFin_kronecker (Z := Z), Matrix.one_mul]

end ConnectionLaplacian
