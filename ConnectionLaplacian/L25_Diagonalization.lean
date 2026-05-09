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
theorem laplacian_dft_diagonalization :
    let P := (1 : Matrix Z.V Z.V ℂ) ⊗ₖ (dftMatrixFin n)
    let P_inv := (1 / (n : ℂ)) • ((1 : Matrix Z.V Z.V ℂ) ⊗ₖ (dftInverseFin n))
    P * (coverLaplacian Z) * P_inv = sectoralBlocks Z := by
  /-
  Remaining Lean gap:
  * prove that `P_inv` is the `Pmat` witness from `L21_SectoralDecomposition`
    and that `P` is its inverse;
  * transfer the already-established intertwining relation to this explicit DFT
    presentation.
  -/
  sorry

end ConnectionLaplacian
