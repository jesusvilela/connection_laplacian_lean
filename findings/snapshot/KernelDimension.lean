/-
ConnectionLaplacian/KernelDimension.lean

Theorem 1: The kernel dimension of the connection Laplacian distinguishes
Möbius from flat bundles, and more specifically counts signed connected
components determined by the parity of wrap edges per component.

Proof strategy:
  1. Decompose ℝ² into σ_x-eigenspaces: E_+ (symmetric, eigenvalue +1) and
     E_- (antisymmetric, eigenvalue −1).
  2. The connection Laplacian L = L_sym ⊕ L_anti where
       L_sym  acts on V ⊗ E_+ as the ordinary scalar graph Laplacian of G
       L_anti acts on V ⊗ E_- as the SIGNED Laplacian where interior edges
              have weight +1 and wrap edges have weight −1
  3. Flat bundle: L_anti ≡ L_sym (both ordinary), total nullity 2 · (#CCs).
  4. Möbius bundle: L_sym nullity = #CCs, L_anti nullity = #CCs − (#odd-wrap).
  5. Total Möbius nullity = 2·#CCs − (#odd-wrap).

The scalar graph Laplacian's kernel dimension is closed via Mathlib's
`card_ConnectedComponent_eq_rank_ker_lapMatrix` in
`Mathlib.Combinatorics.SimpleGraph.LapMatrix`.
-/

import ConnectionLaplacian.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Matrix.Kronecker

namespace ConnectionLaplacian

open Matrix BigOperators
open scoped Kronecker

namespace ConnGraph

variable (G : ConnGraph)

/-- Number of connected components of the underlying simple graph. -/
noncomputable def numComponents : ℕ :=
  Fintype.card G.graph.ConnectedComponent

/-- For each connected component C, the number of wrap edges both of whose
endpoints lie in C. Since an edge's two endpoints are adjacent, they lie in
the same component, so it suffices to require that some endpoint lies in C. -/
noncomputable def wrapEdgesIn (C : G.graph.ConnectedComponent) : ℕ := by
  classical
  exact Fintype.card
    { e : G.graph.edgeSet //
      G.wrap e ∧ ∃ v : G.V, v ∈ (e.val : Sym2 G.V) ∧
        G.graph.connectedComponentMk v = C }

/-- A component has "odd wrap parity" if it contains an odd number of wrap edges. -/
def hasOddWrapParity (C : G.graph.ConnectedComponent) : Prop :=
  Odd (G.wrapEdgesIn C)

noncomputable instance decHasOdd (C : G.graph.ConnectedComponent) :
    Decidable (G.hasOddWrapParity C) := Classical.dec _

noncomputable def numOddWrapComponents : ℕ :=
  Fintype.card { C : G.graph.ConnectedComponent // G.hasOddWrapParity C }

/-- The symmetric-subspace Laplacian is the ordinary scalar graph Laplacian
of `G` (Mathlib's `lapMatrix`). All edges contribute +1 on the σ_x symmetric
eigenspace, wrap or interior. -/
noncomputable def scalarLaplacian : Matrix G.V G.V ℝ :=
  G.graph.lapMatrix ℝ

/-- The antisymmetric-subspace Laplacian for the Möbius bundle: the signed
Laplacian where wrap edges enter with sign opposite to interior edges. On
interior edges the off-diagonal entry is −1 (standard Laplacian); on wrap
edges the off-diagonal entry is +1 (σ_x acts as −1 on the antisymmetric
fiber, flipping the overall sign). -/
noncomputable def signedLaplacianMobius : Matrix G.V G.V ℝ :=
  fun u v =>
    if u = v then (G.graph.neighborFinset u).card
    else if h : G.graph.Adj u v then
      let e : G.graph.edgeSet := ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
      if G.wrap e then 1 else -1
    else 0

/-- Re-indexing equivalence: `G.V × Fin 2 ≃ G.V ⊕ G.V`, sending `(v, 0) ↦ inl v`
and `(v, 1) ↦ inr v`. Used to align the block structure of the connection
Laplacian with Mathlib's `Matrix.fromBlocks`. -/
def prodFinTwoEquivSum : G.V × Fin 2 ≃ G.V ⊕ G.V :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongr finTwoEquiv (Equiv.refl _)).trans (Equiv.boolProdEquivSum _))

/-- The unnormalized Hadamard rotation R̂ = !![1,1;1,-1]. After conjugating
σ_x this goes to diag(2, -2); after conjugating I₂ it stays diag(2, 2). The
common factor of 2 is absorbed by using (1/2)·P as the matrix inverse of
the block-diagonal P built from R̂. -/
private def RhatMob : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

private lemma RhatMob_sq :
    RhatMob * RhatMob = !![2, 0; 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RhatMob, Matrix.mul_fin_two] <;> norm_num

private lemma RhatMob_I₂_RhatMob :
    RhatMob * I₂ * RhatMob = !![2, 0; 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RhatMob, I₂, Matrix.mul_fin_two] <;> norm_num

private lemma RhatMob_σx_RhatMob :
    RhatMob * σx * RhatMob = !![2, 0; 0, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RhatMob, σx, Matrix.mul_fin_two] <;> norm_num

/-- Flat entry-wise: in flat mode the connection Laplacian is fiber-diagonal,
with each fiber copy equal to the scalar Laplacian. -/
private lemma laplacian_flat_entry (u v : G.V) (i j : Fin 2) :
    G.laplacian false (u, i) (v, j) =
      if i = j then G.scalarLaplacian u v else 0 := by
  show (G.laplacianBlock false u v) i j = _
  unfold laplacianBlock degreeBlockMatrix adjacencyMatrix edgeMatrix scalarLaplacian
  simp only [Bool.false_and, if_false, Matrix.sub_apply,
             SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
             SimpleGraph.adjMatrix_apply, Matrix.diagonal_apply]
  by_cases huv : u = v
  · subst huv
    have hna : ¬ G.graph.Adj u u := SimpleGraph.irrefl _
    rw [dif_neg hna, if_pos rfl, if_pos rfl, if_neg hna]
    simp only [Matrix.zero_apply, sub_zero]
    unfold degree SimpleGraph.degree
    fin_cases i <;> fin_cases j <;> simp [I₂]
  · rw [if_neg huv, if_neg huv]
    simp only [Matrix.zero_apply, zero_sub]
    by_cases hadj : G.graph.Adj u v
    · rw [dif_pos hadj]
      fin_cases i <;> fin_cases j <;> simp [I₂, hadj]
    · rw [dif_neg hadj]
      fin_cases i <;> fin_cases j <;> simp [hadj]

/-- Möbius entry-wise after Hadamard rotation: (R̂·L_block·R̂)(i,j) splits
fiber-diagonally into 2·scalarLap (on symmetric fiber i=j=0) and 2·signedLap
(on antisymmetric fiber i=j=1). The factor of 2 is absorbed by P⁻¹ = (1/2)•P
in the main theorem. Case analysis parallels `laplacian_flat_entry`. -/
private lemma laplacian_mobius_rotated_entry (u v : G.V) (i j : Fin 2) :
    (RhatMob * G.laplacianBlock true u v * RhatMob) i j =
      if i = j then
        2 * (if i = (0 : Fin 2) then G.scalarLaplacian u v
             else G.signedLaplacianMobius u v)
      else 0 := by
  by_cases huv : u = v
  · -- Diagonal case: L_block true u u = deg u • I₂
    subst huv
    have hna : ¬ G.graph.Adj u u := SimpleGraph.irrefl _
    have hlap : G.laplacianBlock true u u = (G.degree u : ℝ) • I₂ := by
      unfold laplacianBlock degreeBlockMatrix adjacencyMatrix
      ext k l
      simp only [Matrix.sub_apply, if_pos rfl, dif_neg hna,
                 Matrix.zero_apply, sub_zero, if_true]
    rw [hlap, Matrix.mul_smul, Matrix.smul_mul, RhatMob_I₂_RhatMob]
    simp only [Matrix.smul_apply, smul_eq_mul]
    unfold scalarLaplacian signedLaplacianMobius
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
               Matrix.diagonal_apply_eq, SimpleGraph.adjMatrix_apply,
               if_pos rfl, if_neg hna, Matrix.zero_apply, sub_zero]
    unfold degree SimpleGraph.degree
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      ring
  · -- Off-diagonal case: case split on adjacency and (if adj) on wrap
    by_cases hadj : G.graph.Adj u v
    · -- adjacent
      by_cases hwrap : G.wrap ⟨s(u,v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
      · -- wrap edge (Möbius): L_block = -σx
        have hlap : G.laplacianBlock true u v = -σx := by
          unfold laplacianBlock degreeBlockMatrix adjacencyMatrix edgeMatrix
          ext k l
          simp only [Matrix.sub_apply, if_neg huv, Matrix.zero_apply,
                     zero_sub, dif_pos hadj, true_and, if_pos hwrap,
                     Matrix.neg_apply]
        rw [hlap]
        rw [show (-σx : Matrix (Fin 2) (Fin 2) ℝ) = (-1 : ℝ) • σx from by
              rw [neg_one_smul]]
        rw [Matrix.mul_smul, Matrix.smul_mul, RhatMob_σx_RhatMob]
        simp only [Matrix.smul_apply, smul_eq_mul]
        unfold scalarLaplacian signedLaplacianMobius
        simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
                   Matrix.diagonal_apply_ne _ huv, SimpleGraph.adjMatrix_apply,
                   if_pos hadj, if_neg huv, Matrix.zero_apply, zero_sub,
                   dif_pos hadj, if_pos hwrap]
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · -- interior edge (Möbius non-wrap): L_block = -I₂
        have hlap : G.laplacianBlock true u v = -I₂ := by
          unfold laplacianBlock degreeBlockMatrix adjacencyMatrix edgeMatrix
          ext k l
          simp only [Matrix.sub_apply, if_neg huv, Matrix.zero_apply,
                     zero_sub, dif_pos hadj, true_and, if_neg hwrap,
                     Matrix.neg_apply]
        rw [hlap]
        rw [show (-I₂ : Matrix (Fin 2) (Fin 2) ℝ) = (-1 : ℝ) • I₂ from by
              rw [neg_one_smul]]
        rw [Matrix.mul_smul, Matrix.smul_mul, RhatMob_I₂_RhatMob]
        simp only [Matrix.smul_apply, smul_eq_mul]
        unfold scalarLaplacian signedLaplacianMobius
        simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
                   Matrix.diagonal_apply_ne _ huv, SimpleGraph.adjMatrix_apply,
                   if_pos hadj, if_neg huv, Matrix.zero_apply, zero_sub,
                   dif_pos hadj, if_neg hwrap]
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · -- non-adjacent: L_block = 0
      have hlap : G.laplacianBlock true u v = 0 := by
        unfold laplacianBlock degreeBlockMatrix adjacencyMatrix
        ext k l
        simp only [Matrix.sub_apply, if_neg huv, Matrix.zero_apply,
                   zero_sub, dif_neg hadj, neg_zero]
      rw [hlap, Matrix.mul_zero, Matrix.zero_mul]
      unfold scalarLaplacian signedLaplacianMobius
      simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
                 Matrix.diagonal_apply_ne _ huv, SimpleGraph.adjMatrix_apply,
                 if_neg hadj, Matrix.zero_apply, sub_zero, zero_sub, neg_zero,
                 if_neg huv, dif_neg hadj]
      split_ifs <;> simp

/-- Decomposition spec: after a block change of basis the connection
Laplacian splits into a direct sum of the scalar Laplacian (symmetric fiber)
and either the scalar Laplacian (flat case) or the signed Laplacian (Möbius
case). The concrete P for Möbius is I_V ⊗ R where R = (1/√2)[[1,1],[1,-1]]
diagonalises σ_x; for flat P = 1 suffices. Decomposition is stated up to the
reindex `prodFinTwoEquivSum : G.V × Fin 2 ≃ G.V ⊕ G.V`. -/
theorem laplacian_decomposes (mobius : Bool) :
    ∃ (P : Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ),
      P.det ≠ 0 ∧
      (Matrix.reindex G.prodFinTwoEquivSum G.prodFinTwoEquivSum
          (P * G.laplacian mobius * P⁻¹) =
        Matrix.fromBlocks
          G.scalarLaplacian
          (0 : Matrix G.V G.V ℝ)
          (0 : Matrix G.V G.V ℝ)
          (if mobius then G.signedLaplacianMobius else G.scalarLaplacian)) := by
  cases mobius with
  | false =>
    -- Flat: P = 1 suffices. L_false is already fiber-diagonal.
    refine ⟨1, by simp, ?_⟩
    have hconj : (1 : Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ) * G.laplacian false * 1⁻¹
               = G.laplacian false := by
      rw [inv_one, Matrix.mul_one, Matrix.one_mul]
    rw [hconj]
    simp only [Bool.false_eq_true, if_false]
    ext a b
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    have hsym_inl : ∀ w : G.V, G.prodFinTwoEquivSum.symm (Sum.inl w) = (w, 0) := by
      intro w; rfl
    have hsym_inr : ∀ w : G.V, G.prodFinTwoEquivSum.symm (Sum.inr w) = (w, 1) := by
      intro w; rfl
    rcases a with u | u <;> rcases b with v | v
    · rw [hsym_inl, hsym_inl, Matrix.fromBlocks_apply₁₁,
          G.laplacian_flat_entry u v 0 0, if_pos rfl]
    · rw [hsym_inl, hsym_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
          G.laplacian_flat_entry u v 0 1, if_neg (by decide)]
    · rw [hsym_inr, hsym_inl, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
          G.laplacian_flat_entry u v 1 0, if_neg (by decide)]
    · rw [hsym_inr, hsym_inr, Matrix.fromBlocks_apply₂₂,
          G.laplacian_flat_entry u v 1 1, if_pos rfl]
  | true =>
    -- Möbius: similarity P = 1_V ⊗ₖ R̂ with R̂ = !![1,1;1,-1].
    -- R̂² = 2•I₂, so P² = 2•1 and P⁻¹ = (1/2)•P via Matrix.inv_eq_right_inv.
    -- Conjugation expands entry-wise via two Finset.sum_eq_single collapses,
    -- then laplacian_mobius_rotated_entry gives the block-diagonal content.
    let P : Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ :=
      (1 : Matrix G.V G.V ℝ) ⊗ₖ RhatMob
    have hRhatMob_sq' : RhatMob * RhatMob =
        (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [RhatMob_sq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have hPP : P * P = (2 : ℝ) • (1 : Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ) := by
      show ((1 : Matrix G.V G.V ℝ) ⊗ₖ RhatMob) *
          ((1 : Matrix G.V G.V ℝ) ⊗ₖ RhatMob)
        = (2 : ℝ) • (1 : Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ)
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, hRhatMob_sq',
          Matrix.kronecker_smul, Matrix.one_kronecker_one]
    have hPinvP : P * ((1/2 : ℝ) • P) = 1 := by
      rw [Matrix.mul_smul, hPP, smul_smul]
      norm_num
    have hPinv_eq : P⁻¹ = (1/2 : ℝ) • P := Matrix.inv_eq_right_inv hPinvP
    have hdet : P.det ≠ 0 := by
      intro h
      have hd := congrArg Matrix.det hPinvP
      rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hd
      exact zero_ne_one hd
    have hPent : ∀ (u v : G.V) (i j : Fin 2),
        P (u, i) (v, j) = if u = v then RhatMob i j else 0 := by
      intro u v i j
      show ((1 : Matrix G.V G.V ℝ) ⊗ₖ RhatMob) (u, i) (v, j) = _
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
      split_ifs with huv
      · rw [one_mul]
      · rw [zero_mul]
    have hPL : ∀ (u v : G.V) (i j : Fin 2),
        (P * G.laplacian true) (u, i) (v, j) =
          (RhatMob * G.laplacianBlock true u v) i j := by
      intro u v i j
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single u]
      · rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [hPent u u i k, if_pos rfl]
        rfl
      · intro w _ hne
        apply Finset.sum_eq_zero
        intro k _
        rw [hPent u w i k, if_neg hne.symm, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hPLP : ∀ (u v : G.V) (i j : Fin 2),
        ((P * G.laplacian true) * P) (u, i) (v, j) =
          (RhatMob * G.laplacianBlock true u v * RhatMob) i j := by
      intro u v i j
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single v]
      · conv_rhs => rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [hPL u v i k, hPent v v k j, if_pos rfl]
      · intro w _ hne
        apply Finset.sum_eq_zero
        intro k _
        rw [hPent w v k j, if_neg hne, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    refine ⟨P, hdet, ?_⟩
    rw [hPinv_eq, Matrix.mul_smul]
    simp only [if_true]
    ext a b
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
        smul_eq_mul]
    have hsym_inl : ∀ w : G.V, G.prodFinTwoEquivSum.symm (Sum.inl w) = (w, 0) := by
      intro w; rfl
    have hsym_inr : ∀ w : G.V, G.prodFinTwoEquivSum.symm (Sum.inr w) = (w, 1) := by
      intro w; rfl
    rcases a with u | u <;> rcases b with v | v
    · rw [hsym_inl, hsym_inl, Matrix.fromBlocks_apply₁₁, hPLP u v 0 0,
          G.laplacian_mobius_rotated_entry u v 0 0, if_pos rfl, if_pos rfl]
      ring
    · rw [hsym_inl, hsym_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
          hPLP u v 0 1, G.laplacian_mobius_rotated_entry u v 0 1,
          if_neg (by decide : (0:Fin 2) ≠ 1)]
      ring
    · rw [hsym_inr, hsym_inl, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
          hPLP u v 1 0, G.laplacian_mobius_rotated_entry u v 1 0,
          if_neg (by decide : (1:Fin 2) ≠ 0)]
      ring
    · rw [hsym_inr, hsym_inr, Matrix.fromBlocks_apply₂₂, hPLP u v 1 1,
          G.laplacian_mobius_rotated_entry u v 1 1, if_pos rfl,
          if_neg (by decide : (1:Fin 2) ≠ 0)]
      ring

/-- Kernel dimension of the ordinary scalar Laplacian equals the number of
connected components. Closed via Mathlib's
`SimpleGraph.card_ConnectedComponent_eq_rank_ker_lapMatrix`. -/
theorem scalarLaplacian_kernel_dim :
    FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' G.scalarLaplacian)) =
      G.numComponents := by
  unfold scalarLaplacian numComponents
  exact (G.graph.card_ConnectedComponent_eq_rank_ker_lapMatrix).symm

/-- Trivial bound: the number of odd-wrap components is at most the total
number of connected components. -/
lemma numOddWrapComponents_le :
    G.numOddWrapComponents ≤ G.numComponents := by
  unfold numOddWrapComponents numComponents
  exact Fintype.card_subtype_le _

/-
The historical `signedLaplacian_kernel_dim`, `connectionLaplacian_kernel_dim`,
and `mobius_kernel_strict_iff` lived here with `= numComponents − numOddWrapComponents`
on their RHS. That RHS is FALSE on arbitrary wrap (counterexample: K₄ with
wrap = {a–b, a–c} — one odd-count component, but the component is already
unbalanced by the non-wrap edge (b,c) forming a 3-cycle with sign flip). The
correct statement uses `numBalancedComponents` and lives in
`ConnectionLaplacian.L8_Recognition` as `…_general`. See
`memory/signed_kernel_dim_false.md` for the counterexample derivation.
-/

end ConnGraph

end ConnectionLaplacian
