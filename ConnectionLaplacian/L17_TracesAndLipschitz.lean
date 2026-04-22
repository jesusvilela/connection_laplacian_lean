/-
ConnectionLaplacian/L17_TracesAndLipschitz.lean

**Stratum L17 — Corollary bundle (Tier A: trace/determinant identities).**

All Tier A results are direct corollaries of M7 (charpoly factorisation,
`mobius_charpoly_eq_scalar_times_signed` in L16) or the block
decomposition `laplacian_decomposes` (L4) plus the trace formulas from L9.

Landed in this file (Tier A):
1. `shiftedDet_factorises` (S1) — `det(α•1 − L_möb) = det(α•1 − L_s) · det(α•1 − L_sig)`.
2. `trace_sq_laplacian_decomposes` (S3) — `tr(L_möb²) = tr(L_s²) + tr(L_sig²)`.
3. `frobenius_laplacian_decomposes` (S4) — Frobenius-² splits.
4. `trace_mul_scalar_signed_eq` (S2, polarisation form) — mixed trace.
5. `trace_laplacian_mobius` (S5) — `tr(L_möb) = 4·|E|`.

Tier B (Lipschitz bundle, S6–S9) is deferred to R7. The β-Lipschitz
machinery requires Weyl interlacing at the level of `finrank` across
distinct underlying vertex types, which L15 does not currently expose
in the shape needed. Detailed rationale in the R6 Stage-7 report.

No `sorry`, no `native_decide`, no new axioms.
-/

import ConnectionLaplacian.L16_SpectrumUnion
import ConnectionLaplacian.L9_Bounds
import ConnectionLaplacian.L13_PSD
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L17.1 — Shifted-determinant factorisation (S1). -/

/-- Evaluate the charpoly of `M` at a scalar `α` to recover
`det(α • 1 − M)`. Standard Mathlib corollary of `eval_det` and
`matPolyEquiv_charmatrix`. -/
private lemma charpoly_eval_eq_det_sub {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (M : Matrix n n R) (α : R) :
    Polynomial.eval α M.charpoly = ((α : R) • (1 : Matrix n n R) - M).det := by
  unfold Matrix.charpoly
  rw [Matrix.eval_det, matPolyEquiv_charmatrix]
  have hX : (Polynomial.eval (Matrix.scalar n α) (Polynomial.X - Polynomial.C M))
            = Matrix.scalar n α - M := by
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hX]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply_eq,
                   Matrix.diagonal_apply_eq]
  · simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply_ne h,
          Matrix.diagonal_apply_ne _ h]

/-- **S1 — Shifted-det factorisation (M7 corollary).**
`det(α • 1 − L_möb) = det(α • 1 − L_s) · det(α • 1 − L_sig)`. -/
theorem shiftedDet_factorises (α : ℝ) :
    (α • (1 : Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ) - G.laplacian true).det
      = (α • (1 : Matrix G.V G.V ℝ) - G.scalarLaplacian).det *
        (α • (1 : Matrix G.V G.V ℝ) - G.signedLaplacianMobius).det := by
  have hcp := G.mobius_charpoly_eq_scalar_times_signed
  have hev := congrArg (Polynomial.eval α) hcp
  rw [Polynomial.eval_mul] at hev
  rw [charpoly_eval_eq_det_sub _ α,
      charpoly_eval_eq_det_sub _ α,
      charpoly_eval_eq_det_sub _ α] at hev
  exact hev

/-! ### L17.2 — Trace of the Möbius connection Laplacian (S5). -/

/-- **S5 — `tr(L_möb) = 4·|E|`.**
Diagonal entry at `(v, i)` equals `deg v` for each `i : Fin 2`, giving
`∑_{(v,i)} deg v = 2·∑_v deg v = 4·|E|` by the handshake lemma. -/
theorem trace_laplacian_mobius :
    (G.laplacian true).trace = (4 * G.graph.edgeFinset.card : ℝ) := by
  unfold Matrix.trace
  have hdiag : ∀ (p : G.V × Fin 2),
      Matrix.diag (G.laplacian true) p = (G.graph.degree p.1 : ℝ) := by
    rintro ⟨v, i⟩
    show G.laplacian true (v, i) (v, i) = _
    simp only [laplacian, laplacianBlock, degreeBlockMatrix,
               adjacencyMatrix, Matrix.sub_apply, if_true]
    have hna : ¬ G.graph.Adj v v := SimpleGraph.irrefl _
    rw [dif_neg hna]
    simp only [Matrix.zero_apply, sub_zero]
    unfold degree SimpleGraph.degree
    fin_cases i <;> simp [I₂]
  simp only [hdiag]
  -- sum over V × Fin 2 = 2 · sum over V, via Fintype.sum_prod_type.
  have hsum : (∑ p : G.V × Fin 2, (G.graph.degree p.1 : ℝ))
              = 2 * ∑ v : G.V, (G.graph.degree v : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
               nsmul_eq_mul]
    rw [← Finset.mul_sum]
    norm_num
  rw [hsum]
  have h := G.graph.sum_degrees_eq_twice_card_edges
  rw [show (∑ v, (G.graph.degree v : ℝ)) = ((∑ v, G.graph.degree v : ℕ) : ℝ) by push_cast; rfl, h]
  push_cast; ring

/-! ### L17.3 — Squared-trace identity (S3).

We use the block-diagonalisation `laplacian_decomposes` (L4) to reduce
`tr(L_möb²)` to `tr((fromBlocks L_s 0 0 L_sig)²)`, then expand block
multiplication. -/

/-- Helper: trace is invariant under reindexing by an `Equiv`. -/
private lemma trace_reindex {α β : Type*} [Fintype α] [Fintype β]
    {R : Type*} [AddCommMonoid R] (e : α ≃ β) (M : Matrix α α R) :
    (Matrix.reindex e e M).trace = M.trace := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

/-- Helper: trace of a `fromBlocks _ 0 0 _` equals the sum of traces of
the diagonal blocks. -/
private lemma trace_fromBlocks_diag {α β : Type*} [Fintype α] [Fintype β]
    {R : Type*} [AddCommMonoid R] (A : Matrix α α R) (B : Matrix β β R) :
    (Matrix.fromBlocks A 0 0 B).trace = A.trace + B.trace := by
  unfold Matrix.trace
  rw [Fintype.sum_sum_type]
  simp [Matrix.diag_apply, Matrix.fromBlocks]

/-- **S3 — Squared-trace splits: `tr(L_möb²) = tr(L_s²) + tr(L_sig²)`.** -/
theorem trace_sq_laplacian_decomposes :
    ((G.laplacian true) * (G.laplacian true)).trace
      = (G.scalarLaplacian * G.scalarLaplacian).trace +
        (G.signedLaplacianMobius * G.signedLaplacianMobius).trace := by
  obtain ⟨P, hPdet, hreindex⟩ := G.laplacian_decomposes true
  have hP_unit : IsUnit P.det := Ne.isUnit hPdet
  set L := G.laplacian true
  -- trace is similarity-invariant: tr(L·L) = tr(PL P⁻¹ · PLP⁻¹).
  have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP_unit
  have hPLP2 : (P * L * P⁻¹) * (P * L * P⁻¹) = P * (L * L) * P⁻¹ := by
    rw [show P * L * P⁻¹ * (P * L * P⁻¹)
          = P * L * (P⁻¹ * P) * L * P⁻¹ by
            simp [Matrix.mul_assoc]]
    rw [hinv, Matrix.mul_one]
    simp [Matrix.mul_assoc]
  have htr_sim : (L * L).trace = ((P * L * P⁻¹) * (P * L * P⁻¹)).trace := by
    rw [hPLP2, Matrix.trace_mul_cycle]
    rw [show P⁻¹ * P * (L * L) = L * L by rw [hinv, Matrix.one_mul]]
  rw [htr_sim]
  -- Use hreindex to rewrite PLP⁻¹ as reindex-of-B.
  set B : Matrix (G.V ⊕ G.V) (G.V ⊕ G.V) ℝ :=
    Matrix.fromBlocks G.scalarLaplacian (0 : Matrix G.V G.V ℝ)
      (0 : Matrix G.V G.V ℝ) G.signedLaplacianMobius with hBdef
  have hB_eq :
      Matrix.reindex G.prodFinTwoEquivSum G.prodFinTwoEquivSum (P * L * P⁻¹) = B := by
    rw [hreindex]; rfl
  -- Rewrite via the reindex-symm trick.
  have hPLPinv_eq :
      P * L * P⁻¹ = Matrix.reindex G.prodFinTwoEquivSum.symm G.prodFinTwoEquivSum.symm B := by
    rw [← hB_eq]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hPLPinv_eq]
  -- trace((reindex B)²) = trace(reindex (B²)) = trace (B²)
  rw [show Matrix.reindex G.prodFinTwoEquivSum.symm G.prodFinTwoEquivSum.symm B *
          Matrix.reindex G.prodFinTwoEquivSum.symm G.prodFinTwoEquivSum.symm B =
          Matrix.reindex G.prodFinTwoEquivSum.symm G.prodFinTwoEquivSum.symm (B * B) from by
        simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]]
  rw [trace_reindex]
  -- Now compute trace (B * B) where B = fromBlocks L_s 0 0 L_sig.
  have hBsq : B * B = Matrix.fromBlocks (G.scalarLaplacian * G.scalarLaplacian) 0 0
                        (G.signedLaplacianMobius * G.signedLaplacianMobius) := by
    rw [hBdef, Matrix.fromBlocks_multiply]
    simp
  rw [hBsq, trace_fromBlocks_diag]

/-! ### L17.4 — Frobenius-squared identity (S4). -/

/-- **S4 — Frobenius squared norm splits.** Since `L_möb`, `L_s`, `L_sig`
are all symmetric, `tr(Aᵀ · A) = tr(A · A)`, and S3 applies. -/
theorem frobenius_laplacian_decomposes :
    ((G.laplacian true)ᵀ * (G.laplacian true)).trace
      = (G.scalarLaplacianᵀ * G.scalarLaplacian).trace +
        (G.signedLaplacianMobiusᵀ * G.signedLaplacianMobius).trace := by
  have hL : (G.laplacian true).IsSymm := G.laplacian_symmetric true
  have hs : G.scalarLaplacian.IsSymm := SimpleGraph.isSymm_lapMatrix _
  have hsig : G.signedLaplacianMobius.IsSymm := G.signedLaplacianMobius_isSymm
  rw [show ((G.laplacian true)ᵀ * (G.laplacian true))
        = (G.laplacian true) * (G.laplacian true) by rw [hL]]
  rw [show (G.scalarLaplacianᵀ * G.scalarLaplacian)
        = G.scalarLaplacian * G.scalarLaplacian by rw [hs]]
  rw [show (G.signedLaplacianMobiusᵀ * G.signedLaplacianMobius)
        = G.signedLaplacianMobius * G.signedLaplacianMobius by rw [hsig]]
  exact G.trace_sq_laplacian_decomposes

/-! ### L17.5 — Mixed trace identity (S2, polarisation form). -/

/-- **S2 — Mixed trace C10 (polarisation form).**
`2·tr(L_s · L_sig) = tr((L_s + L_sig)²) − tr(L_s²) − tr(L_sig²)`. This
is the polarisation identity for trace, using `trace_mul_comm` to
identify the two cross terms. Combined with S3, this expresses
`tr(L_s · L_sig)` purely in terms of single-matrix trace invariants. -/
theorem trace_mul_scalar_signed_eq :
    2 * (G.scalarLaplacian * G.signedLaplacianMobius).trace
      = ((G.scalarLaplacian + G.signedLaplacianMobius) *
           (G.scalarLaplacian + G.signedLaplacianMobius)).trace
        - (G.scalarLaplacian * G.scalarLaplacian).trace
        - (G.signedLaplacianMobius * G.signedLaplacianMobius).trace := by
  have hcomm : (G.signedLaplacianMobius * G.scalarLaplacian).trace
              = (G.scalarLaplacian * G.signedLaplacianMobius).trace :=
    Matrix.trace_mul_comm _ _
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, hcomm]
  ring

end ConnGraph

end ConnectionLaplacian
