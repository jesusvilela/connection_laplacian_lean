/-
ConnectionLaplacian/L16_SpectrumUnion.lean

**Stratum L16 — Spectrum union for the connection Laplacian (M6/M7).**

Form chosen for M6: **charpoly product (M7)**. Multiset/eigenvalue union
(M6) follows as an immediate corollary of charpoly factorisation, because
a polynomial over ℝ of a real-symmetric matrix has, as its roots (with
multiplicity), exactly the eigenvalues of the matrix.

The headline theorem is

  `(G.laplacian true).charpoly =
     G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly`.

For the flat case (`mobius = false`) we also prove

  `(G.laplacian false).charpoly = G.scalarLaplacian.charpoly ^ 2`,

which is the natural specialisation of M6 on the flat bundle.

**Proof strategy.** Exactly the same three-step pattern used in
`cover_charpoly_eq_scalar_times_mobius` (L10):
  1. Take `charpoly` of both sides of `laplacian_decomposes` (L4).
  2. `Matrix.charpoly_reindex` removes the `Matrix.reindex`.
  3. `Matrix.charpoly_conj_of_isUnit_det` (proved in L10) collapses
     `P · L · P⁻¹` to `L`.
  4. `Matrix.charpoly_fromBlocks_zero₁₂` factors the block-diagonal
     charpoly into a product of the two diagonal charpolys.

Since `laplacian_decomposes` already does the hard work of the change of
basis, the M6 / M7 theorem is essentially a thin wrapper around it, in
complete analogy with the cover charpoly split in L10.
-/

import ConnectionLaplacian.L10_CoverCharpoly
import ConnectionLaplacian.KernelDimension

namespace ConnectionLaplacian

open Matrix BigOperators
open Polynomial (C)

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L16.1 — M7: charpoly of the connection Laplacian factors.

The characteristic polynomial of the (2n × 2n) connection Laplacian
factors as a product of the scalar and signed Laplacians' charpolys
(Möbius case) or as the square of the scalar Laplacian's charpoly
(flat case). -/

/-- **M7 (general).** For either mode, the connection Laplacian's
characteristic polynomial factors over the diagonal blocks obtained from
`laplacian_decomposes`. -/
theorem connectionLaplacian_charpoly_decomposes (mobius : Bool) :
    (G.laplacian mobius).charpoly =
      G.scalarLaplacian.charpoly *
        (if mobius then G.signedLaplacianMobius else G.scalarLaplacian).charpoly := by
  -- Extract the similarity+reindex witness from L4.
  obtain ⟨P, hPdet, hreindex⟩ := G.laplacian_decomposes mobius
  -- Step 1. Apply `charpoly` to both sides of the block-similarity identity.
  have hcp := congrArg Matrix.charpoly hreindex
  -- LHS: `charpoly (reindex e e (P · L · P⁻¹))
  --        = charpoly (P · L · P⁻¹) = charpoly L`.
  rw [Matrix.charpoly_reindex] at hcp
  rw [Matrix.charpoly_conj_of_isUnit_det (Ne.isUnit hPdet)] at hcp
  -- RHS: block-diagonal charpoly factors.
  rw [Matrix.charpoly_fromBlocks_zero₁₂] at hcp
  exact hcp

/-- **M7 (Möbius).** The characteristic polynomial of the Möbius
connection Laplacian equals the product of the scalar and signed
(Möbius) Laplacians' characteristic polynomials. This is the
charpoly-level form of the spec-union identity M6. -/
theorem mobius_charpoly_eq_scalar_times_signed :
    (G.laplacian true).charpoly =
      G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly := by
  have h := G.connectionLaplacian_charpoly_decomposes true
  simpa using h

/-- **Flat specialisation.** The flat connection Laplacian's charpoly is
the square of the scalar Laplacian's charpoly (two fiber copies of the
symmetric Laplacian). -/
theorem flat_charpoly_eq_scalar_sq :
    (G.laplacian false).charpoly =
      G.scalarLaplacian.charpoly * G.scalarLaplacian.charpoly := by
  have h := G.connectionLaplacian_charpoly_decomposes false
  simpa using h

/-! ### L16.2 — M6: multiset of eigenvalues as a union.

The multiset of roots (with multiplicity) of `charpoly(A * B)` is the
union of the multisets of roots of `charpoly A` and `charpoly B`. Over
ℝ[X], `Polynomial.roots` delivers exactly this. Combined with M7 we
get M6 in its multiset form.

This avoids any dependence on Mathlib's `Matrix.eigenvalues` (which is
only defined for Hermitian matrices over ℂ via `Matrix.IsHermitian`)
and instead works purely at the level of polynomial roots — which, for
real-symmetric matrices, coincide with eigenvalues.
-/

/-- **M6 (multiset form).** The multiset of charpoly-roots of the
Möbius connection Laplacian equals the disjoint union of the
charpoly-roots of the scalar and signed Laplacians. -/
theorem mobius_charpoly_roots_eq_union :
    (G.laplacian true).charpoly.roots =
      G.scalarLaplacian.charpoly.roots +
        G.signedLaplacianMobius.charpoly.roots := by
  rw [G.mobius_charpoly_eq_scalar_times_signed]
  exact Polynomial.roots_mul (by
    -- The product is nonzero because each factor is a monic polynomial
    -- of positive degree (it's a charpoly over a nontrivial ring).
    have h1 : G.scalarLaplacian.charpoly ≠ 0 :=
      Matrix.charpoly_monic _ |>.ne_zero
    have h2 : G.signedLaplacianMobius.charpoly ≠ 0 :=
      Matrix.charpoly_monic _ |>.ne_zero
    exact mul_ne_zero h1 h2)

/-- **M6 (flat form).** The multiset of charpoly-roots of the flat
connection Laplacian is the scalar Laplacian's roots, doubled. -/
theorem flat_charpoly_roots_eq_double :
    (G.laplacian false).charpoly.roots =
      G.scalarLaplacian.charpoly.roots +
        G.scalarLaplacian.charpoly.roots := by
  rw [G.flat_charpoly_eq_scalar_sq]
  exact Polynomial.roots_mul (by
    have h : G.scalarLaplacian.charpoly ≠ 0 :=
      Matrix.charpoly_monic _ |>.ne_zero
    exact mul_ne_zero h h)

end ConnGraph

end ConnectionLaplacian
