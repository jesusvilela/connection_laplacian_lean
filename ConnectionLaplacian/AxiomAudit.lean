import ConnectionLaplacian

/-!
Trust-boundary audit for the public theorem spine.

This file is compiled separately in CI.  Its output is checked by
`scripts/audit_trust.py`; only Lean/Mathlib's standard logical axioms are
allowed.  A project-local axiom entering any representative end theorem makes
the workflow fail.
-/

#print axioms ConnectionLaplacian.ConnGraph.cover_charpoly_eq_scalar_times_mobius
#print axioms ConnectionLaplacian.ConnGraph.cover_charpoly_roots_eq_union
#print axioms ConnectionLaplacian.ConnGraph.cover_charpoly_root_count_eq_sum
#print axioms ConnectionLaplacian.ConnGraph.isBalanced_iff_closedWalk_wrap_even
#print axioms ConnectionLaplacian.ConnGraph.signedLaplacianMobius_posSemidef
#print axioms ConnectionLaplacian.ConnGraph.numBalancedComponents_monotone_remove_nonwrap_nonbridge
#print axioms ConnectionLaplacian.ConnGraph.mobius_charpoly_roots_eq_union
#print axioms ConnectionLaplacian.ConnGraph.frobenius_laplacian_decomposes
#print axioms ConnectionLaplacian.ConnGraph.trace_mul_scalar_signed_eq

/-! Full n-cycle characteristic polynomials and spectral multisets (n ≥ 3).
     Includes the independently checked Fourier eigen-equations, invertible
     Vandermonde assembly, complex formulas, and real cosine descent. -/
#print axioms ConnectionLaplacian.Cycle.charpoly_of_vandermonde_eigenbasis
#print axioms ConnectionLaplacian.Cycle.scalarCycle_eigenvector_complex
#print axioms ConnectionLaplacian.Cycle.signedCycle_eigenvector_complex
#print axioms ConnectionLaplacian.Cycle.scalarCycle_charpoly_complex
#print axioms ConnectionLaplacian.Cycle.signedCycle_charpoly_complex
#print axioms ConnectionLaplacian.Cycle.scalarCycle_charpoly_real
#print axioms ConnectionLaplacian.Cycle.signedCycle_charpoly_real
#print axioms ConnectionLaplacian.Cycle.scalarCycle_roots_real
#print axioms ConnectionLaplacian.Cycle.signedCycle_roots_real
