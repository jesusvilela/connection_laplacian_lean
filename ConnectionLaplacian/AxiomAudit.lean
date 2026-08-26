/-!
Trust-boundary audit for the public theorem spine.

This file is compiled separately in CI.  Its output is checked by
`scripts/audit_trust.py`; only Lean/Mathlib's standard logical axioms are
allowed.  A project-local axiom entering any representative end theorem makes
the workflow fail.
-/

import ConnectionLaplacian

#print axioms ConnectionLaplacian.ConnGraph.cover_charpoly_eq_scalar_times_mobius
#print axioms ConnectionLaplacian.ConnGraph.isBalanced_iff_closedWalk_wrap_even
#print axioms ConnectionLaplacian.ConnGraph.signedLaplacianMobius_posSemidef
#print axioms ConnectionLaplacian.ConnGraph.numBalancedComponents_monotone_remove_nonwrap_nonbridge
#print axioms ConnectionLaplacian.ConnGraph.mobius_charpoly_roots_eq_union
#print axioms ConnectionLaplacian.ConnGraph.frobenius_laplacian_decomposes
#print axioms ConnectionLaplacian.ConnGraph.trace_mul_scalar_signed_eq
