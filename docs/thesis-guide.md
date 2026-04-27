# Thesis guide

This guide expands the paper into a reader-oriented manual for the verified
Lean development. It does not introduce additional theorems; the authoritative
formal statements are the declarations imported by
`/home/runner/work/connection_laplacian_lean/connection_laplacian_lean/ConnectionLaplacian.lean`.

## Central question

For a finite simple graph `G` with a distinguished set of wrap edges `W`, the
formalization studies the kernel of the `ℤ/2` connection Laplacian. The main
mathematical question is:

> How many global zero modes does the connection Laplacian have, and how does
> that number depend on the wrap data?

The answer is expressed in terms of connected components and balanced
components:

- the flat branch has two zero modes per connected component;
- the Möbius branch has one scalar zero mode per component plus one signed zero
  mode for each balanced component;
- strict loss of kernel dimension occurs precisely on components whose wrap
  holonomy is non-trivial.

## Reading order

1. `ConnectionLaplacian/Basic.lean` introduces the finite graph and matrix
   infrastructure.
2. `ConnectionLaplacian/KernelDimension.lean` records the scalar Laplacian
   kernel-dimension input from Mathlib.
3. `ConnectionLaplacian/L5_Cover.lean` and
   `ConnectionLaplacian/L6_Cohomology.lean` build the orientation double cover
   and the balance/cohomology language.
4. `ConnectionLaplacian/L8_Recognition.lean` assembles the recognition
   theorems for balanced components and kernel dimension.
5. `ConnectionLaplacian/L10_CoverCharpoly.lean` through
   `ConnectionLaplacian/L17_TracesAndLipschitz.lean` add spectral, tree,
   monotonicity, trace, and Lipschitz-style companion results.

## Theorem map

| Theme | Representative declaration | Role |
| --- | --- | --- |
| Cover and decomposition | `cover_charpoly_eq_scalar_times_mobius` | Relates the double-cover characteristic polynomial to scalar and Möbius factors. |
| Balance recognition | `isBalanced_iff_closedWalk_wrap_even` | Converts balance into an even-wrap closed-walk condition. |
| Positive semidefinite signed branch | `signedLaplacianMobius_posSemidef` | Supplies the signed Laplacian PSD statement. |
| Bridge monotonicity | `numBalancedComponents_monotone_remove_nonwrap_nonbridge` | Tracks balanced components under a non-wrap non-bridge removal. |
| Spectrum union | `mobius_charpoly_roots_eq_union` | Packages the Möbius spectrum as scalar plus signed branches. |
| Frobenius decomposition | `frobenius_laplacian_decomposes` | Gives the block decomposition behind the main matrix identities. |
| Trace identity | `trace_mul_scalar_signed_eq` | Connects scalar/signed trace expressions. |

## Manual checklist for extending the thesis

- State a mathematical claim in graph language before adding Lean code.
- Identify whether the claim belongs to the scalar, signed, cover, or Möbius
  block branch.
- Prefer proving component-wise statements before global counting statements.
- Keep empirical findings under `findings/` clearly separated from imported
  Lean theorems.
- After formalization, add the imported theorem name to the README or paper only
  when it is part of the `ConnectionLaplacian.lean` import spine.
