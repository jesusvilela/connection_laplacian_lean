# Formal cycle-spectrum multiset assembly — proof programme

**Status:** in progress; the cycle-specific characteristic-polynomial products
below are mathematical targets, **not yet Lean theorems**. The existing
`Cycle.scalarCycle_eigenvalue` and `Cycle.signedCycle_eigenvalue` establish
one nonzero eigenvector per frequency, but do not certify multiplicities or
completeness. Treating these as if they formed a basis without proof would
repeat the specification mistakes documented in `Hardening/`.

## Exact mathematical target

For each integer `n ≥ 3`, for the scalar cycle Laplacian `L_sc` and
one-wrap signed cycle Laplacian `L_sg` in `CycleSpectrum.lean`:

```text
charpoly(L_sc) = product_{k=0}^{n-1} (X - (2 - 2*cos(2*pi*k/n)))
charpoly(L_sg) = product_{k=0}^{n-1} (X - (2 - 2*cos((2*k+1)*pi/n)))
```

As a **multiset** (not a set), the eigenvalues, counted with algebraic
multiplicity, equal the listed values **with repeated frequencies retained**.
The theorem should live on the actual cycle matrices, not an unrelated
existential vector or abstract lists.

For the connection Laplacian itself, the existing
`ConnGraph.mobius_charpoly_roots_eq_union` then supplies the scalar/signed
branch union once the cycle matrices are identified with the graph instance.

## Why the existing cosine witnesses cannot close the gap

The vectors in `scalarCycle_eigenvalue` are cosines. Frequencies `k` and
`n-k` yield the **same cosine vector** and often the same eigenvalue,
so counting those declarations as independent eigenvectors is invalid.
The one-wrap signed cycle has analogous degeneracies
`k ↔ n-1-k`. A valid assembly must exhibit a *full rank basis* or
prove the characteristic polynomial directly. It may not replace
multiset equality with support-set equality.

## Recommended proof route: twisted discrete Fourier basis

Work over `Complex` first, with

```text
zeta  = exp(2*pi*i/n)
alpha = exp(pi*i/n)
F_sc[j,k] = zeta^(j*k)
F_sg[j,k] = alpha^j * zeta^(j*k)
```

The one-wrap signed basis is the ordinary Fourier basis with an
anti-periodic boundary twist: `alpha^n = -1` while `zeta^n = 1`.
For the explicit real matrices mapped to `Complex`, prove:

1. **Root identities:** `zeta` is primitive of order `n`,
   `alpha^n=-1`, and all powers used in the matrices are nonzero.
2. **Eigen-equations:** `L_sc * F_sc = F_sc * diag(lambda_sc)` and
   `L_sg * F_sg = F_sg * diag(lambda_sg)`. Check first/middle/last
   rows separately, especially the signed wrap edge.
3. **Basis invertibility:** `F_sc^* F_sc = n I` and
   `F_sg^* F_sg = n I` by a finite root-of-unity geometric sum,
   or use Vandermonde and the primitive-root distinctness lemma.
   Orthogonality of the *complex exponentials* is essential; cosine
   witnesses alone are not enough.
4. **Charpoly product:** combine similarity invariance
   (already available as `Matrix.charpoly_conj_of_isUnit_det`)
   with the characteristic polynomial of a diagonal matrix to obtain
   an `n`-factor product with all repeats.
5. **Real descent:** because the matrices and spectral values are real,
   descend the complex coefficient equality along the injective
   homomorphism `Real →+* Complex`, or prove the real polynomial
   equality after complexifying. Then use `Polynomial.roots` to
   retain algebraic multiplicities over `Real`.
6. **Cycle/graph identification:** if this is later lifted to an
   arbitrary `ConnGraph` instance, establish the actual permutation
   similarity or matrix equality; do not assume that the specialised
   `Cycle` definitions are definitionally equal to the general
   `ConnGraph` Laplacians.

An alternative, potentially shorter route is a cyclic tridiagonal
determinant/Chebyshev recurrence with anti-periodic boundary sign.
Choose only after comparing the Mathlib v4.11 available lemmas.

## Smaller checked consequence already proposed on this branch

Two direct consequences of the **existing proven** cover charpoly
factorisation have been added as Lean code to
`ConnectionLaplacian/L10_CoverCharpoly.lean`:

- `cover_charpoly_roots_eq_union`: multiset of real roots of the
  cover charpoly = scalar roots + signed roots.
- `cover_charpoly_root_count_eq_sum`: pointwise *algebraic*
  multiplicity of every real root is additive across those factors.

These are **not** the open cycle Fourier assembly. They require
`lake build` and the updated `AxiomAudit.lean` before merging.

## Negative controls and numerical triangulation

The independent, numerical
`findings/round10/test_cycle_fourier_multisets.py` verifies for
`3 ≤ n ≤ 64`:

- full matrix eigen-equation, not merely scalar cosine values;
- `F* F / n = I` (so the candidate eigenvectors form a basis);
- sorted eigenvalues **with multiplicity**, not set supports;
- a **negative control**: periodic Fourier vectors must not pass
  the one-wrap signed case.

This establishes no Lean theorem. The protocol deliberately checks the
boundary sign and repeated frequencies that a superficial check can miss.

## Other genuine pending tasks (ordered)

| Priority | Work | Acceptance criterion | State |
|---|---|---|---|
| P0 | Cover spectral roots and pointwise multiplicity | Lean build + three-axiom audit for both new theorems | Code proposed; **uncompiled** |
| P1 | Scalar cycle full multiset | Actual `L_sc` charpoly/root-multiset equality for every `n≥3` | OPEN |
| P2 | One-wrap signed cycle full multiset | Actual `L_sg` charpoly/root-multiset equality, including repeated roots | OPEN |
| P3 | Strong even-wrap cycle detection | In `L14_CycleEw`, explicit Eulerian fundamental walk and independent reverse direction; remove reliance on caller-supplied `hrev` | OPEN |
| P4 | Combinatorial mixed trace | Formalise `tr(L_sc*L_sg) = tr(L_sc²) - 4*|W|` with correct cast and hypotheses | OPEN |
| P5 | Spectrum conventions | State and prove real/complex spectral correspondence or consistently scope theorem statements to characteristic-polynomial roots | OPEN |
| P6 | Boundary cases and robustness | Explicit n=0/1 graph tests and negative controls for malformed cycle statements | OPEN |
| P7 | Publication and provenance | Rebuild PDF, check theorem names in manuscript index, correct chronology/release metadata, re-run full CI/comparator as needed | OPEN outside Lean proof |

## Merge gate

```sh
lake exe cache get
lake build
lake env lean ConnectionLaplacian/AxiomAudit.lean
python scripts/audit_trust.py
python findings/round10/test_cycle_fourier_multisets.py
```

A successful numerical test or an accepted instance of
`signedCycle_eigenvalue` does **not** close P1/P2.
The formal milestone is the actual characteristic-polynomial product
and/or multiset roots equality for all `n≥3`, with no `sorry`,
`admit`, `native_decide`, or new axioms.

PR #9 has been merged into `main` with its original commit ancestry;
a follow-up main-branch commit regenerated `paper.pdf`. GitHub's comparison
against `main` shows only this feature branch's new proof/code/test files,
so no ancestry rebase is required before review. The follow-up PDF is
already on `main` and should be retained when merging this work.
