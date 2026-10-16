# Full cycle-spectrum multisets — Lean proof and verification ledger

**Status: PROVED** for the *specialised* real scalar cycle Laplacian and
one-wrap signed cycle Laplacian defined in
[`ConnectionLaplacian/CycleSpectrum.lean`](../ConnectionLaplacian/CycleSpectrum.lean),
for **every `n ≥ 3`**, including **all algebraic multiplicities**.
The complete proof is in
[`ConnectionLaplacian/CycleMultiset.lean`](../ConnectionLaplacian/CycleMultiset.lean),
imported by `ConnectionLaplacian.lean`. The full proof was merged in
[PR #11](https://github.com/jesusvilela/connection_laplacian_lean/pull/11)
(merge commit `5bd01eb664a832cca6cc75f40d1664a8c8e5179b`).
Its final PR-head [GitHub Actions run 38811118539](https://github.com/jesusvilela/connection_laplacian_lean/actions/runs/38811118539)
passed `lake build`, the source trust audit, and the then-current
`AxiomAudit.lean`. A subsequent hardening pass explicitly includes the new
spectrum theorems in the axiom audit.

## Exact proved results

For each `n ≥ 3`, write `L_sc` for the scalar cycle matrix and
`L_sg` for the one-wrap signed cycle matrix, both over `ℝ`.

```text
charpoly(L_sc) = product_{k=0}^{n-1} (X - (2 - 2*cos(2*pi*k/n)))
charpoly(L_sg) = product_{k=0}^{n-1} (X - (2 - 2*cos((2*k+1)*pi/n)))
```

The **multisets** of characteristic-polynomial roots are respectively

```text
roots(charpoly(L_sc)) = { 2 - 2*cos(2*pi*k/n)     | k = 0,...,n-1 }
roots(charpoly(L_sg)) = { 2 - 2*cos((2*k+1)*pi/n) | k = 0,...,n-1 }
```

These are multiset equalities, **not** just set equality and not the
existence of one eigenpair per index. In particular, frequencies giving the
same cosine appear with their proper algebraic multiplicities.

### Named machine-checked statements

| Lean theorem in `ConnectionLaplacian.Cycle` | What it certifies |
|---|---|
| `charpoly_of_vandermonde_eigenbasis` | Injective spectral parameters and eigen-equations give the complete characteristic polynomial |
| `scalarCycle_eigenvector_complex` | Every periodic Fourier vector satisfies the equation for the actual complexified scalar cycle matrix |
| `signedCycle_eigenvector_complex` | Every anti-periodic Fourier vector satisfies the equation for the actual complexified signed cycle matrix |
| `scalarCycle_charpoly_complex` | All scalar cycle factors, with multiplicities, over `ℂ` |
| `signedCycle_charpoly_complex` | All signed cycle factors, with multiplicities, over `ℂ` |
| `scalarCycle_charpoly_real` | Scalar characteristic-polynomial product in the paper's real-cosine form |
| `signedCycle_charpoly_real` | Signed characteristic-polynomial product in the paper's real-cosine form |
| `scalarCycle_roots_real` | Exact real-root multiset for the scalar cycle |
| `signedCycle_roots_real` | Exact real-root multiset for the signed cycle |

## Proof architecture

The older `Cycle.scalarCycle_eigenvalue` and
`Cycle.signedCycle_eigenvalue` construct *individual* real cosine
eigenvectors. Those statements alone **cannot establish completeness**:
frequencies `k` and `n-k` can yield the same real cosine vector.
The new development does not infer linear independence from those witnesses.

Instead it works with complex Fourier parameters

```text
ζ = exp(2*pi*i/n)             α = exp(pi*i/n)
z_sc(k) = ζ^k                z_sg(k) = α*ζ^k
v_k(j) = z(k)^j              λ_k = 2 - z(k) - z(k)^(-1)
```

1. **Root orders and distinctness.** `ζ` is a primitive `n`-th root;
   `α^n = -1`. The scalar roots `ζ^k` and signed roots `α ζ^k`
   are each pairwise distinct for `k : Fin n`.
2. **Exact eigen-equations.** Existing real row identities for the
   specialised cycle matrices are transported to `ℂ`; the periodic
   and anti-periodic Fourier vectors satisfy them, including the
   different sign at the signed closing edge. The proof explicitly
   handles the zero row, interior rows, and final row.
3. **Completeness and multiplicity.** Form the matrix whose columns
   are `v_k`. It is a **Vandermonde matrix** with pairwise distinct
   roots, so its determinant is nonzero. Thus the eigenvectors form
   a basis, allowing a similarity to `diag(λ_k)`. Taking the
   characteristic polynomial gives the *entire* `n`-factor product,
   with repeated eigenvalues preserved.
4. **Real-cosine descent.** Euler's identity converts
   `z+z⁻¹` to `2*cos(θ)`. Injectivity of the coefficient map
   `ℝ → ℂ` descends both polynomial equalities to `ℝ`.
   `Polynomial.roots_prod` then proves the two stated root multisets.

All four stages are in Lean 4.11 with Mathlib v4.11.0.

## Independent falsification and what it establishes

The numerical cross-check
[`findings/round10/test_cycle_fourier_multisets.py`](../findings/round10/test_cycle_fourier_multisets.py)
tests `n=3,...,64`: the complete scalar and signed eigen-equations,
full Fourier basis rank, and both sorted spectra **with multiplicities**.
It also tests a negative control: an ordinary periodic basis must
**fail** the signed one-wrap case. The reported round-10 run found
124 positive cases passing and 62 negative controls rejected.

These computational checks are secondary evidence; the Lean proofs
above, not the numerical tests, establish the universal statements.

### Formal verification

```sh
lake exe cache get
lake build
lake env lean ConnectionLaplacian/AxiomAudit.lean 2>&1 | tee axiom-audit.log
python3 scripts/audit_trust.py --axiom-output axiom-audit.log
python3 findings/round10/test_cycle_fourier_multisets.py
```

The comment-aware audit forbids `sorry`, `admit`,
`native_decide`, and locally declared axioms in the theorem spine.
The dedicated `#print axioms` checks require each selected end theorem
to depend only on Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.
The post-merge audit adds all nine spectrum-related statements to that
check (including the abstract completeness lemma and concrete
eigen-equations). The follow-on scope-hardening also audits the five
conditional graph-transfer claims from `CycleGraphTransfer.lean`.
The trust-audit script now fails if an expected `#print axioms`
declaration is silently absent from the resulting log.

## Formal transfer into the general connection-graph theory

`ConnectionLaplacian/CycleGraphTransfer.lean` establishes **five further
Lean theorems**, including `mobius_connection_roots_of_cycle_reindex`.
Given a `ConnGraph G`, a vertex bijection `e : G.V ≃ Fin n` and proofs

```text
reindex e e G.scalarLaplacian = scalarCycleLaplacian n
reindex e e G.signedLaplacianMobius = signedCycleLaplacian n
```

it transports *both* real cycle charpolys and exact root multisets
to `G`, and combines them into the complete Möbius connection
root multiset using the separately formalised general
`G.mobius_charpoly_roots_eq_union`.

The hypotheses are **not** tautological or automatically discharged:
they encode exactly the graph-to-matrix identification obligation.
Their presence prevents an unsupported inference from
"this graph is called a cycle" to "these matrices coincide".
A further theorem deriving both identities from an explicit
`SimpleGraph.cycleGraph` is still **not proved**.

## Comparator extension and trust distinctions

`Hardening/CycleChallenge.lean` and `CycleSolution.lean` now state five
claims (both real charpolys, both root multisets, and one conditional
full connection multiset) for comparator checking. The challenge
imports `CycleSpectrum` but not the completed `CycleMultiset` proof.
`config-cycle-nanoda.json` requests built-in and external-kernel replay;
two negative controls tamper with the signed phase and inject an axiom.

**Three different verification stages must not be conflated:**

- Lean CI and the strengthened axiom audit prove and check the
  original theorems in the standard three-axiom footprint.
- CI compiles the comparator challenge and solution and audits the
  *configuration integrity*. This is a useful preflight, **not**
  comparator or dual-kernel execution.
- The actual pinned comparator with landlock/nanoda and negative
  controls requires an observed successful run; record its status,
  SHAs, evidence logs, and OS enforcement separately.

See [the dedicated comparator ledger](../Hardening/CYCLE-COMPARATOR.md)
for the precise commands and acceptance criteria.

## Scope boundary and remaining work

This closes the **cycle-specific Fourier-spectrum assembly**, not the
whole research programme. In particular:

| Work | Status |
|---|---|
| Cover factorisation, root union, and pointwise multiplicity corollaries | **PROVED** in `L10_CoverCharpoly.lean` |
| Scalar cycle full real charpoly and root multiset, `n≥3` | **PROVED** in `CycleMultiset.lean` |
| One-wrap signed cycle full real charpoly and root multiset, `n≥3` | **PROVED** in `CycleMultiset.lean` |
| Transfer of full cycle spectra under proven `ConnGraph` matrix reindexing | **PROVED, conditional** in `CycleGraphTransfer.lean` (5 named statements); concrete cycle-instance equivalence still **OPEN** |
| Strengthening `L14_CycleEw` without caller-supplied reverse hypothesis | **OPEN** |
| General combinatorial mixed-trace identity `tr(L_sc * L_sg) = tr(L_sc²) - 4|W|` | **OPEN** |
| Out-of-scope graph sizes / malformed-cycle boundary cases `n=0,1` | **OPEN**; cycle theorems explicitly assume `n≥3` |
| Manuscript LaTeX and tracked PDF | **UPDATED** in [PR #12](https://github.com/jesusvilela/connection_laplacian_lean/pull/12); GitHub Actions rebuilt `paper/paper.pdf` after synchronizing `paper/paper.tex` |
| Archived DOI release metadata, chronology, and external comparator replay of the new declarations | **OPEN**; comparator challenge/solution and an attempted dual-kernel runner are prepared, but the original seven-theorem run did not include these claims |

**Important convention:** The signed specialised matrix places its
anti-periodic sign on the closing edge of the cyclic indexing. An arbitrary
single-wrap edge can be rotated to that position, but a Lean theorem
identifying that graph-level `ConnGraph` model with this specialised
matrix is **not yet claimed**. Likewise, a Lean-checked characteristic-
polynomial root multiset should not be mistaken for a proof of unrelated
claims about arbitrary-graph spectral operators.

The original PR #10 supplied cover-factorisation corollaries and the
proof plan, while PR #11 carried out the two full cycle-specific proofs.
