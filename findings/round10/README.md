# Round 10 — Fourier-basis completeness and multiplicity probes

**Scope:** scalar cycle and one-wrap signed cycle, `n=3..64`.
This is a *numerical validation protocol* for the future full
Lean multiset assembly, **not** the mathematical proof.

Run from repo root:

```sh
python findings/round10/test_cycle_fourier_multisets.py
```

The script reconstructs both explicit cycle Laplacians without reading
the existing numerical implementation. It builds the ordinary Fourier
matrix `F_sc[j,k]=exp(2*pi*i*j*k/n)` and the one-wrap twisted basis
`F_sg[j,k]=exp(pi*i*j*(2*k+1)/n)`.

For each matrix the test checks:
1. The **entire** eigen-equation `L F = F D`.
2. The unitarity/scaled-basis identity `F* F = n I`.
3. Equality of **sorted eigenvalue arrays with multiplicities**.
4. A negative control: the *periodic* Fourier basis falsely applied to
   the signed one-wrap matrix must **fail** the eigen-equation.

Observed local run (Python/NumPy), 2026-10-15:

```json
{
  "n": "3..64",
  "cases": 124,
  "max_eigen_equation_residual": 1.3441293712077815e-14,
  "max_unitarity_residual": 1.441283908783747e-15,
  "max_sorted_multiset_discrepancy": 5.329070518200751e-15,
  "negative_controls_rejected": 62,
  "status": "PASS (numerical, not a Lean theorem)"
}
```

These results depend on floating-point arithmetic and NumPy and should
not be mistaken for kernel verification. **Subsequent formal closure
(2026-10-16):** `ConnectionLaplacian/CycleMultiset.lean` now proves the
complex Fourier eigen-equations, Vandermonde invertibility, both real
cosine characteristic-polynomial products, and both exact eigenvalue
multisets for every `n >= 3`. This round-10 test remains independent
empirical corroboration of that later proof, not its justification.

See [the completed proof ledger](../../docs/cycle-spectrum-multiset-assembly.md).
