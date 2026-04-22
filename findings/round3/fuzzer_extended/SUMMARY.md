# Round-3 Extended Fuzzer — Summary

**Script**: `fuzz_ext.py`. **Results**: `fuzz_ext_results.json`. **Report**: `report.md`.

## Coverage

| n | Mode | Graphs | Configs |
|---|---|---|---|
| 2 | exhaustive | 2 | 3 |
| 3 | exhaustive | 4 | 15 |
| 4 | exhaustive | 11 | 163 |
| 5 | exhaustive | 34 | 3,275 |
| 6 | exhaustive graphs, wrap cap 4,096 | 156 | 92,643 |
| 7 | random sample, wrap cap 1,024 | 512 | 360,851 |
| **total** | | **719** | **456,950** |

Runtime ~5 min, single-threaded.

## Results — 0 failures across all 10 identities

- **T1_spec**: spec(L_möb) = multiset union of spec(L_scalar) and spec(L_signed).
- **T1_trace**: tr(L_möb) = tr(L_scalar) + tr(L_signed) = 2·tr(L_scalar) = 4|E|.
- **T1_det**: det(L_möb + αI) = det(L_scalar + αI)·det(L_signed + αI) for α ∈ {0.5, 1.0, 2.0, 3.7, 10.0}.
- **T2_ker**: dim ker L_möb = dim ker L_scalar + dim ker L_signed (re-confirmed).
- **T2_split**: ker L_möb = sym-sheet-lift(ker L_scalar) ⊕ antisym-sheet-lift(ker L_signed) (basis-level).
- **T3_fiber**: #cover-components above C = 2 iff C balanced (re-confirmed).
- **T4_balance_cross**: BFS walk-parity == brute-force 2-coloring (redundancy check).
- **T5_zero_mult**: `dim ker L_möb = #π₀(G) + #balanced(G)`.
- **T6_mult_per_eig**: pointwise multiplicities: `mult_möb(λ) = mult_scalar(λ) + mult_signed(λ)`.
- **T7_signed_ker**: `dim ker L_signed = #balanced(G)`.

## Cycle shift-by-half probe

For every C_n with a single wrap edge (n ∈ {3,4,5,6,7,8,9,12,16}), the orientation-double-cover scalar-Laplacian spectrum matches `{2 − 2 cos(π k / n) : k = 0,…,2n−1}` to numerical precision (max diff 2.7e-15). Attractive Lean target for the cycle special case.

## Candidates for next Lean theorems (fuzz-verified)

1. **T7** — `dim ker L_signed = #balanced(G)` (single-matrix formula).
2. **T5** — `dim ker L_möb = #π₀(G) + #balanced(G)` (combines T2 + T7).
3. **T6** — pointwise multiplicity decomposition (strengthens T1).
4. **T2_split** — explicit kernel basis as sym/antisym sheet lifts (constructive LinearEquiv).
5. **C_n shift-by-half** — closed-form spectrum of cycle cover with one wrap.

## Note

Initial run crashed at report-write due to Windows cp1252 not encoding `⊔`. JSON had already been written. Script fixed with `encoding="utf-8"`; report regenerated from saved JSON.
