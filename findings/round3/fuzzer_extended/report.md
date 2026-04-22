# Round-3 Extended Fuzzer Report

*Date: 2026-04-21 - seed 20260421*

Total configs tested: **456,950** across **719** graph representatives (n = 2..7).

## Per-test fail counts (aggregate)

| Test | Description | Fails |
|---|---|---|
| `T1_spec` | spec(L_mob) = multiset union of spec(L_scalar) and spec(L_signed) | **0** |
| `T1_trace` | tr(L_mob) = tr(L_scalar)+tr(L_signed) = 2 tr L_scalar = 4|E| | **0** |
| `T1_det` | det(L_mob+aI) = det(L_scalar+aI) * det(L_signed+aI) for a in {0.5,1,2,3.7,10} | **0** |
| `T2_ker` | dim ker L_mob = dim ker L_scalar + dim ker L_signed | **0** |
| `T2_split` | ker L_mob = sym-lift(ker L_scalar) (+) antisym-lift(ker L_signed) | **0** |
| `T3_fiber` | #fiber(C) = 2 if C balanced else 1 | **0** |
| `T4_balance_cross` | walk-parity balance iff 2-coloring balance (redundancy check) | **0** |
| `T5_zero_mult` | dim ker L_mob = #pi_0(G) + #balanced components | **0** |
| `T6_mult_per_eig` | mult_mob(lambda) = mult_scalar(lambda) + mult_signed(lambda) per eigenvalue | **0** |
| `T7_signed_ker` | dim ker L_signed = #balanced components | **0** |

## Per-bucket breakdown

| Bucket | Mode | Graphs | Configs | Any fails? |
|---|---|---|---|---|
| n=2 | exhaustive | 2 | 3 | no |
| n=3 | exhaustive | 4 | 15 | no |
| n=4 | exhaustive | 11 | 163 | no |
| n=5 | exhaustive | 34 | 3,275 | no |
| n=6 | exhaustive_graphs_wrap_cap_4096 | 156 | 92,643 | no |
| n=7 | random_sample_512_wrap_cap_1024 | 512 | 360,851 | no |

## Cycle shift-by-half probe (C_n, single wrap edge)

Compare spec(L_mob) on orientation double cover of C_n with one wrap edge against {2 - 2 cos(pi*k/n) : k=0..2n-1}.

| n | match | max |diff| |
|---|---|---|
| 3 | yes | 8.88e-16 |
| 4 | yes | 1.33e-15 |
| 5 | yes | 2.66e-15 |
| 6 | yes | 1.33e-15 |
| 7 | yes | 2.00e-15 |
| 8 | yes | 1.33e-15 |
| 9 | yes | 1.33e-15 |
| 12 | yes | 2.66e-15 |
| 16 | yes | 1.78e-15 |

## Interpretation

- All ten identities hold across every tested (graph, wrap) config.
- In particular, beyond T1/T2/T3 (already confirmed in round 2):
  - **T2_split**: the kernel of `L_mob` really does split as the direct sum of symmetric-sheet lifts of ker(L_scalar) and anti-symmetric-sheet lifts of ker(L_signed). This is a concrete *basis*-level statement, candidate for the next Lean theorem.
  - **T5**: `dim ker L_mob = #pi_0(G) + #balanced(G)` - a single closed-form invariant combining the two decomposition halves.
  - **T6**: the spectral decomposition is pointwise (multiplicity-wise), not just set-wise.
  - **T7**: `dim ker L_signed = #balanced(G)`, the standard signed-Laplacian kernel formula; a clean Lean target.
  - **T4**: walk-parity agrees with 2-coloring brute-force balance - confirms the algorithmic balance predicate is sound.
  - **Cycle probe**: spec(L_mob) for C_n with one wrap edge matches the shift-by-half spectrum {2-2cos(pi*k/n) : k=0..2n-1} - to ~1e-15. This is a Mobius-band-like identity with a clean closed form.

## Files

- `fuzz_ext.py` - this script
- `fuzz_ext_results.json` - full results + up to 20 failing samples per test

## Notes on scope

- n = 2..5: fully exhaustive (all non-iso graphs, all 2^|E| wrap subsets) - reproduces round-2 coverage + new tests.
- n = 6: all 156 non-iso graphs; wrap subsets capped at 4,096 per graph (uniform sample when |E| > 12).
- n = 7: random sample of 512 non-iso graphs via gnp + WL/iso dedup; wrap cap 1,024 per graph.
- Cycles C_3..C_16 with single wrap edge compared against the predicted eigenvalue formula.