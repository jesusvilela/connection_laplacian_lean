# Round-4 FUZZER-N8 Report

*Date: 2026-04-22 — seed 20260422*

Wall time: **198.0 s**. Total configs tested: **176,169** over **527** graph reps (n=2..8).

Max cover-charpoly relative |LHS-RHS| observed: **7.29e-03**.

## Identities under test

| Test | Description | Total fails |
|---|---|---|
| `T1_spec` | spec(L̃) == spec(L_scalar) ⊔ spec(L_signed) | **0** |
| `T1_trace` | tr(L̃) = 2 tr(L_scalar) = 4|E| | **0** |
| `T1_det` | det(L̃+αI)=det(L_scalar+αI)·det(L_signed+αI), α∈{.5,1,2,3.7,10} | **0** |
| `T2_ker` | dim ker L̃ = dim ker L_scalar + dim ker L_signed | **0** |
| `T2_split` | ker L̃ = sym-lift ker L_scalar ⊕ antisym-lift ker L_signed | **0** |
| `T3_fiber` | #fiber(C) = 2 iff C balanced else 1 | **0** |
| `T4_balance_cross` | walk-parity balance iff 2-coloring balance | **0** |
| `T5_zero_mult` | dim ker L̃ = #π₀(G) + #balanced(G) | **0** |
| `T6_mult_per_eig` | per-eigenvalue mult (TOL_SPEC) aligns | **0** |
| `T7_signed_ker` | dim ker L_signed = #balanced(G) | **0** |
| `B_cover_charpoly` | det(λI-L̃) = det(λI-L_scalar)·det(λI-L_signed), ≥10 λ's | **20** |
| `C_mult_pointwise` | per-eigenvalue mult @ TOL_MULT=1e-10 | **0** |
| `D_tr_scalar_2e` | tr(L_scalar) = 2|E| | **0** |
| `D_tr_signed_2e` | tr(L_signed) = 2|E| | **0** |
| `D_ker_bound` | dim ker L_signed ≤ dim ker L_scalar | **0** |
| `D_ker_diff_pi0` | dim ker L̃ − dim ker L_signed = #π₀(G) | **0** |
| `D_scalar_eq_pi0` | dim ker L_scalar = #π₀(G) | **0** |
| `D_all` | all L9_Bounds hold simultaneously | **0** |

## Per-bucket breakdown

| Bucket | Mode | Graphs | Configs | Max rel charpoly | Any fail? |
|---|---|---|---|---|---|
| n=2 | exhaustive | 2 | 3 | 2.13e-16 | no |
| n=3 | exhaustive | 4 | 15 | 1.72e-15 | no |
| n=4 | exhaustive | 11 | 163 | 3.41e-13 | no |
| n=5 | exhaustive | 34 | 3,275 | 1.26e-10 | no |
| n=6 | exhaustive_graphs_wrap_cap_2048 | 156 | 74,211 | 2.52e-08 | no |
| n=7 | random_sample_200_wrap_cap_512 | 200 | 73,531 | 9.09e-06 | YES — see JSON |
| n=8 | random_sample_120_wrap_cap_256 | 120 | 24,971 | 7.29e-03 | YES — see JSON |

## Cycle single-wrap probe (C_n, 1 wrap edge)

Predicted: spec(L̃) = {2 − 2 cos(π k / n) : k=0,..,2n−1}.

| n | match | max |diff| |
|---|---|---|
| 3 | yes | 8.88e-16 |
| 4 | yes | 1.33e-15 |
| 5 | yes | 2.66e-15 |
| 6 | yes | 1.33e-15 |
| 7 | yes | 2.00e-15 |
| 8 | yes | 1.33e-15 |
| 9 | yes | 1.33e-15 |
| 10 | yes | 2.22e-15 |
| 11 | yes | 2.22e-15 |
| 12 | yes | 2.66e-15 |
| 13 | yes | 2.22e-15 |
| 14 | yes | 3.11e-15 |
| 15 | yes | 3.11e-15 |
| 16 | yes | 1.78e-15 |
| 17 | yes | 2.22e-15 |
| 18 | yes | 1.78e-15 |
| 19 | yes | 3.11e-15 |
| 20 | yes | 2.66e-15 |
| 21 | yes | 2.22e-15 |
| 22 | yes | 2.66e-15 |
| 23 | yes | 3.11e-15 |
| 24 | yes | 2.64e-15 |

## Cycle two-wrap probe (C_n, 2 wrap edges)

Two wraps make cycle balanced, so cover splits into 2 copies of C_n. Predicted: spec(L̃) = {2 − 2 cos(2π k/n) : k=0..n-1} ∪ (same multiset). Table reports, over all unordered wrap-pairs, the max |diff| from that two-copies prediction.

| n | pairs tested | pairs match | max |diff| |
|---|---|---|---|
| 3 | 3 | 3 | 1.33e-15 |
| 4 | 6 | 6 | 1.11e-15 |
| 5 | 10 | 10 | 3.11e-15 |
| 6 | 15 | 15 | 2.22e-15 |
| 7 | 21 | 21 | 3.55e-15 |
| 8 | 28 | 28 | 4.44e-15 |
| 9 | 36 | 36 | 4.44e-15 |
| 10 | 45 | 45 | 4.88e-15 |
| 11 | 55 | 55 | 5.33e-15 |
| 12 | 66 | 66 | 5.33e-15 |
| 13 | 78 | 78 | 5.33e-15 |
| 14 | 91 | 91 | 5.33e-15 |
| 15 | 105 | 105 | 8.44e-15 |
| 16 | 120 | 120 | 7.99e-15 |
| 17 | 136 | 136 | 7.55e-15 |
| 18 | 153 | 153 | 7.11e-15 |
| 19 | 171 | 171 | 6.66e-15 |
| 20 | 190 | 190 | 7.11e-15 |
| 21 | 210 | 210 | 5.33e-15 |
| 22 | 231 | 231 | 6.22e-15 |
| 23 | 253 | 253 | 9.77e-15 |
| 24 | 276 | 276 | 6.70e-15 |

## Interpretation

- **FAILURE DETECTED**: see JSON fail_samples for details.
  - `B_cover_charpoly`: 20 fails

## Files

- `fuzz_n8.py` — this script
- `results.json` — full per-bucket JSON with up to 10 fail samples per key