# Negator Report: `scalarLap_cover_splits` (L5_Cover.lean:176)

## Verdict
**NO COUNTEREXAMPLE FOUND.** Across 12 small graphs the theorem holds. Stronger than charpoly agreement: the explicit Hadamard construction `P = I_V ⊗ R` with `R = [[1,1],[1,-1]]` makes the reindexed conjugation equal fromBlocks on the nose. P is invertible with det(P) = ±(2^|V|).

## Methodology

Two SymPy scripts at `findings/round2/neg_splits/check.py` and `check_sim.py`. For each ConnGraph G:
1. `scalarLap` (ordinary graph Laplacian)
2. `signedLap` (wrap edges contribute +1 off-diagonal, per `KernelDimension.lean:74`)
3. `Ltilde` (Laplacian of cover graph on V × Bool, vertices ordered 2v, 2v+1)

Then compared: (a) charpoly(Ltilde) vs charpoly(fromBlocks(L, 0, 0, S)); (b) explicit `P_kron * Ltilde * P_kron⁻¹` reindexed via the permutation matching `prodBoolEquivSum`.

## Examples tested (all match)

| # | G | wrap config | charpoly match | Hadamard-P match |
|---|---|---|---|---|
| 1 | K_2 | none | yes | yes |
| 2 | K_2 | {0-1} | yes | yes |
| 3 | C_3 | {0-1} | yes | yes |
| 4 | C_3 | all three | yes | yes |
| 5a | K_4 | none | yes | yes |
| 5b | K_4 | {0-1} | yes | yes |
| 5c | K_4 | triangle 0-1-2 | yes | yes |
| 5d | K_4 | all six | yes | yes |
| 6 | P_3 | middle edge | yes | yes |
| 7 | 2·K_2 disconnected | first only | yes | yes |
| 8 | C_4 | two opposite wrap | yes | yes |
| 9 | C_4 | 1 wrap (odd parity) | yes | yes |

## Why the Hadamard P works (mechanism)

The cover Laplacian Ltilde has 2×2 fiber structure indexed by Bool-sheets. Non-wrap edges give off-diagonal block `−I₂`; wrap edges give `−σ_x`. Conjugating by R simultaneously diagonalizes: `R·I₂·R⁻¹ = I₂` and `R·σ_x·R⁻¹ = diag(1,−1)`. Each fiber splits into symmetric (eigenvalue +1 → ordinary L) and antisymmetric (+1 interior, −1 wrap → signed S) copies.

## Important negative observation

Direct reindexing of Ltilde WITHOUT any P equals fromBlocks only when there are zero wrap edges. So a non-trivial P is strictly necessary when any wrap edge is present — a naive `P = id` proof attempt will fail.

## Recommendation for the prover

Use `P := (1 : Matrix V V ℝ) ⊗ᵏ !![1,1;1,-1]` with `P⁻¹ = (1/2) · P` (since R² = 2·I). det(P) = (det R)^|V| = (−2)^|V| ≠ 0. The `RhatMob` machinery around `KernelDimension.lean:93–111` is directly reusable.
