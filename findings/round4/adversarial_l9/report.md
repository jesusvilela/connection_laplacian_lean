# ADVERSARIAL-L9 — Round 4 Audit of `L9_Bounds.lean`

**Overall verdict: NO BUGS FOUND.** All 5 theorems are mathematically correct and the proofs hold up to edge-case scrutiny. Two minor fragilities flagged.

## Hand verifications (all pass)

| Graph | V | E | Degrees | trace(L) | 2·E | C | B (no wrap) | drop |
|-------|---|---|---------|----------|-----|---|---|------|
| ∅ | 0 | 0 | — | 0 | 0 | 0 | 0 | 0 |
| K₁ | 1 | 0 | (0) | 0 | 0 | 1 | 1 | 0 |
| K₂ | 2 | 1 | (1,1) | 2 | 2 | 1 | 1 | 0 |
| P₃ | 3 | 2 | (1,2,1) | 4 | 4 | 1 | 1 | 0 |
| K₃ | 3 | 3 | (2,2,2) | 6 | 6 | 1 | 1 | 0 |
| K₄ | 4 | 6 | (3,3,3,3) | 12 | 12 | 1 | 1 | 0 |
| C₄ (0 wrap) | 4 | 4 | (2,2,2,2) | 8 | 8 | 1 | 1 | 0 |
| C₄ (1 wrap) | 4 | 4 | (2,2,2,2) | 8 | 8 | 1 | 0 | 1 |

## Per-theorem verdicts

1. **`trace_scalarLaplacian = 2·|E|` — ROBUST.** Uses `SimpleGraph.sum_degrees_eq_twice_card_edges`. The ℕ→ℝ bridge is discharged by `push_cast; rfl`. Empty V: both sides 0 by sum-over-empty. No off-by-one or overflow.

2. **`trace_signedLaplacianMobius = 2·|E|` — ROBUST (minor fragility).** Correct: diagonal ignores wrap signs. The `show (if v = v then …)` hack works because the def has that shape and `(neighborFinset v).card = SimpleGraph.degree v` by `rfl` in Mathlib. **Fragility:** if Mathlib ever refactors `SimpleGraph.degree` to not be definitionally `(neighborFinset v).card`, both the `show` match and the closing `rfl` break.

3. **`signed_kernel_le_scalar_kernel` — ROBUST, SHARP.** Reduces to `numBalancedComponents ≤ numComponents`. Tight: equality iff all components are balanced; strict on C₄ with one wrap edge.

4. **`kernel_drop_eq_unbalanced` — ROBUST.** `2·C − (C + B) = C − B` in ℕ. `hbal_le` guarantees ℕ-subtraction does not truncate. Empty-graph case: `0 − 0 = 0`.

5. **`kernel_drop_le_numComponents` — ROBUST.** Trivial after (4); `omega` discharges `C − B ≤ C`.

## Fragility inventory

- `SimpleGraph.degree` definitional equality with `(neighborFinset v).card` — load-bearing for `signedLaplacianMobius_diag`.
- `SimpleGraph.sum_degrees_eq_twice_card_edges` name/shape — used in traces (1) and (2).
- Simp normal form of `SimpleGraph.lapMatrix`, `SimpleGraph.degMatrix`, `Matrix.diagonal_apply_eq`, `SimpleGraph.adjMatrix_apply` — used in `scalarLaplacian_diag`.
- `push_cast; rfl` normal form for nat-coercion-of-sum.

## Accidental-proof check

- `trace_*`: canonical route; no shortcut of the form `simp` quietly picks a different lemma.
- `signed_kernel_le_scalar_kernel`: the only route through `signedLaplacian_kernel_dim_general` requires the correct RHS `numBalancedComponents`; the older buggy formula would not yield this inequality.
- `kernel_drop_*`: cross-checked against hand computation on C₄-with-one-wrap (drop = 1) which matches the `C − B = 1 − 0` prediction.

## Conclusion

No counterexample exists among tested graphs. No proof "accidentally works". File is clean to land.
