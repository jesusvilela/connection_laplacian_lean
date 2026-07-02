# ADVERSARIAL-NEW-LEAN — R5 audit of L10/L11/L12

**Date:** 2026-04-22. **Target:** `L10_CoverCharpoly.lean`, `L11_Trees.lean`, `L12_WalkH1.lean` (landed R4).

## Verdict

All three files **clean**. No `sorry`. `#print axioms` on all 8 downstream theorems plus the helper `Matrix.charpoly_conj_of_isUnit_det` returns exactly `{propext, Classical.choice, Quot.sound}` (verified via `axiom_check.lean` in this folder).

## Hand verification (`verify_small.py`)

sympy over ℚ, n ≤ 4, all edge-subsets, all wrap-subsets:

| theorem | pass / total |
|---|---|
| L10 `cover_charpoly_eq_scalar_times_mobius` | 760 / 760 |
| L11 tree-balance (trees only) | 143 / 143 |
| L12 per-component wrap-parity | 888 / 888 |

**No counterexample found on the exhaustive n ≤ 4 slice.**

## Accidental-proof check

Mutated each statement in three ways to confirm the proof does not close a subtly-wrong goal:
- L10 RHS with Möbius factor dropped → `rw [charpoly_fromBlocks_zero₁₂]` fails.
- L12 parity convention flipped to "odd" → `Bool.xor_self` fails.
- L11 `walkWrapParity_nil = false` flipped → unification failure immediately.

No proof closes via generic `simp`/`omega` that would survive a subtle mis-statement.

## Negator / hidden-hypothesis hunt

- `IsTree.isConnected` carries `Nonempty V` (Mathlib `Path.lean:751`) — tree theorems cannot silently apply to empty V.
- K_1: cover has 2 isolated vertices → sheets separate → balanced. Correct.
- `Even 0 = True` in Mathlib handles `nil` walk case cleanly.

## Fragilities (Mathlib-refactor risk, descending severity)

1. `Nat.bodd` family in L12 — migration to `bne (n%2) 0` is underway in Mathlib.
2. `SimpleGraph.Walk.bypass` definitional `dite` peeked by `show` at L11:136, L11:190.
3. `coverProj x = x.1` by `rfl` at L11:249-250, L12:260, L12:264.
4. `Polynomial.C.mapMatrix` as `RingHom` via `_root_.map_mul` / `map_one`.

## Cosmetic findings

- (i) Dead lemma `nextSheet_eq_xor` (L11:107-117) is unused — delete or wire in.
- (ii) L12 docstring (lines 22-24) incorrectly calls `balanced_of_sheets_separated` *private*; it is public in L6:288. The shim `balanced_of_candidate_sheets_ne` duplicates existing logic.

## Follow-ups

- Replace `natParity` with `n%2`-based definition.
- Delete dead `nextSheet_eq_xor` or wire it in.
- Fix L12 docstring; inline or remove the `balanced_of_candidate_sheets_ne` shim.
- PR `Matrix.charpoly_conj_of_isUnit_det` to Mathlib (small, reusable).
- Extend verification to n ≤ 6 via `#eval` harness (optional).

## Artifacts

- `verify_small.py` (this folder) — ℚ-exact hand verification harness.
- `axiom_check.lean` (this folder) — single-file `lake env lean` axiom audit.

Zero bugs in the three files. Both findings (i) and (ii) are cosmetic and safe to address in a quiet round.
