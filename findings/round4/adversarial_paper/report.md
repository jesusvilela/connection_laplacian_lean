# ADVERSARIAL-PAPER-R4 Audit Report

Target: `paper/paper.tex` (1248 lines). New content: §8 (930–1069), §9 (1072–1156), §10 (1159–1211), tightened Lemma signed-psd.

## §8 Further Identities

- **Prop. Trace formulas** — ROBUST. Diagonals match; sum via `sum_degrees_eq_twice_card_edges`.

- **Prop. Kernel inequalities** — ROBUST. β ≤ #comp by subset; `2#comp − (#comp + β) = #comp − β` ✓.

- **Lemma signed-psd (CRITICAL BUG IN PROOF)** — STATEMENT ROBUST, PROOF CONTAINS SIGN ERROR. Correct expansion:
  `<x, L^sg x> = Σ_u deg(u)x_u² + 2Σ_{wrap} x_u x_v − 2Σ_{non-wrap} x_u x_v`
  `= Σ_{non-wrap}(x_u−x_v)² + Σ_{wrap}(x_u+x_v)²`.
  But proof lines 1002–1004 open with spurious leading minuses; lines 1009–1011 arrive at `Σ_{E\W}(x_u+x_v)² + Σ_W(x_u−x_v)²` — the OPPOSITE pairing. Same SOS (correct form) already appears in §2 lines 263–266. Only the proof is wrong.

- **Thm cover-charpoly, Cor mult-pointwise** — ROBUST. P invertible over ℝ (P⁻¹ = P/2); real symmetric → real spectra.

## §9 Structure Theorems

- **Thm tree-balanced** — ROBUST. For edge {u,v} where u is parent, `p_{r→v} = p_{r→u} ++ {u,v}`, so `ε(u)⊕ε(v) = 1_{{u,v}∈W}`. Works for any wrap set.
- **Cor forest-star-path** — ROBUST.
- **Thm walk-sum** — ROBUST. Telescoping, no hidden lemmas.
- **Cor cycle-ew (presentation gap)** — "up to backtracking" glosses formal closed-walk reduction on C_n. Needs explicit backtrack reduction or cite `H¹(C_n;Z/2) = Z/2`.

## §10 Counter-claims

- **Ex naive-eq** — CONFIRMED ERROR. Text: "dim Ker L_Mob = 6 ≠ 3 = dim Ker L_scalar". On empty n=3 W=∅: L_Mob and L_flat are both zero 6×6, so both kernels 6-dim; G vacuously balanced; the naive claim `dim Ker L_Mob = dim Ker L_flat iff balanced` is VERIFIED not refuted. The example compares L_Mob to L_scalar instead of L_flat. Either the example fails to refute, or the claim should read differently.

- **Ex bridge-wrap** — CONFIRMED ERROR (invalid witness). P_3 with W={{v_0,v_1}} is balanced, but witness `ε(v_0)=⊤, ε(v_1)=⊥, ε(v_2)=⊤` violates Def 4.1 on edge {v_1,v_2}: ε differs but edge not in W. Correct witness: `ε(v_0)=⊤, ε(v_1)=⊥, ε(v_2)=⊥`.

- **Ex fiber-mult** — CONFIRMED ERROR (double). For 3 isolated vertices: `#π⁻¹({v_0,v_1,v_2}) = 6`, not 8. Moreover the stated "correct multiplicative law" is wrong: fiber cardinality under `comp(G̃) → comp(G)` is ADDITIVE across disjoint components. Both the numbers and the replacement "correct law" are mistakes.

- **Ex contraction** — ROBUST.

## Overall

- Lemma signed-psd: statement correct, proof has arithmetic sign bug.
- §10 is weakest: 3 of 4 examples have confirmed errors; only `contraction` is solid.
- §8 (aside from signed-psd proof), §9 trees/walks, cover-charpoly are robust. Cor cycle-ew is hand-wave-adjacent on backtracking.
