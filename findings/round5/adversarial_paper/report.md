# ADVERSARIAL-PAPER-R5 — attack paper post-R4 fixes

**Date:** 2026-04-22. **Target:** `paper/paper.tex` after R4 landings.

## Top-line verdict

R4 mathematical fixes (Lemma 8.3 algebra, four §10 examples, Theorem 9.1 proof) are **all correct**. But R4 introduced / left **2 broken `\ref`s and 3 inaccurate rows in Appendix A** — a reproducibility landmine since the appendix invites `#print axioms` verification.

## Correctness verification (all pass)

- **Lem 8.3 (signed-PSD, lines 1000-1029).** Expansion `Σ deg·x² + 2Σ_W − 2Σ_{E\W}` → `Σ_{E\W}(x_u − x_v)² + Σ_W(x_u + x_v)²`. Signs match the matrix definition at paper.tex:250-254.
- **§10 examples.**
  - `ex:naive-eq`: empty G on n=3, dim Ker L_Mob = 6 vs dim Ker L_scalar = 3.
  - `ex:bridge-wrap`: ε = (⊤,⊥,⊥) does satisfy Def 4.1 on both edges.
  - `ex:cross-merge`: β drops 3 → 2 under non-wrap merge — correct.
  - `ex:contraction`: K_3 kernel 0 → 1 under non-wrap contraction — correct.
- **Thm 9.1 (tree balance, lines 1105-1131).** Closed-walk-even-traversal argument works: splitting into p_{r→u} · {u,v} · p_{v→r} gives ε(u) ⊕ 1_W ⊕ ε(v) ≡ 0, hence Def 4.1 balance.

## NEW BUGS (all fixed in this round)

1. **`\ref{prop:scalarLaplacian-kernel}` undefined** — used at paper.tex:1212 and paper.tex:1275. Target is `thm:scalar-ker` (line 697). Both rendered "??" in the PDF. **FIXED** in R5 paper edit.
2. **`\ref{sec:cycle}` typo** at paper.tex:269. Correct label is `sec:cycles` (line 784). **FIXED.**
3. **Appendix A row 1278**: Lean name `flatLaplacian_kernel_dim` does **not exist**. Correct: `laplacian_decomposes` in `KernelDimension.lean:345`. **FIXED.**
4. **Appendix A row 1280**: `laplacian_kernel_dim_decomposes` exists but in `L8_Recognition.lean:87`, not `KernelDim.lean`. **FIXED.**
5. **Appendix A row 1292**: `strict_inequality_when_unbalanced` does **not exist**. Correct: `mobius_kernel_strict_iff_general` in `L8_Recognition.lean:142`. **FIXED.**
6. **Row 1304 stale**: Lem 8.3 said "Lean port scheduled L13_PSD.lean", but `L13_PSD.lean:298` already contains fully-proved `signedLaplacianMobius_posSemidef`. **FIXED.**

## Survived-R4 cleanup items (tracked for later)

- Appendix A missing rows for `thm:cover-splits`, `thm:flat-cycle` / `thm:mobius-cycle`, `cor:cover-kernel`, `cor:components-cover`, `lem:fiber-subset`, `lem:sep-if-balanced`, `lem:merge-if-unbalanced`. (Appendix opener now admits this explicitly.)
- Orphan labels: `def:cover`, `lem:deck`, `eq:Pcov-identity`, `app:formal-index`, `sec:structure`.
- `L15_BridgeMonotone.lean` landing is unreferenced in the appendix.
- Lem 8.3 proof could cite matrix def explicitly; Thm 9.1 proof line 1117 deserves a Mathlib citation for "every edge traversed an even number of times".
- σ_W / 1_{e∈W} unification sentence still missing in §7/§8.
- Abstract (n ≤ 7 sweep) vs Appendix A (n ≤ 8 sweep) sweep numbers need disambiguation — addressed by the honesty rewrite of the Reproducibility paragraph in R5.

## Net

6 fixable bugs identified, all patched in R5.
