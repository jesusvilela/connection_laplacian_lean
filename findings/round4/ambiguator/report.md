# AMBIGUATOR-R4 report

Scan of `paper/paper.tex` (1248 lines, post-R4). Audit only; no edits made.

## §A. New R4 ambiguities (highest priority)

**A1 [CRITICAL]. Sign-of-squares proof of Lemma 8.3 (`lem:signed-psd`) contradicts its own statement** (lines 989-1018). Statement: non-wrap → `(x_u − x_v)²`, wrap → `(x_u + x_v)²`. Proof expansion at lines 1001-1004 writes `<x, L^sg x> = ∑_u deg(u)x_u² − ∑_W 2 x_u x_v·(+1) − ∑_{E\W} 2 x_u x_v·(−1)` — the leading minuses are spurious, because the off-diagonal of `L^sg` is `+1` on wrap, so its contribution is `+∑_W 2 x_u x_v`. The expansion at line 1010 ends with `(x_u+x_v)²` for non-wrap and `(x_u−x_v)²` for wrap — the OPPOSITE pairing from the stated lemma. Either the statement or the expansion must be corrected.

**A2.** Thm 9.3 "closed walk" sum ambiguity wrt multiplicity (line 1116). `∑_{e ∈ w} 1_{e∈W}` — list multiplicity or edge-set? The telescoping needs multiplicity; the Lean proof will use `SimpleGraph.Walk.edges : List`. Should be stated.

**A3.** §9 Thm 9.1 tree-balance proof claims `p_{r→v}` is obtained from `p_{r→u}` "by pre- or post-composition with `{u,v}`", but the edge `{u,v}` need not be terminal. Correct: symmetric-difference + acyclicity.

**A4.** §8 Rem. 8.7 typo: `det L_Mob(G+λI) = det L_flat(G+λI)` — `G+λI` undefined; should be `det(λI − L_Mob(G)) = det(λI − L_flat(G))`.

**A5.** §9 Cor. 9.5 hand-waves "up to back-tracking". Requires `dim H¹(C_n; Z/2) = 1`; should be stated.

## §B. Status of R3 open items

1. Rhat factor-of-2 (lines 222-223): `R·R = 2·I_2` internally consistent. **Addressed.**
2. `[u]_{\comp}` leftover: no remaining uses. **Addressed.**
3. Hadamard Bool ↔ Fin2 convention: no false/true↔scalar/signed claim at paper level. **Non-issue.**
4. σ_W as "1-cocycle" vs "1-cochain": still inconsistent. Line 185 "Z/2-cocycle", 371 "1-cocycle", 518 "1-cochain", 523 "automatically a 1-cocycle". **NOT addressed.**
5. Fourier Re/Im at k=0 and k=n/2: Im=0 at k=0 and (for even n) at k=n/2, not noted. **NOT addressed.**

## §C. Round-4 cross-reference consistency

- Trace formula match: §8 Prop 8.1 `tr L^sc = 2#E` matches Lean `trace_scalarLaplacian` at `L9_Bounds.lean:57-63`. Exact.
- `\ref{lem:signed-psd}` at line 260 resolves to label at line 990. OK.
- PSD-proof double-sourcing: §2 (257-260) previews via cover similarity; Lem 8.3 proves via SOS directly. No logical contradiction; just preview misdescribes route.
- Kernel-drop statement: §8 Prop 8.2 matches Lean `kernel_drop_eq_unbalanced`. Match.
- Lean file naming: §8 (942) says `L9_Bounds.lean` "scheduled to land" — stale, file exists.

## §D. Priority fix list (top 5)

1. **A1** — Rewrite §8 Lemma 8.3 proof expansion: drop spurious leading minuses, swap the `(x_u±x_v)²` pairing.
2. **B4** — Unify σ_W terminology globally: "σ_W is a 1-cochain; since the 2-skeleton is empty it is automatically a 1-cocycle; its class `[σ_W] ∈ H¹(G; Z/2)` is the balance obstruction."
3. **A3** — Rewrite Thm 9.1 tree-balance proof using symmetric-difference + acyclicity.
4. **A4** — Fix Rem. 8.7 `det L(G+λI)` typo → `det(λI − L(G))`.
5. **B5** — Add one-line Remark after Thm 6.1 that real eigenbasis at `k=0` (and `k=n/2` if even) is `{Re(e_k)}` only.

Minor: line 942 "scheduled to land as `L9_Bounds.lean`" is stale.
