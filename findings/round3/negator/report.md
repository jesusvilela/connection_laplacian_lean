# NEGATOR report (round 3) — 10 naive claims about the connection Laplacian

**Artifacts:**
- `findings/round3/negator/negate.py`
- `findings/round3/negator/results.json`

**Scope.** All non-isomorphic simple graphs on `n ∈ {3,4,5,6}` vertices, every wrap subset `W ⊆ E(G)`. Verified numerically that `spectrum(L_möb) = spectrum(L_scalar) ∪ spectrum(L_signed)` as multisets.

## Summary table

| # | Claim | Verdict | Pass / tested |
|---|-------|---------|---------------|
| 1 | `dim ker L_möb = dim ker L_scalar iff G balanced` | **FALSE (as stated)** | 3 212 / 145 248 |
| 2 | `L_signed ⪰ 0` (PSD) | TRUE | 145 248 / 145 248 |
| 3 | `λ_min(L_möb) = min(λ_min(L_scalar), λ_min(L_signed))` | TRUE | 145 248 / 145 248 |
| 4 | `λ_max(L_signed) ≤ 2·max_deg` | TRUE | 145 248 / 145 248 |
| 5 | `tr(L_möb²) = tr(L_scalar²) + tr(L_signed²)` | TRUE | 145 248 / 145 248 |
| 6 | `dim ker L_signed ≥ dim ker L_scalar − |W|` | TRUE | 145 248 / 145 248 |
| 7 | `G connected, |W|=1 ⇒ G not balanced` | **FALSE** | 976 / 1 111 |
| 8 | `#fiber(C)+#fiber(C′) ≥ #fiber(C∪C′)` | **FALSE** | 8 004 / 8 936 |
| 9 | integrality of `dim ker L_möb − dim ker L_scalar` | TRUE (vacuous) | 145 248 / 145 248 |
| 10a | disjoint union: `ker L_signed` adds | TRUE | 225 / 225 |
| 10b | non-wrap edge contraction preserves `dim ker L_signed` | **FALSE** | 2 730 / 3 393 |

## Counterexamples and notes

**C1 — FALSE as stated.** `dim ker L_möb = dim ker L_scalar + dim ker L_signed`, so `km = ks` forces `ksig = 0` (no component balanced); but "G balanced" means every component balanced. Opposite conditions.
Min counterexample: `n=3, E=∅, W=∅` → `ks=3, ksig=3, km=6`; G trivially balanced but `km ≠ ks`.
**Corrected true form (3453/3453 on n≤5):** `dim ker L_möb = 2·dim ker L_scalar ⟺ every component of G is balanced`. This matches Thm 5.5.

**C2 — TRUE.** `L_signed` switching-equivalent to ordinary Laplacian of double cover, so PSD.

**C3 — TRUE.** Direct consequence of spectral partition.

**C4 — TRUE.** Anderson–Morley bound `L ⪯ 2Δ I` survives sign flips.

**C5 — TRUE.** Frobenius norms add because spectra partition exactly.

**C6 — TRUE.** Flipping one wrap edge breaks at most one balanced component; adding a wrap edge between two balanced components merges them into one.

**C7 — FALSE.** Min counterexample:
```
n=3, E={(0,1),(0,2)}, W={(0,1)} — wrap edge is a bridge
G is balanced (ε: 0→0, 1→1, 2→0).
```
Claim holds iff single wrap edge lies on a cycle. 135/1111 (≈12%) small instances balanced via bridge wrap.

**C8 — FALSE.** Fiber sizes **multiply** under disjoint union, so subadditivity fails.
Min counterexample: 3 isolated vertices, W=∅; A={0}, B={1,2}: `#fiber(A)=2, #fiber(B)=4, #fiber(A∪B)=8`; 2+4 < 8.
Correct statement: `#fiber(G₁ ⊔ G₂) = #fiber(G₁) · #fiber(G₂)` (multiplicative).

**C9 — TRUE (vacuous).** Difference = `dim ker L_signed`, always nonneg integer.

**C10a — TRUE.** `dim ker L_signed` adds on disjoint unions.

**C10b — FALSE.** Contracting a non-wrap edge changed `dim ker L_signed` in 663/3393 (≈20%) cases. Min: `K₃, W={(0,1)}` (unbalanced triangle); contracting `(0,2)` collapses to single wrap edge, balances. Subdivision likely similarly fragile.

## Take-aways for Lean formalization

**Safe targets (universally verified at n ≤ 6):** claims 2, 3, 4, 5, 6, 9, 10a.

**Do NOT formalize:** claims 1 (as stated), 7, 8, 10b — refuted at n = 3.

**Corrected statements:**
- Claim 1 should become `dim ker L_möb = 2 · dim ker L_scalar ⟺ every component is balanced`.
- Fiber-composition law is **multiplicative**, not subadditive.

No Lean files were edited; no builds attempted.
