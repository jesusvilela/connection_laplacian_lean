# NEGATOR-B R6 Stage 5 — second-wave claim discovery

**Date:** 2026-04-22. **Seed:** 20260430. **Envelope:** n ≤ 4 exhaustive (760 configs) + n=5 exhaustive-iso × ≤ 12 wraps (11,337) + n=6 sample (350). **Wall:** 18.1 s. **Stack:** pure Python + networkx + numpy.

**Net:** 17 new top-level claims, 36 parametric sub-claims, **35 at τ=1.0** on original fuzz; **36 of 36 after C6 refinement** to C6-tight.

## Summary table

| id | dir | claim | τ | supp/total | verdict |
|----|---:|-------|---:|-----------:|---------|
| **C1_k1..k10** | 1 | `tr(L_möb^k) = tr(L_s^k) + tr(L_sig^k)` for k = 1..10 | **1.0** | 12447/12447 each | PROMOTE |
| C2_t{0.1, 0.5, 1, 2} | 1 | heat-trace additivity `tr e^{−t L_möb} = tr e^{−t L_s} + tr e^{−t L_sig}` | **1.0** | 12447/12447 each | PROMOTE |
| **C3_a{0.5, 1, 2}** | 1 | `det(L_möb + αI) = det(L_s + αI) · det(L_sig + αI)` | **1.0** | 12447/12447 each | PROMOTE |
| C4_a{0.5, 1, 2} | 1 | resolvent-trace additivity | **1.0** | 12447/12447 each | PROMOTE |
| **C18** | 1 | det identity stable over α ∈ {0.25, 0.5, 1, 2, 4} | **1.0** | 2000/2000 | PROMOTE |
| **C5** | 2 | `\|β(G) − β(G/e)\| ≤ 1` for non-bridge e (two-sided Lipschitz) | **1.0** | 2916/2916 | PROMOTE |
| C6 | 2 | `\|β(G) − β(G − v)\| ≤ deg(v)` | 0.8988 | 4494/5000 | **REFINE** |
| **C6-tight** | 2 | `\|β(G) − β(G − v)\| ≤ max(1, deg(v))` (post-hoc full + n=6 3k) | **1.0** | 301,249/301,249 | PROMOTE |
| C7 | 2 | `\|β(G) − β(G − v)\| ≤ 1 + deg(v)` (slack version) | **1.0** | 5000/5000 | PROMOTE |
| **C8** | 4 | `β(G₁ ⊔ G₂) = β(G₁) + β(G₂)` | **1.0** | 961/961 | PROMOTE |
| C9 | 4 | parity-matched 2-parallel-path preserves β | **1.0** | 3000/3000 | PROMOTE |
| **C10** | 3 | `tr(L_s · L_sig) = tr(L_s²) − 4\|W\|` — polynomial identity | **1.0** exact | 12447/12447 | PROMOTE |
| **C11** | 3 | `tr(L_möb²) = tr(L_s²) + tr(L_sig²)` (concrete k=2) | **1.0** exact | 12447/12447 | PROMOTE |
| **C12** | 3 | `‖L_möb‖_F² = ‖L_s‖_F² + ‖L_sig‖_F²` (concrete B17) | **1.0** exact | 12447/12447 | PROMOTE |
| C13 | 5 | bridge-wrap-flip preserves β | **1.0** | 2084/2084 | PROMOTE |
| C14 | 5 | non-bridge-wrap-flip `\|Δβ\| ≤ 1` | **1.0** | 2916/2916 | PROMOTE |
| C15_k{2, 3} | 5 | mismatched-parity k-subdivision `\|Δβ\| ≤ 1` | **1.0** | 3000/3000 each | PROMOTE |
| C16_w{0, 1} | 5 | triangle-closing `Δβ ∈ {−1, 0}` | **1.0** | 248/248 each | PROMOTE |
| C17 | 4 | line-graph sanity `β(L(G), W_xor) ≤ \|E(G)\|` | **1.0** | 972/972 | PROMOTE (low leverage) |

## Refinements / refutations

**C6 FAILS** on isolated-vertex deletion (deg(v) = 0): CE `n=2, E=∅, W=∅, v=0: β = 2 → 1`. Replacement **C6-tight** uses `max(1, deg(v))`, verified at 301,249 / 301,249 (full n ≤ 5 + n=6 3k sample). The `max(1, ·)` correction absorbs the isolated-vertex case.

## New master-lemma flags

1. **Shifted-determinant factorisation** (C3 / C18) is the analytic parent of the full trace-power / heat-trace / resolvent family. Single Lean theorem collapses 21 sub-claims. Follows directly from `mobius_charpoly_eq_scalar_times_signed` at `x := −α`.
2. **C5 ∪ L15 ∪ L15-rev = complete β-Lipschitz calculus** under edge operations: deletion, contraction, wrap-flip all move β by at most 1. Enables a 2-move walk lemma between arbitrary signings.
3. **A8 ∪ C15 = full subdivision calculus:** parity-matched subdivision preserves β (A8); mismatched parity perturbs β by at most 1 (C15). Together give a complete picture of k-subdivision effects on β.

## Prioritised PROVER-B queue (Stage 7)

### Tier 1 — single-theorem collapse of 21 sub-claims

**S1: Shifted-det factorisation** `∀ α, det(L_möb + α • 1) = det(L_s + α • 1) · det(L_sig + α • 1)`. Direct from M7 at `x := −α`. Collapses C1_k*, C2_t*, C3_a*, C4_a*, C18. **~15 LOC.**

### Tier 2 — clean `ring`-level identities (no spectrum)

- **S2: C10** `tr(L_s · L_sig) = tr(L_s²) − 4|W|` — purely combinatorial, ~5 LOC.
- **S3: C11** `tr(L_möb²) = tr(L_s²) + tr(L_sig²)` — 1-line from Tier 1 at k=2, or ~10 LOC direct.
- **S4: C12** `‖L_möb‖_F² = ‖L_s‖_F² + ‖L_sig‖_F²` — 1-line from C11 via `tr(Mᵀ · M) = tr(M²)` on symmetric.
- **S5: C1_k1** `tr(L_möb) = 4|E|` — direct 5-LOC extension of L9 bounds.

### Tier 3 — β-Lipschitz bundle

- **S6: C5** contraction-Lipschitz `|β(G) − β(G/e)| ≤ 1`.
- **S7: C6-tight** vertex-deletion with `max(1, deg(v))`.
- **S8: C13** bridge-wrap-flip preserves β (1-line via M2 switching-invariance).
- **S9: C14** non-bridge wrap-flip `|Δβ| ≤ 1`.

### Tier 4 — graph-operation identities

- **S10: C8** disjoint-union additivity.
- **S11: C9** parity-matched 2-parallel-path.
- **S12–13: C15_k{2,3}** mismatched-parity subdivision Lipschitz.
- **S14: C16** triangle-closing Δβ bound.

## Forbidden-zone grep (compliance)

Checked claim list against: M1–M7, A2/A3/A5'/A6'/A8/A12/A13, B1–B21, G1–G21, L13/L14/L15/L15-rev, the R6 L16 quartet, and G15/G16/B9/B21. **No overlap.**

Note: C1 covers k ∈ {1..10}; Stage-1 B1 listed only k ∈ {5..8}. The k ∈ {1, 2, 3, 4, 9, 10} entries plus concrete-polynomial C10/C11/C12 are **net-new ready-to-land lemmas** (where B17/B20 were only abstract via M6).

## Surprise discovery

`tr(L_s · L_sig)` admits a closed-form in combinatorial data `tr(L_s²) − 4|W|` that passes with **exactly zero** numerical error (polynomial identity in edge-incidence entries). Likewise C11 / C12. These are `ring`-provable in Lean **without invoking M6 at all** — they're cleaner and easier than the M6-derived path. Stage-1's B2 (`tr(L_s · L_sig) = Σ deg² + 2m − 4|W|`) is equivalent but less telescopic; C10's `tr(L_s²)` form is the Pythagorean-shaped cleaner statement.

## Artifacts

- `fuzz.py`, `run.log`, `results.json` in this directory.
- No Lean files touched. No paper edits.
