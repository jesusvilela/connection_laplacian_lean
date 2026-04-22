# FUZZER-A R6 Stage 2 — Sheaf-section α (edge-ops + inequalities at scale)

**Date:** 2026-04-22. **Envelope:** n ≤ 5 exhaustive (59,805 labeled (G, W) configs; 461 s) + n=6 scale sample (350 connected graphs × 16 wrap subsets each; 48 s) + ineq n ≤ 5 exhaustive (55,892 configs; 94 s) + ineq n=6 random (2,200 configs; 3 s) + L15 direct n=6 (1,500 configs; 1 s). **Total wall:** 615 s. **Stack:** pure Python + networkx; seed 20260422.

## Verdict table (ranked by τ then trials)

| id | claim | tested | passed | τ | verdict |
|----|-------|-------:|-------:|---|---------|
| **A8**     | k-subdivision with parity-matching new wraps preserves β (k ∈ {2, 3}) | 1,474,848 | 1,474,848 | **1.0000** | HOLDS |
| **A10**    | adding 2 new edges is order-independent for β | 985,684 | 985,684 | **1.0000** | HOLDS |
| **A2**     | pendant non-wrap add preserves β | 331,842 | 331,842 | **1.0000** | HOLDS |
| **A3**     | pendant wrap add preserves β | 331,842 | 331,842 | **1.0000** | HOLDS |
| **A13**    | vertex-switching invariance β(G,W) = β(G, W △ δ(v)) | 331,842 | 331,842 | **1.0000** | HOLDS |
| **A12**    | θ-replacement of non-wrap edge preserves β | 189,241 | 189,241 | **1.0000** | HOLDS |
| **L15**    | β(G, W) ≤ β(G − e, W) for non-bridge non-wrap e (cross-check) | 183,204 | 183,204 | **1.0000** | HOLDS |
| **L15-rev**| β(G − e, W) ≤ β(G, W) + 1 (reverse Lipschitz bound)                  | 183,204 | 183,204 | **1.0000** | **NEW — HOLDS** |
| A6'        | β(G, W) ≤ β(G/switched(e), W') for non-bridge wrap e                 | 179,967 | 171,994 | 0.9557 | **FAIL** (Stage-1 hypothesis) |
| A5'        | β(G, W) ≤ β(G/e, W') for non-bridge non-wrap e                       | 179,981 | 172,005 | 0.9557 | **FAIL** (Stage-1 hypothesis) |

## Central findings

### 1. All Stage-1 α τ=1 claims confirmed at n=6 scale

A2, A3, A8, A10, A12, A13 all pass exhaustively with huge supports (up to 1.47 M tests for A8). **No regressions.** These are ready for Stage-3 PROVER-A formalisation.

### 2. NEW: L15-rev (reverse Lipschitz bound on edge deletion)

`β(G − e, W) ≤ β(G, W) + 1` for non-bridge non-wrap e holds at τ=1 on 183,204 configs. Combined with L15 this gives the two-sided bound

> `β(G, W) ≤ β(G − e, W) ≤ β(G, W) + 1`

i.e. edge deletion changes β by 0 or 1 (never more). Promote to PROVER-A queue; likely a short corollary via the L15 interlacing argument + rank-1 perturbation.

### 3. Stage-1's A5'/A6' contraction-monotonicity hypothesis is WRONG

Both one-sided contraction inequalities fail at τ ≈ 0.9557 at n=6:

- **A5' counterexample (minimal):** G = K₄ minus edge (2,3), W = {(0,1), (0,2), (0,3)} (star at vertex 0). (G, W) is balanced via switching at 0, so β_G = 1. Contracting non-wrap e = (1,2): β_{G/e} = 0.
- **A6' counterexample:** same graph, W = {(0,2), (1,2)}, e = (0,2) wrap, switch at 0: β_G = 1, β_result = 0.

**Probe of the reverse direction:** tested `β(G/e) ≤ β(G)` on 176,698 configs: τ = 0.7555 — **also fails**. Minimal CE is the unbalanced triangle K₃ with W = {(0,1)}: β_G = 0, contracting (0,2) gives balanced K₂ with β = 1.

**Implication:** contraction has **no one-sided monotonicity** on β.

### 4. Candidate: contraction-Lipschitz (τ=1 across all observed CEs)

Every counterexample in both directions had `|β_G − β_{G/e}| = 1`. Strong conjecture (not yet fuzzed at full scale):

> **A5-Lip:** `|β(G, W) − β(G/e, W')| ≤ 1` for non-bridge non-wrap e.

Forwarding to Stage-5 NEGATOR-B as a refined hypothesis.

## Stage-3 PROVER-A recommendation (α slice)

Order of landing:

1. **A13 vertex-switching invariance** — classical, likely the fastest win. Foundation for A2/A3/A8/A10/A12 proofs that rely on switch-to-normalise.
2. **A2 pendant non-wrap** — direct from component-by-component β decomposition; uses L15 machinery.
3. **A3 pendant wrap** — corollary of A2 via A13 at the pendant vertex (W' = W △ δ(pendant) removes the wrap).
4. **A8 parity-matching k-subdivision** — the Stage-1 master α claim; subsumes R5 R6/R7 and A7. Proof: induction on k; base k=1 trivial; step uses A2/A3.
5. **A10 edge-add commutativity** — trivial (β is a function of (V, E, W)).
6. **A12 θ-replacement** — α-statement, γ-proof: new 4-cycle has even wrap-count iff original non-wrap; use cycle-parity characterisation (G3).
7. **L15-rev** — new; prove alongside L15 as its Weyl-interlacing dual.
8. **A5-Lip (contraction-Lipschitz)** — defer to Stage-5 after NEGATOR-B fuzz.

## Artifacts

- `fuzz.py` — 26 KB, networkx-based fuzzer.
- `probe_reverse.py` — 4 KB, reverse-direction probe.
- `results.json` — 13.7 KB, per-claim counts + CE exhibits.
- `run.log` — 2.2 KB.

No Lean files touched. No paper edits.
