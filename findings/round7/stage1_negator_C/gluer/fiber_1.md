# R7 Stage 1 Gluer — NEGATOR-C Fibre-1 Manifest

**Date:** 2026-04-22
**Scope:** Consolidate three NEGATOR-C sub-sheaves (α:Z/3, β:Z/k, γ:U(1)) into a single falsifiable-hypothesis manifest and rank for Stage 2 FUZZER-C.

## 1. Sub-sheaf summary

| Sheaf | Fibre | Hypotheses | File |
|-------|-------|-----------|------|
| α | Z/3 pilot (concrete) | 18 | `sheaf_alpha_Z3/report.md` |
| β | Z/k general (structural) | 20 | `sheaf_beta_Zk/report.md` |
| γ | U(1) continuous | 20 | `sheaf_gamma_U1/report.md` |
| **Total** | | **58** | |

The three sub-sheaves project down to one coherent picture:

```
                    Z/2 (R6)
                       |
            embedding  |  embedding                  limit
   Z/3 (α) ---------- Z/k (β) ------------ U(1) (γ)
                  divisor lattice         real-analytic
```

Claim categories:
- **Shared skeleton** (DFT, Fourier character-fibres, PSD, kernel-=-comp criterion on flat classes, trace formulas). Present in α, β, γ with minor modifications.
- **Z/k-specific** (divisor-indexed β^(d), Euler-φ multiplicities, CRT tensor, prime-k Galois-orbit equality, Gauss-sum trace, anti-balance).
- **Continuous-only γ** (Rellich analytic flow, Jacobian torus, IDS, Bloch-Floquet, Harper-Hofstadter, Cheeger-magnetic, Hellmann-Feynman derivative, Kronecker-Hadamard non-result).

## 2. Compatibility audit across sub-sheaves

Cross-sheaf consistency checks (all pass):

| Check | α (Z/3) | β (Z/k) | γ (U(1)) | Status |
|-------|---------|---------|----------|--------|
| Kernel formula | `#comp + 2 β^(3)` | `Σ_{d \| k} φ(d) β^(d)` | `#{flat comp}` over `C` | ✓ coherent: at `k=3`, `Σ_{d \| 3} φ(d) β^(d) = β^(1) + 2 β^(3) = #comp + 2 β^(3)` since `β^(1) = #comp`. |
| `tr(L)` | `6\|E\|` | `2k\|E\|` | `2\|E\|` | ✓ at `k=3`: `2·3·\|E\| = 6\|E\|`; at `k=1`: `2\|E\|`. |
| Forests flat | `dim ker = 3#comp` | `dim ker = k·#comp` | `dim_C ker = #comp` | ✓ all classes trivial; Z/k over R has dimension k on each component kernel; U(1) over C has dimension 1. |
| Charpoly factors | 3 factors, two conjugate | `k` factors, grouped by Galois orbit size | N/A (continuous) | ✓ α is k=3 special case of β. |
| Cycle `C_n` kernel | `3` if `3 \| n`, `1` else | gcd-controlled | `[θ ∈ Z]` | ✓ γ specialises correctly. |
| Bridge insensitivity | yes (Z/3) | yes (Z/k) | yes (U(1)) | ✓ universal. |

No contradictions found.

## 3. Genuinely-new claims beyond R6 (Z/2)

For the FUZZER-C queue, we isolate claims that are *not* trivial specialisations of R6 material:

**From β (Z/k):**
1. **Zk-M1 divisor-indexed formula** `Σ_{d|k} φ(d) β^(d)` — genuinely new.
2. **Zk-CRT** `L_{Mob, k1 k2} ≅ L_{Mob, k1} ⊗ L_{Mob, k2}` for coprime `k_i`.
3. **Zk-primes (Galois)** — all non-trivial characters form one orbit of size `k-1`.
4. **Zk-GaussSum** `tr(L^p)` = weighted sum of closed walks with holonomy `≡ 0 mod k`.
5. **Zk-anti-balance** — behaviour at unbalanced classes vs divisor-balanced.
6. **Zk-cycle gcd-formula** — `dim ker L_{Mob,k}(C_n, W) = gcd(n, k/gcd(k, Σ W))` or similar explicit.
7. **Zk-degree-monotonicity** — spectrum interlacing as `k -> k'` divides.

**From γ (U(1)):**
8. **U1-M1 kernel dichotomy** `{0,1}` per component, a *continuous* strengthening.
9. **U1-M2 Jacobian gauge invariance** `Spec` factors through `J(G) = (R/Z)^{b_1}`.
10. **U1-M3 flat ⇔ coboundary**.
11. **U1-M4 Rellich analytic spectral flow** on continuous `W_t`.
12. **U1-Hellmann-Feynman** — derivative formula.
13. **U1-IDS, Bloch-Floquet, Harper-Hofstadter** — continuous-only on infinite periodic covers.
14. **U1-Cheeger-magnetic** — Cheeger constant with holonomy correction.
15. **U1-tensor non-result** — *no* Kronecker-Hadamard analogue; protects PROVER-C.

From α (Z/3): mostly concrete instances of β and prior structure; treated as fuzzer anchors rather than new structural claims.

## 4. Falsifiability-scope classification (G1–G5)

Per pre-registration discipline (memory/`pre_registration_discipline.md`):

| Tier | G1 (Predictable) | G2 (Observable) | G3 (Falsifiable) | G4 (Specific) | G5 (Pre-registered) |
|------|:-:|:-:|:-:|:-:|:-:|
| Tier-1 (α+β+γ) | ✓ | ✓ | ✓ | ✓ | ✓ |
| Tier-2 (α+β+γ) | ✓ | ✓ | ✓ | ✓ | ✓ |
| Tier-3 γ continuous-only | ✓ | partial (need surrogate) | partial | partial | ✓ |

Tier-3 γ claims (IDS, Bloch-Floquet, Harper-Hofstadter, Cheeger-magnetic) are only finitely-falsifiable on surrogates (e.g. toroidal grids `Z_n × Z_n` as proxy for `Z²` lattice). FUZZER-C must use surrogate schemas and flag them explicitly.

## 5. Ranked Stage 2 FUZZER-C queue

Ranking criteria:
- (a) load-bearing for Stage 3 PROVER-C (Tier-1 first),
- (b) high surprise value if false (would invalidate broad structural claims),
- (c) computational tractability (exhaustive or dense-random),
- (d) already-partial evidence (R6 analogues verified).

### Priority 0 (must pass before PROVER-C can start)

| Rank | Claim | Sheaf | Method | Scope |
|------|-------|-------|--------|-------|
| 1 | Zk-M1 kernel formula `Σφ(d)β^(d)` | β | exhaustive | `k ∈ {2,3,4,5,6,7,8}`, `G ∈ {C_n, K_n, path}`, `n ≤ 7`, all `W` |
| 2 | Z3-M1 `#comp + 2β^(3)` | α | exhaustive | `k=3, G ∈ {C_3..C_9, K_4, K_5}`, all `W` |
| 3 | U1-M1 kernel dichotomy {0,1} | γ | dense random + rational sweep | 500 `(G,W)` random; rational `(1/k)Z/Z` for `k ∈ {2..8}` |
| 4 | U1-M2 Jacobian gauge invariance | γ | random + coboundary perturbation | `Spec(L(W)) == Spec(L(W+δf))` |
| 5 | Zk-M2 charpoly factorisation | β | symbolic factor test | `k ∈ {3,4,6}` |
| 6 | Z3-T2 / Zk-S1 `tr = 2k\|E\|` | α+β | exhaustive | all random `(G,W)`; must be `W`-independent |

### Priority 1 (Tier-2 load-bearing)

| Rank | Claim | Sheaf | Method |
|------|-------|-------|--------|
| 7 | Zk-cycle gcd-formula | β | exhaustive `n = 3..10`, `k = 2..6` |
| 8 | U1-cycle Bloch spectrum | γ | `n = 3..10`, random `θ` |
| 9 | Zk-CRT tensor | β | check `L_{6} ≅ L_{2} ⊗ L_{3}` on `G` small |
| 10 | Zk-GaussSum cubic trace | β | exhaustive triangles with prescribed holonomy |
| 11 | Zk-primes Galois-orbit | β | random `k` prime, check spectrum of `L_χ_i` identical for `i = 1..k-1` |
| 12 | U1-M3 flat ⇔ coboundary | γ | random null-space test vs `δ`-image |
| 13 | Z3-tree / Zk-tree / U1-tree forest flatness | all | random trees + random `W` |
| 14 | Z3-PSD, Zk-PSD, U1-PSD | all | smallest-eigenvalue ≥ -ε over 500 `(G,W)` |
| 15 | U1-bridge insensitivity | γ | graph with distinguished bridges |

### Priority 2 (Tier-3 + fragile targets)

| Rank | Claim | Sheaf | Method | Notes |
|------|-------|-------|--------|-------|
| 16 | Z3-O1 / U1-interlacing | α,γ | random 200 `(G,W)` | **high surprise value if false** — expected to fail in some regime |
| 17 | U1-M4 Rellich analytic flow | γ | numerical `dλ/dt` vs `-2Re(ψ̄ Φ ψ)` | Hellmann-Feynman |
| 18 | U1-random-phase kernel=0 a.s. | γ | Monte-Carlo on connected `G` with `b_1 ≥ 1` |
| 19 | Zk-O2 Gauss-sum matrix-tree | β | exploratory det-vs-weighted-forest |
| 20 | Zk-anti-balance | β | construct maximally-unbalanced classes |
| 21 | U1-Harper-Hofstadter surrogate | γ | finite `Z_n × Z_n` with uniform flux | continuous-only, surrogate test |
| 22 | U1-tensor non-result (anti-fuzz) | γ | attempt Hadamard decompositions; all must fail | protects PROVER-C from over-reach |

## 6. Sub-sheaf work routing for Stage 2

Per voxelize directive (memory/`feedback_voxelize_rounds.md`), FUZZER-C runs as three parallel agents, one per sub-sheaf:

| Agent | Fibre | Load | Owns ranks |
|-------|-------|------|-----------|
| FUZZER-C α | Z/3 concrete | small exhaustive | 2, 6 (α-slice), 13 (α-slice), 14 (α-slice), 16 (α-slice) |
| FUZZER-C β | Z/k structural | moderate exhaustive + symbolic | 1, 5, 6 (β-slice), 7, 9, 10, 11, 13 (β-slice), 14 (β-slice), 19, 20 |
| FUZZER-C γ | U(1) continuous | dense-random + surrogate | 3, 4, 8, 12, 13 (γ-slice), 14 (γ-slice), 15, 16 (γ-slice), 17, 18, 21, 22 |

Each agent produces:
- `findings/round7/stage2_fuzzer_C/sheaf_{α,β,γ}_*/report.md` — per-claim PASS/FAIL + witness counts
- machine-readable summary for Stage 3 gluer

Gluer for Stage 2 will consolidate into `findings/round7/stage2_fuzzer_C/gluer/fiber_2.md` for PROVER-C input.

## 7. Open questions for the PROVER-C stage (flagged early)

Items where FUZZER-C must be conclusive before Lean formalization attempt:

- **Zk-M1 divisor-indexed formula.** Before attempting Lean proof, need complete evidence across k ≤ 8 and all small graphs. Hard target: prove over Mathlib with explicit φ-multiplicity bookkeeping.
- **U1-M4 Rellich analyticity.** Standard textbook, but Lean analytic-matrix-family infrastructure may be sparse — expect to either formalise minimally or cite informally.
- **U1-tensor non-result.** A *negative* claim; needs careful formulation ("there is no pair of unitaries U, D such that...") and is unlikely to be Lean-tractable — probably stays a paper-level structural observation.
- **Harper-Hofstadter on finite surrogate.** Even the surrogate is outside current Lean scope; FUZZER-C evidence is end-state for R7.

## 8. Gluer verdict

All 58 hypotheses across α/β/γ are internally consistent and mutually compatible at rational embedding boundaries. No claim pairs contradict. Queue is ranked; FUZZER-C can proceed on three parallel sheaves.

R7 Stage 1 NEGATOR-C closes. Stage 2 FUZZER-C may launch.
