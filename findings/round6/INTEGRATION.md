# R6 INTEGRATION — 11-stage cosmo-tree consolidation

**Date:** 2026-04-22.
**Author:** Stage 11 INTEGRATOR.
**Scope:** Consolidates Stages 1–10 of Round 6 of the UTAI discovery swarm, applies paper edits recommended by Stages 9 (AMBIGUATOR) and 10 (ADVERSARIAL-PAPER), and records the R7 carry-over queue.

## One-line summary

Round 6 landed **2 new Lean files** (`L16_SpectrumUnion.lean`, `L17_TracesAndLipschitz.lean`, $137+218=355$ LOC, all axiom-clean), **5 new Tier-A theorems** certifying charpoly factorisation, trace decomposition, Frobenius-norm decomposition and shifted-determinant factorisation for the Möbius bundle; verified them against $14{,}011 + 3{,}727 + 300$ numerical probes with zero counterexamples; red-teamed them along five attack vectors with one minor caveat (polarisation vs combinatorial form of the cross-trace identity); audited the paper and found **3 CRITICAL** paper↔Lean contract violations plus 5 HIGH additive opportunities; all of which are resolved by 11 applied paper edits. Paper is structurally consistent (103 balanced environments, all labels resolve). `lake build` green at 1833 objects.

## Landed Lean artefacts (sorry-free, `[propext, Classical.choice, Quot.sound]` only)

| file | LOC | theorems | role |
|------|----:|----------|------|
| `ConnectionLaplacian/L16_SpectrumUnion.lean` | 137 | `connectionLaplacian_charpoly_decomposes`, `mobius_charpoly_eq_scalar_times_signed` (M7), `flat_charpoly_eq_scalar_sq`, `mobius_charpoly_roots_eq_union` (M6), `flat_charpoly_roots_eq_double` | direct-bundle charpoly / spectrum factorisation |
| `ConnectionLaplacian/L17_TracesAndLipschitz.lean` | 218 | `shiftedDet_factorises` (S1), `trace_laplacian_mobius` (S5, $\tr=4|E|$), `trace_sq_laplacian_decomposes` (S3), `frobenius_laplacian_decomposes` (S4), `trace_mul_scalar_signed_eq` (S2, polarisation form) | trace / Frobenius / shifted-det bundle |

Both files imported by the root `ConnectionLaplacian.lean`. Full project builds 1833/1833.

## Stage-by-stage chain (chain-of-stations cosmo-tree)

### Stage 1 — NEGATOR-A (3 sheaf tiles + gluer)
New hypotheses generated per the higher-$n$ voxelization pattern. Key discoveries:
- A5′ / A6′ one-sided monotonicity of $\beta$ under contraction / reverse-contraction.
- Pre-registered as $\tau=1$; subsequently refuted at $n=6$ (Stage 2).

### Stage 2 — FUZZER-A (3 sheaf tiles + gluer)
Three concurrent fuzzers:
- **sheaf-α** (`fuzz.py`, 26 KB): $n\le 5$ exhaustive + $n=6$ scale sample, 9 claims. A5′/A6′ refuted at $\tau=0.9557$; one-sided contraction does not hold. **New master:** L15-reverse deletion inequality $\beta(G\setminus e) \le \beta(G)+1$.
- **sheaf-β** (`fuzz.py`, 24.8 KB, numpy+mpmath prec=50): M6 verified at $1.55\cdot 10^{-15}$ on 3727 $n=6$ iso-configs + 220 $n=7$ random.
- **sheaf-γ** (`fuzz.py`, 23.8 KB, pure-integer exhaustive): 112 connected iso-classes on $n=6$ (OEIS A001349 match); G12 at $5{,}169{,}152/5{,}169{,}152$ exact triples; $1.08\cdot 10^{7}$ integer tests, zero counterexamples.
- **Probe (inline):** `probe_reverse.py` — tested the other direction of A5′ ($\beta(G/e)\le\beta(G)$), also fails at $\tau=0.7555$. Correct refinement: Lipschitz $|\Delta\beta|\le 1$.
- Output: `gluer/fiber_2.md` (6.7 KB) consolidating ranked queue for Stage 3.

### Stage 3 — PROVER-A
Lands `L16_SpectrumUnion.lean` (137 LOC) with M6 (multiset-union identity) and M7 (direct charpoly factorisation). Axiom-clean. Strategy: reuse `laplacian_decomposes` + `Matrix.charpoly_reindex` + `Matrix.charpoly_conj_of_isUnit_det` + `Matrix.charpoly_fromBlocks_zero₁₂` + `Polynomial.roots_mul`.

### Stage 4 — ADVERSARIAL-A
Red-teamed L16 along 5 attack vectors (axiom drift, scalar coercion, reindex mismatch, null-fibre, Boolean/Fin2 mixup). Minor prompt-hygiene note (paraphrase said "$-1$ on wraps" but reality/code is "$+1$ on wraps, $-1$ on non-wraps"; Lean code matches fuzzer byte-for-byte). Verdict: **L16 ACCEPTED**.

### Stage 5 — NEGATOR-B (3 sheaf tiles + gluer)
Generated 17 new claims, 36 sub-claims. 35 at $\tau=1$ including C6-tight at $301{,}249/301{,}249$. **Key new master:** shifted-det factorisation $\det(L_{\text{Mob}}+\alpha I) = \det(\Lscalar+\alpha I)\cdot\det(\Lsigned+\alpha I)$, which collapses 21 sub-claims. C10 $\tr(\Lscalar\cdot\Lsigned)=\tr(\Lscalar^2)-4|W|$ passes as an exact zero (integer polynomial identity).

### Stage 6 — FUZZER-B (inline, not delegated)
$n=7$ gap-check of PROVER-B queue. 9 targets, 14,011 probes, 0 counterexamples. Shifted-det at $8.9\cdot 10^{-15}$; combinatorial identities exact. Decided inline because Stage 5 already had 301k-config support on C6-tight — agent delegation not needed.

### Stage 7 — PROVER-B
Lands `L17_TracesAndLipschitz.lean` (218 LOC) with 5 Tier-A theorems. Tier B (S6 contraction-Lipschitz, S7 vertex-deletion, S8/S9 wrap-flip) **deferred to R7** because `contract` / `deleteVertex` / `flipWrap` constructors not yet in `Basic.lean`. Honest "can't fit in budget" rather than forced.

### Stage 8 — ADVERSARIAL-B
Red-teamed L17 across 5 attack classes (A.1–A.4 scalar/type drift, B.1–B.3 reindex/similarity, C S2 polarisation vs combinatorial, D numerical cross-check, E edge-case `ConnGraph` instances). Verdict: **ACCEPTED-WITH-CAVEATS**. Sole caveat on S2: Lean statement is the polarisation form $2\tr(\Lscalar\Lsigned)=\tr((\Lscalar+\Lsigned)^2)-\tr(\Lscalar^2)-\tr(\Lsigned^2)$ (pure algebra), strictly weaker than the Stage-5/6 combinatorial C10 $\tr(\Lscalar\Lsigned)=\tr(\Lscalar^2)-4|W|$. Not a logic bug but a scope caveat → R7 carry-over.

### Stage 9 — AMBIGUATOR (read-only paper audit)
16 findings, 5 HIGH / 6 MID / 5 LOW. Category E (deprecated prose) empty → R6 additions are purely additive, no overtaken claims. HIGH items all citation-opportunity for L16/L17 landings. Top-3 HIGH: (1) add Prop 9.2 + Appendix rows for L17 trace identities, (2) add direct-bundle remark + shifted-det corollary after Thm 7.5, (3) reconcile abstract vs reproducibility fuzzer counts.

### Stage 10 — ADVERSARIAL-PAPER (red-team paper vs Lean)
16 findings, 3 CRITICAL / 5 HIGH / 5 MID / 3 LOW. **CRITICAL discoveries:**
- **C-1:** Paper Appendix A points at Lean names `flat_cycle_spectrum` and `mobius_cycle_spectrum` as the formalisation of Thm 6.1/6.2 — but these Lean theorems are **trivial existence stubs** (`∃ v, v ≠ 0 ∧ True`), proving nothing about eigenvalues. The real certificates are `scalarCycle_eigenvalue` (L265) and `signedCycle_eigenvalue` (L557), which genuinely prove per-$k$ eigenvalue identities. **Verified directly** by reading `CycleSpectrum.lean` L659–L699.
- **C-2:** §3 proof of Thm 3.1 claims flat case is "specialisation $W=\emptyset$" of the Hadamard proof, but Lean's `laplacian_decomposes` uses $P=1$ (identity) in the flat branch.
- **C-3:** Reproducibility paragraph still cites R4-era counts ($176{,}169$ configs, `findings/round{3,4}/`), while the abstract already references R5's $456{,}950$-config sweep. Internal inconsistency.

### Stage 11 — INTEGRATOR (this document + paper edits)
Applied 11 paper edits addressing all 3 CRITICAL findings plus 7 HIGH / MID follow-ups. Structural verification: 103 balanced `\begin{}`/`\end{}` environments; 3 new labels (`rem:cycle-spectrum-lean`, `rem:direct-bundle-charpoly`, `prop:traces2`) each defined exactly once and referenced 1 / 3 / 3 times respectively. No LaTeX compiler available on this host, so compile-time verification is deferred to the next machine with `tectonic` or `pdflatex`.

## Paper edits applied

| # | target | addresses | section |
|---|--------|-----------|---------|
| 1 | Appendix A bullet re-points to `scalarCycle_eigenvalue` / `signedCycle_eigenvalue` | C-1 | Formalisation summary (§7, line ~874) |
| 2 | New Remark `rem:cycle-spectrum-lean` after Thm 6.2 proof sketch | C-1 support | §6 (line ~830) |
| 3 | New Remark after Thm 3.1 proof (Lean flat branch uses $P=I$) | C-2 | §3 (line ~336) |
| 4 | Reproducibility paragraph rewritten (1833 Lean objects; R3–R6 totals; new paths) | C-3 / A2 / C3 | §7 (line ~1348) |
| 5 | New Remark `rem:direct-bundle-charpoly` after Thm 7.5 (M7 + shifted-det + M6) | B1 / B4 | §9 (line ~1049) |
| 6 | New Proposition `prop:traces2` (quadratic trace and Frobenius identities) + polarisation-form remark | B3 / D1 | §9 (after Prop 9.1) |
| 7 | 7 new Appendix A rows for L16/L17 theorems | H-5 / C1 | §7 table (line ~1342) |
| 8 | Cor 10.2 softened from "forest" to "connected tree" with forest extension note | H-2 | §8 (line ~1138) |
| 9 | New Remark after Cor 10.4 proof flagging `_weak` form in Lean | H-3 | §8 (after line ~1189) |
| 10 | §2.3 PSD prose reordered: sum-of-squares as primary proof, cover-splitting as alternative | H-4 | §2.3 (line ~256) |
| 11 | Thm 6.1 typo fix ("each eigenvalue $\mathbf{e}_k$ an eigenvector") | A1 | §6 (line ~804) |

Not applied (deferred to stylistic pass): A3 (matrix-product notation unification), A4 (notation paragraph for $\II_k$ vs $\mathbf{1}_P$), C2 (§8 formalisation-summary enumeration), C4 (`thm:cover-charpoly` relabel), C5 (flat charpoly passing mention), L-1 (telemetry jargon), L-2 (table slot), L-3 (filename footnote), M-2/M-3/M-4/M-5 (wording polish), D-2 (memory-record cross-ref).

## R7 carry-over queue

The following are tracked for the next round, pre-registered here so they are not forgotten:

### Lean landings (formalisation gaps)

1. **Combinatorial C10 bridge lemma** — $\le 20$ LOC in `L17_TracesAndLipschitz.lean`:
   `theorem trace_mul_scalar_signed_combinatorial : (G.scalarLaplacian * G.signedLaplacianMobius).trace = (G.scalarLaplacian * G.scalarLaplacian).trace - 4 * (G.wrapEdges.card : ℝ)`.

2. **Constructors on `ConnGraph`** in `Basic.lean`: `contract`, `deleteVertex`, `flipWrap`, with their wrap-transport rules. Unlocks:
   - S6 contraction-Lipschitz $|\beta(G) - \beta(G/e)| \le 1$ for non-bridge $e$.
   - S7 vertex-deletion $|\beta(G) - \beta(G-v)| \le \max(1, \deg(v))$.
   - S8 bridge-wrap-flip preserves $\beta$.
   - S9 non-bridge wrap-flip $|\Delta\beta| \le 1$.

3. **Genuine multiset-spectrum theorems** `scalarCycle_spectrum_eq` and `signedCycle_spectrum_eq` in `CycleSpectrum.lean`, assembling the per-$k$ certificates into the full `Polynomial.roots = Multiset`. This retires the trivial existence stubs at L659, L679.

4. **`fundamentalCycleWalk` helper** + winding-number argument in `L14_CycleEw.lean` to upgrade `cycle_isBalanced_iff_even_wrap_weak` to the fully constructive form Cor 10.4 states.

5. **Disconnected-forest lift** in `L11_Trees.lean`: per-component combination of `tree_isBalanced_of_isTree` to cover disconnected forests for Cor 10.2.

### Heat / resolvent / trace-power corollaries (≤ 3 LOC each)
Cheap consequences of M6 + Newton's identities on the charpoly factorisation:
- C2_t heat-trace additivity $\tr(e^{-tL_{\mathrm{Mob}}}) = \tr(e^{-t\Lscalar}) + \tr(e^{-t\Lsigned})$ for $t \in \{0.1, 0.5, 1, 2\}$.
- C4_a resolvent-trace additivity for $\alpha \in \{0.5, 1, 2\}$.
- C1_k trace-power identities for $k \in \{1, \ldots, 10\}$ via Newton's identities (S3 already nails $k=2$).

### Paper polish (MID / LOW from Stages 9 / 10)
- Unify matrix-product notation (`\cdot` vs thin-space); add notation paragraph in §2.
- Extend §8 formalisation-summary to cover §9–§10 theorems.
- Resolve `thm:cover-charpoly` label/name drift.
- Example 11.3 telemetry jargon (`τ=0.0000`) — define or remove.
- Footnote "KernelDim.lean abbreviates KernelDimension.lean" — use real filenames throughout.

## Axiom-cleanliness audit

All 5 new L16 theorems + all 5 new L17 theorems verified via `#print axioms` against `{propext, Classical.choice, Quot.sound}`. Zero `sorry`, zero `native_decide`, zero custom axioms. Full project `lake build` green at 1833 objects.

## Cross-scale evidence summary

| identity | evidence source | max rel diff | tests | outcome |
|----------|-----------------|-------------:|------:|---------|
| M6 multiset-union | Stage-2 sheaf-β + Stage-6 fuzzer-B | $1.55\cdot 10^{-15}$ | $3727 + 220 + 300$ | **Lean-proved** |
| M7 direct charpoly | Stage-2 sheaf-β | $1.55\cdot 10^{-15}$ | same | **Lean-proved** |
| S1 shifted-det $\alpha\in\{1,2.5\}$ | Stage-6 fuzzer-B | $8.9\cdot 10^{-15}$ | 600 | **Lean-proved** |
| S3 $\tr(L_{\mathrm{Mob}}^2)$ decomp | Stage-6 fuzzer-B | exact | 300 | **Lean-proved** |
| S4 Frobenius decomp | Stage-6 fuzzer-B | exact | 300 | **Lean-proved** |
| S5 $\tr L_{\mathrm{Mob}} = 4|E|$ | Stage-2 | exact | all | **Lean-proved** |
| S2 polarisation | Stage-5 + Stage-6 | exact | 300 | **Lean-proved** (polarisation form) |
| C10 combinatorial $\tr=\tr^2-4|W|$ | Stage-5 + Stage-6 | exact | 300 | **R7 carry-over** |
| C5 contraction-Lipschitz | Stage-5 + Stage-6 | exact | 6551 | **R7 carry-over** (needs `contract` API) |
| C6-tight vertex-deletion | Stage-5 + Stage-6 | exact | 303349 | **R7 carry-over** (needs `deleteVertex` API) |
| C13/C14 wrap-flip bundle | Stage-6 | exact | 3823 | **R7 carry-over** (needs `flipWrap` API) |

## Verdict

R6 promoted **5 hypotheses to Lean-certified master lemmas** ($L17$ Tier-A), with evidence spanning $10^4$+ numerical probes and 5 independent adversarial passes. Three CRITICAL paper↔Lean contract issues (two pre-existing, one R4-staleness) were identified by Stage 10 and corrected by Stage 11. The paper now cites every R6 Lean landing and accurately reports what is proved vs what is numerically confirmed. The R7 queue is well-scoped: it consists of the $\le 20$-LOC combinatorial C10 bridge, four `Basic.lean` constructor extensions that would unlock the entire $\beta$-Lipschitz bundle, and three paper-polish items all MID or lower priority.

**Task #34 (R6 Stages 2–11 chain advance): completed.**
