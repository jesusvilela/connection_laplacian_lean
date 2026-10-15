# Round 8 — Independent reference implementation of the paper's Z/2 connection Laplacian

Files:

- `independent_impl.py` — numpy-only implementation, written **exclusively** from
  `paper/paper.tex` (no Lean sources, no prior fuzzers consulted).
- `selftest.py` — internal sanity checks (paper theorems + hand-derived small
  cases). Output: `selftest_output.txt`; **all 8887 checks pass** (exit 0,
  reproducible across runs).

All line numbers below refer to `paper/paper.tex`.

---

## 1. Formulas implemented (with paper quotes and references)

### 1.1 Connection matrices on edges (Sec. 1, lines 135–143)

> "Attach to each $e\in E$ a $2\times 2$ real matrix $\Phi(e)$ by
> $\Phi(e) \defeq \begin{cases} \sigma_x & \text{if } e\in W,\\ \II_2 & \text{if } e\notin W, \end{cases}$
> $\sigma_x = \begin{pmatrix}0&1\\1&0\end{pmatrix}$."

### 1.2 Connection Laplacian `connection_laplacian(adj, wrap_e)` (eq:connection-laplacian, lines 144–153)

> "$L_{\operatorname{Mob}}[u,v] \defeq \begin{cases} \deg(u)\,\II_2 & u=v,\\ -\,\Phi(\{u,v\}) & \{u,v\}\in E,\\ 0 & \text{otherwise.} \end{cases}$"

Block placement implemented: diagonal block `deg(u) * I2`; **non-wrap edge block
`-I2`; wrap edge block `-sigma_x`**. Flat index of the paper's $(u,i)\in V\times\operatorname{Fin}2$
is `2*u + i` (vertex-major; see Ambiguity A1).

### 1.3 Scalar Laplacian `scalar_laplacian(adj)` (Sec. 2.3, lines 243–249)

> "$\Lscalar[u,v] \defeq \begin{cases} \deg(u) & u=v,\\ -1 & \{u,v\}\in E,\\ 0 & \text{otherwise,}\end{cases}$"

Implemented as `diag(deg) - adj`.

### 1.4 Signed (Möbius) Laplacian `signed_laplacian(adj, wrap_e)` (Sec. 2.3, lines 251–260)

> "$\Lsigned[u,v] \defeq \begin{cases} \deg(u) & u=v,\\ +1 & \{u,v\}\in E,\ \{u,v\}\in W,\\ -1 & \{u,v\}\in E,\ \{u,v\}\notin W,\\ 0 & \text{otherwise.}\end{cases}$"

i.e. **wrap edges carry off-diagonal `+1`, non-wrap edges `-1`** — the opposite
sign, exactly as the task phrased it. The convention is independently pinned by
the paper's quadratic form (Sec. 2.3 lines 266–269 and Lemma 8.5 lines 1105–1113):

> "$\pair{x}{\Lsigned x} = \sum_{\{u,v\}\in E\setminus W} (x_u - x_v)^2 + \sum_{\{u,v\}\in W} (x_u + x_v)^2$"

### 1.5 Flat Laplacian `flat_laplacian(adj)` (lines 157–159)

> "The flat Laplacian $L_{\operatorname{flat}}$ is obtained by the same recipe
> with $\Phi\equiv \II_2$ ... it agrees with two copies of the ordinary graph
> Laplacian."

Implemented as `np.kron(Lsc, I2)`.

### 1.6 Orientation double cover `orientation_cover_adjacency(adj, wrap_e)` (Def. 4.1, lines 380–391)

> "$(u,b)\sim_{\tG} (v,c) \iff \{u,v\}\in E \;\text{and}\; \bigl(\{u,v\}\in W \Leftrightarrow b\ne c\bigr)$"

Non-wrap edges connect **same** sheets, wrap edges connect **opposite** sheets.
Bool encoding `0 = false = bot`, `1 = true = top`; flat index `2u + b`.

### 1.7 Balance `is_balanced_component(adj, wrap_e, comp)` (Def. 5.1, lines 556–566)

> "A connected component $C\in\comp(G)$ is balanced iff there is a map
> $\varepsilon:V\to\operatorname{Bool}$ such that for every edge $\{u,v\}\in E$
> with $[u]_{\sim_G} = C$: $\{u,v\}\in W \iff \varepsilon(u)\ne \varepsilon(v)$."

Scope per Remark 5.2 (lines 568–589): **component-local** (only edges inside `C`
constrained) and **isolated vertices are vacuously balanced** (explicitly
"load-bearing" per the paper). Implementation: root-labelled search assigning
`eps(v) = eps(u) XOR 1_{uv in W}` along tree edges, then the biconditional is
checked on every edge of the component (this decides the existential because any
witness is fixed by its root value up to global flip).

### 1.8 Fibre sheets `fibre_sheets(adj, wrap_e)` (Thm 5.3 thm:fiber-card, lines 594–602; Cor 5.7, lines 700–709)

> "$\#\pi^{-1}(C) \;=\; \begin{cases} 2 & C \text{ balanced,}\\ 1 & \text{otherwise.} \end{cases}$"
> "$\#\comp(\tG) \;=\; \#\comp(G) \;+\; \beta(G)$."

Returns per-component sheet counts (2 iff balanced, per the balance predicate)
and the total cover component count. A second function
`cover_component_fibres(adj, wrap_e)` measures the same quantities
**constructively** by building the cover of Def. 4.1 and counting connected
components over each base component — the two routes agreeing is exactly
Theorem 5.3, and it is checked in the selftest.

### 1.9 Spectrum / kernel

`spectrum(M)`: `eigvalsh`, sorted ascending, each eigenvalue rounded to 8
decimals (1e-8, audit instruction). `kernel_dim(M)`: number of eigenvalues with
`|lambda| <= 1e-8`.

### 1.10 Auxiliary

`edges`, `degrees`, `connected_components`, `beta` (number of balanced
components, Def. 5.1 lines 563–565), `I2`, `SIGMA_X`, `HADAMARD`
(eq:Rhat lines 226–234: $\widehat R=\begin{pmatrix}1&1\\1&-1\end{pmatrix}$,
$\widehat R\widehat R=2\II_2$).

---

## 2. API

```python
import numpy as np
# adj:    n x n numpy array, entries {0,1}, symmetric, zero diagonal
# wrap_e: set of frozenset({u,v})   (canonical; a 0/1 adjacency matrix or an
#         iterable of 2-tuples is accepted and converted; validated so that
#         W ⊆ E, else ValueError)
scalar_laplacian(adj)                        -> ndarray (n, n)
signed_laplacian(adj, wrap_e)                -> ndarray (n, n)
connection_laplacian(adj, wrap_e)            -> ndarray (2n, 2n), index 2*u+i
flat_laplacian(adj)                          -> ndarray (2n, 2n) = kron(Lsc, I2)
orientation_cover_adjacency(adj, wrap_e)     -> ndarray (2n, 2n), index 2*u+b
spectrum(M)                                  -> sorted eigenvalues, rounded 1e-8
kernel_dim(M, tol=1e-8)                      -> int
connected_components(adj)                    -> list of sorted vertex tuples
is_balanced_component(adj, wrap_e, comp)     -> bool   (Def. 5.1, component-local)
beta(adj, wrap_e)                            -> int    (number balanced comps)
fibre_sheets(adj, wrap_e)                    -> dict with keys
    "components" (list of tuples), "balanced" (list of bool),
    "sheets" (list of {1,2}), "total_cover_components" (int)
cover_component_fibres(adj, wrap_e)          -> (list of {1,2}, total)  [constructed]
```

---

## 3. Selftest results

`python selftest.py` → exit 0, deterministic across runs. Full output
(`selftest_output.txt`):

```
========================================================================
selftest.py -- internal sanity checks for independent_impl.py
sources of truth: paper/paper.tex theorems + hand computations
========================================================================
[1] Hand-written matrices (triangle, P3)
[2] Hand-derived spectra
[3] Hand-derived kernel dimensions (via Cor 9.4 parity + Thms 6.x)
[4] The paper's own examples and remarks
[5] Cycle spectra [Thm 7.1 flat-cycle; Thm 7.2 mobius-cycle]
[6] Structural battery on named configurations
  ...battery done for 23 named configs (25 checks each)
[7] Exhaustive wrap subsets on cycles C3, C4, C5 [Cor 9.4]
  ...56 cycle configurations, all structural checks
[8] Exhaustive wrap subsets on trees P3, P4, K1,3 [Thm 9.1]
  ...20 tree configurations, all structural checks
[9] Seeded random sweep, n in 2..6 (Thms 6.2, 6.3, 8.6, 5.3)
  ...250 random configurations, all structural checks
========================================================================
TOTAL individual checks: 8887
ALL CHECKS PASSED
```

What is checked, and on what authority:

**Hand-derived (pencil-and-paper) facts.** Entrywise matrices: `Lsc(C3)`,
`Lsg(C3)` for W = ∅ / 1 edge / 2 edges / 3 edges, `L_Mob(C3, W={01})` and
`L_Mob(P3, W={01})` written out 6×6, cover of `C3` (2-regular on 6 vertices,
Lem 4.3; single 6-cycle for one wrap, two disjoint triangles for W=∅).
Hand spectra: `Lsc(C3)={0,3,3}`, `Lsg(C3)` = `{0,3,3}` (W even) / `{1,1,4}`
(W odd, char. poly `(λ−1)²(λ−4)`), `Lsc(C4)={0,2,2,4}`,
`Lsg(C4,W={01})={2−√2,2−√2,2+√2,2+√2}`, `Lsg(C4,`2 wraps, adjacent or
opposite`)={0,2,2,4}` (explicit diagonal ±1 switching conjugations given),
`Lsc(P3)={0,1,3}`, `Lsg(P3,W={01})={0,1,3}` (char. poly λ(λ−1)(λ−3)), plus the
explicit switching identity `Lsg(P3,W={01}) = D Lsc D`, `D=diag(1,−1,−1)`
(the paper's Example 10.2 colouring). Hand kernel dimensions for triangle
(0/1/2/3 wraps), square (0/1/2-adjacent/2-opposite wraps) and P3 (all wrap
subsets), all consistent with Cor 9.4 parity + Thms 6.2/6.3.

**Paper theorems, checked on every configuration** (23 named + 56 exhaustive
cycle + 20 exhaustive tree + 250 seeded random, n ≤ 6, disconnected graphs
included): spectral unions `Spec(L_Mob) = Spec(Lsc) ⊎ Spec(Lsg)` (Remark 8.7 /
Thm 3.1), `Spec(L_flat) = Spec(Lsc) ⊎ Spec(Lsc)` (lines 157–159),
`Spec(L̃) = Spec(Lsc) ⊎ Spec(Lsg)` (Thm 8.6 cover-charpoly); kernel formulas
`ker Lsc = #comp` (Thm 6.1), `ker Lsg = β` (Thm 6.2), `ker L_Mob = #comp + β`,
`ker L_flat = 2#comp` (Thm 6.3), `ker L̃ = ker Lsc + ker Lsg` (Cor 4.5);
entrywise Hadamard decompositions `(1/2)P L_Mob P → diag(Lsc, Lsg)`,
`(1/2)P L_flat P → diag(Lsc, Lsc)` (Thm 3.1, proof lines 331–338) and
`(1/2)P L̃ P → diag(Lsc, Lsg)` (Thm 4.4, proof lines 473–509) with
`P = kron(I, R̂`; Kronecker-sum formula for `L_Mob` (line 154); traces
`tr Lsc = tr Lsg = 2#E`, `tr L_flat = tr L_Mob = 4#E` (Prop 8.1),
`tr(L_Mob²) = tr(Lsc²) + tr(Lsg²)` and the Frobenius identity (Prop 8.2);
fibre cardinalities from the cover construction equal the balance-derived
sheets, and `#comp(G̃) = #comp(G) + β` (Thm 5.3, Cor 5.7); inequalities and
strictness (Prop 8.3, Thm 6.4).

**Paper-only external anchors.** Cycle spectra `Spec Lsc(C_n) = {2−2cos(2πk/n)}`
(Thm 7.1) and `Spec Lsg(C_n, W={{0,1}}) = {2−2cos((2k+1)π/n)}` (Thm 7.2) for
n = 3..6; parity law `β(C_n,W) = [|W| even]` exhaustively for C3/C4/C5 (Cor 9.4);
trees balanced for every W, `ker L_Mob = 2` (Thm 9.1, Cor 9.2) exhaustively on
P3/P4/K1,3; the paper's own examples: K4 with wrap matching has `β = 0`,
`ker Lsg = 0` (Remark 6.5 — the case that refutes the false parity formula (★)),
empty graph on 3 vertices has `β = 3`, `ker L_Mob = 6` (Ex 10.1), P3 with bridge
wrap balanced (Ex 10.2), β drop 3 → 2 after adding a non-wrap edge (Ex 10.3),
`ker Lsg(K3, W={{v0,v1}}) = 0` (Ex 10.4), all-wrap `C_n` balanced iff n even
(Remark 7.5), single-wrap `C_n` has `ker Lsg = 0` and `ker L_Mob = 1 < 2`
(Cor 7.4), isolated vertex vacuously balanced (Remark 5.2b).

No failures. (Two initial failures were bugs in the *test expectations*, not the
implementation: a reused cover variable, and a wrong switching witness
`diag(1,−1,1)` instead of `diag(1,−1,−1)`; both corrected.)

---

## 4. Points where the paper is ambiguous or silent about conventions

These are the judgment calls an implementer must make; any divergence between
this implementation and the Lean formalisation should be audited against this
list.

- **A1. Kronecker ordering inconsistency (line 154–156).** The paper's
  "equivalently" formula mixes conventions: `D ⊗ I2` is vertex-major (index
  `(u,i) ↦ u·2+i`) while `Φ(e) ⊗ 1_e` is fibre-major (index `(i,u) ↦ i·n+u`);
  the two cannot literally be summed without a shuffle. The operative
  display (1) (lines 146–153) is unambiguous, and we implemented it with
  vertex-major flattening; the vertex-major equivalent of the edge term is
  `kron(1_e, Φ(e))`. Our first selftest draft literally transcribed
  `kron(Φ(e), 1_e)` and failed every configuration — a trap for any reader.
- **A2. Sign convention of the signed Laplacian.** Stated three times
  independently (display lines 254–260; quadratic form lines 266–269/Lemma 8.5;
  Hadamard block `−2 diag(1,−1)` in Thm 3.1's proof). All three agree, so no
  ambiguity remains *if* one reads all three; reading only the display, a
  sign slip against the Zaslavsky convention (wrap = "negative" edge, off-diagonal +1)
  would be easy. We cross-verified all three.
- **A3. Component-local vs graph-global balance.** The paper itself flags this
  (Remark 5.2a): for disconnected graphs the two notions differ, and "every
  theorem below uses the component-local version". We implement component-local,
  with isolated vertices vacuously balanced (Remark 5.2b, "load-bearing").
- **A4. "Number of sheets of the cover fibre".** The cover always has 2|V|
  vertices and every cover vertex has degree `deg_G(u)` (Lemma 4.3) — the
  covering map is everywhere locally 2-sheeted. The per-component "sheet count"
  of Thm 5.3 is the **cardinality of the π₀-fibre** (1 or 2), a global, not
  local, quantity. The task's phrasing required resolving this terminological
  gap; we implemented `#π₀⁻¹(C) ∈ {1,2}` per Thm 5.3.
- **A5. Bool/Fin2 encoding of the fibre.** The paper uses Fin2 in Sec. 3 and
  Bool in Sec. 4 ("the same matrix under the obvious bijection", lines 236–239)
  and maps `(v,⊥) ↦ ι_ℓv`, `(v,⊤) ↦ ι_rv` (Thm 4.4). The Hadamard on Bool has
  its −1 entry at `(⊤,⊤)` (lines 439–444). We used `0 = ⊥` (left block),
  `1 = ⊤` (right block); swapping the labels conjugates by a block permutation
  and changes no spectrum or kernel count, but would change entrywise matrix
  comparisons.
- **A6. Scope of the cycle theorems.** Thm 7.2 is stated only for the single
  wrap edge `W = {{0,1}}`; for general W on a cycle the paper only proves the
  parity law for β (Cor 9.4), not a full spectrum formula. The selftest
  accordingly asserts full spectra only for W ∈ {∅, single edge} and
  2-wrap C4 (hand-derived via explicit switching conjugations), and only
  kernel dimensions elsewhere.
- **A7. `ker L_Mob` "inside ℂ^{2V}"` (Example 10.1, line 1354).** The paper
  switches to complex ambient space for kernel counting; for real symmetric
  matrices the kernel dimension over ℝ and ℂ coincide, so the convention is
  immaterial — but a formalisation could in principle state one or the other.
- **A8. Numerical tolerances.** The paper prescribes none (its fuzzers chose
  their own); the 1e-8 rounding for `spectrum` and 1e-8 threshold for
  `kernel_dim` come from the audit instructions, not the paper.
- **A9. W ⊆ E validation.** The paper defines a connection graph with
  `W ⊆ E` (line 215) but says nothing about behavior when the input violates
  it; we raise `ValueError` rather than silently ignoring such edges.
- **A10. Unproved (numerically-confirmed-only) statement deliberately NOT
  checked as a theorem.** Remark 8.3 (lines 1072–1082) states the combinatorial
  cross-term `tr(Lsc·Lsg) = tr(Lsc²) − 4#W` and explicitly marks it "not yet a
  separately named Lean theorem". Per the audit rule (only paper-proved
  relations), it is excluded from the selftest; noted here because it is the
  one identity in the paper's own text whose formal status is provisional.

---

## 5. Conclusion

The independent implementation reproduces, from the paper's conventions alone,
every structural theorem the paper states about `L_Mob`, `L_flat`, `L^sc`,
`L^sg` and the orientation cover — 8887 internal checks over 349
configurations (named, exhaustive cycles/trees, seeded random), zero failures.
The conventions that a formalisation could most plausibly get wrong (A1
Kronecker order, A2 sign of wrap edges, A3 balance scope, A4 sheet-count
semantics) are precisely the ones called out above.
