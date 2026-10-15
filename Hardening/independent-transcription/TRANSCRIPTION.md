# Independent transcription audit — seven spine theorems

Date: 2026-10-14.
Auditor method: the Lean statements below were copied character-for-character
from the sources in `ConnectionLaplacian/` (toolchain `leanprover/lean4:v4.11.0`,
Mathlib v4.11.0 from `lake-manifest.json`); the paper quotes were copied
character-for-character from `paper/paper.tex`. No material under
`Hardening/` was read prior to writing this file (fresh-eyes audit). No web
search was performed.

**Transcription conventions.**

* Each Lean block is a *standalone* theorem: the section `variable (G : ConnGraph)`
  is expanded into an explicit `(G : ConnGraph)` binder (except T4, whose source
  already binds `G` explicitly), and the block carries the `open` declarations of
  its source file so it can be dropped into a file that imports
  `ConnectionLaplacian`.
* The theorem names below carry a trailing `'` **only** to avoid clashing with the
  library's own declarations when the block is dropped into such a file; everything
  after the name, up to and including the type ascription and the final `:=`, is
  verbatim from the source (the `by`-proof is replaced by a one-line delegation to
  the library theorem so the block elaborates).
* All source files sit inside `namespace ConnectionLaplacian` / `namespace
  ConnGraph`; the standalone blocks reproduce this.
* Verified Mathlib v4.11.0 definitions used in the judgements (from
  `.lake/packages/mathlib`):
  `Matrix.PosSemidef (M : Matrix n n R) := M.IsHermitian ∧ ∀ x : n → R, 0 ≤ dotProduct (star x) (M *ᵥ x)`
  (`Mathlib/LinearAlgebra/Matrix/PosDef.lean:45-46`), and
  `Matrix.charpoly (M : Matrix n n R) : R[X] := (charmatrix M).det`, i.e.
  `det (X•I − M)` (`Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean:90-91`).

Supporting Lean definitions (for reading the statements standalone):

* `ConnGraph` (`Basic.lean:54-61`): fields `V` (`Type*` with `Fintype`,
  `DecidableEq`), `graph : SimpleGraph V` (with `DecidableRel graph.Adj`), and
  `wrap : graph.edgeSet → Prop` (with `DecidablePred wrap`).
* `scalarLaplacian : Matrix G.V G.V ℝ := G.graph.lapMatrix ℝ`
  (`KernelDimension.lean:182-183`) — the ordinary graph Laplacian.
* `signedLaplacianMobius : Matrix G.V G.V ℝ` (`KernelDimension.lean:190-197`):
  diagonal `deg(u)`, off-diagonal `+1` on wrap edges, `−1` on non-wrap edges,
  `0` elsewhere.
* `laplacian (mobius : Bool) : Matrix (G.V × Fin 2) (G.V × Fin 2) ℝ`
  (`Basic.lean:99-101`) — the flattened block connection Laplacian; `true` =
  Möbius mode (σ_x on wrap edges).
* `orientationDoubleCover : ConnGraph` (`L5_Cover.lean:112-116`): vertex set
  `G.CoverV = G.V × Bool`, cover graph, and `wrap := fun _ => False` (trivial
  connection).
* `isBalanced (C : G.graph.ConnectedComponent) : Prop` (`L6_Cohomology.lean:52-57`):
  ∃ `ε : G.V → Bool` with, on every edge of the component,
  `wrap e ↔ ε u ≠ ε v` (component-local, matching paper Def. 2.3).
* `numBalancedComponents : ℕ := Fintype.card {C // G.isBalanced C}`
  (`L6_Cohomology.lean:63-64`).
* `eraseEdge (e : G.graph.edgeSet) : ConnGraph` (`L15_BridgeMonotone.lean:57-65`):
  `graph := G.graph.deleteEdges {e.val}` with `wrap` inherited on surviving edges.

---

## T1. `cover_charpoly_eq_scalar_times_mobius`

**Source:** `ConnectionLaplacian/L10_CoverCharpoly.lean:115-117`.
**Section context** (lines 32-39): `namespace ConnectionLaplacian`;
`open Matrix BigOperators`; `open Polynomial (C)`; `namespace ConnGraph`;
`variable (G : ConnGraph)`.

```lean
import ConnectionLaplacian

namespace ConnectionLaplacian.ConnGraph

open Matrix BigOperators
open Polynomial (C)

theorem cover_charpoly_eq_scalar_times_mobius' (G : ConnGraph) :
    (G.orientationDoubleCover.scalarLaplacian).charpoly =
      G.scalarLaplacian.charpoly * G.signedLaplacianMobius.charpoly :=
  G.cover_charpoly_eq_scalar_times_mobius

end ConnGraph
```

**Paper counterpart:** Theorem 5.5 `thm:cover-charpoly`
(`paper/paper.tex:1141-1153`), "Multiplicative spectral partition: cover
characteristic polynomial":

```latex
\begin{theorem}[Multiplicative spectral partition: cover
characteristic polynomial]\label{thm:cover-charpoly}
Let $\tL = \Lscalar(\tG)$ be the scalar Laplacian of the orientation
double cover of~$G$. Then the characteristic polynomials factor as
\[
  \det\bigl(\lambda\,\II_{\tV} - \tL\bigr) \;=\;
  \det\bigl(\lambda\,\II_V - \Lscalar(G)\bigr)\cdot
  \det\bigl(\lambda\,\II_V - \Lsigned(G)\bigr).
\]
Equivalently, as multisets the spectra satisfy
$\operatorname{Spec}(\tL) = \operatorname{Spec}(\Lscalar(G)) \uplus
\operatorname{Spec}(\Lsigned(G))$.
\end{theorem}
```

**Judgement:** The Lean statement expresses exactly the same claim: since
`Matrix.charpoly M = det (X•I − M)`, the Lean polynomial identity is equivalent
to the paper's determinant identity for all `λ`; it holds for every connection
graph `G` with no connectedness hypothesis, matching the paper's quantifier-free
"for G" (the cover's trivial wrap `fun _ => False` matches Def. 4.1's
"W̃ = ∅", and `charpoly` sign convention `det(X•I − M)` matches the paper's
`det(λI − ·)`). The paper's trailing "Equivalently, as multisets …" clause is an
informal corollary in the paper and is *not* part of this Lean statement (for the
cover it is not a separately named Lean theorem; see also Discrepancies, item 4).

---

## T2. `isBalanced_iff_closedWalk_wrap_even`

**Source:** `ConnectionLaplacian/L12_WalkH1.lean:303-308`.
**Section context** (lines 28-34): `namespace ConnectionLaplacian`;
`open Matrix BigOperators`; `namespace ConnGraph`;
`variable (G : ConnGraph)`. (No `open Polynomial`.)

```lean
import ConnectionLaplacian

namespace ConnectionLaplacian.ConnGraph

open Matrix BigOperators

theorem isBalanced_iff_closedWalk_wrap_even' (G : ConnGraph)
    (C : G.graph.ConnectedComponent) : G.isBalanced C ↔
      ∀ (v : G.V) (p : G.graph.Walk v v),
        G.graph.connectedComponentMk v = C →
        Even (p.edges.countP
                (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩))) :=
  G.isBalanced_iff_closedWalk_wrap_even C

end ConnGraph
```

**Paper counterpart:** Theorem 6.7 `thm:walk-sum`
(`paper/paper.tex:1273-1277`), "Walk-sum detector for balance":

```latex
\begin{theorem}[Walk-sum detector for balance]\label{thm:walk-sum}
Let $C\in\comp(G)$. Then $C$ is balanced iff every closed walk
$w:v\to v$ with $v\in C$ satisfies
$\sum_{e\in w} \mathbf{1}_{e\in W} \equiv 0 \pmod 2$.
\end{theorem}
```

**Judgement:** Same claim. Lean's `isBalanced` is the component-local 2-colouring
definition matching the paper's Def. 4.2 (`def:balanced`, `paper.tex:556-566`,
with the same Remark 4.3(a) component-local convention); `p.edges.countP
(wrap-indicator)` counts wrap-edge traversals of the closed walk `p` **with
multiplicity**, and `Even` of that count is exactly
`Σ_{e∈w} 1_{e∈W} ≡ 0 (mod 2)`; `G.graph.connectedComponentMk v = C` is Lean's
`v ∈ C`; quantifier structure (∀ v ∈ C, ∀ closed walk at v) matches. No
discrepancy in quantifiers, hypotheses, or conventions.

---

## T3. `signedLaplacianMobius_posSemidef`

**Source:** `ConnectionLaplacian/L13_PSD.lean:299-300`.
**Section context** (lines 23-29): `namespace ConnectionLaplacian`;
`open Matrix BigOperators`; `namespace ConnGraph`;
`variable (G : ConnGraph)`. (No `open Polynomial`.)

```lean
import ConnectionLaplacian

namespace ConnectionLaplacian.ConnGraph

open Matrix BigOperators

theorem signedLaplacianMobius_posSemidef' (G : ConnGraph) :
    G.signedLaplacianMobius.PosSemidef :=
  G.signedLaplacianMobius_posSemidef

end ConnGraph
```

**Paper counterpart:** Lemma 5.4 `lem:signed-psd`
(`paper/paper.tex:1105-1114`), "Positive semidefiniteness of the signed
Laplacian":

```latex
\begin{lemma}[Positive semidefiniteness of the signed
Laplacian]\label{lem:signed-psd}
$\Lsigned(G) \succeq 0$. Indeed
\[
  \pair{x}{\Lsigned(G)\, x}
  = \!\!\sum_{e=\{u,v\}\in E\setminus W}\! (x_u - x_v)^2
    + \sum_{e=\{u,v\}\in W} (x_u + x_v)^2
\qquad \text{for all } x\in\RR^V.
\]
\end{lemma}
```

**Judgement:** The Lean statement asserts the same PSD claim over the same field
ℝ for every connection graph (Mathlib's `PosSemidef` is
`IsHermitian ∧ ∀ x : V → ℝ, 0 ≤ dotProduct (star x) (M *ᵥ x)`, and over ℝ
`star x = x`, so this is ⟨x, L^sg x⟩ ≥ 0 for all x ∈ ℝ^V, i.e. `⪰ 0`);
however, the paper's lemma additionally asserts the explicit sum-of-squares
quadratic-form identity, which the public Lean statement does **not** carry (the
identity is proved en route in private lemmas `sLM_quadForm_raw` /
`sLM_quadForm_nonneg`, `L13_PSD.lean:125-249`) — see Discrepancies, item 2.

---

## T4. `numBalancedComponents_monotone_remove_nonwrap_nonbridge`

**Source:** `ConnectionLaplacian/L15_BridgeMonotone.lean:254-258`.
**Section context** (lines 38-44): `namespace ConnectionLaplacian`;
`open Matrix BigOperators`; `namespace ConnGraph`;
`variable (G : ConnGraph)` — note the theorem **re-binds** `(G : ConnGraph)`
explicitly, so the standalone form needs no expansion; the statement is verbatim
including the binder order and the underscore-hypothesis `_hnonwrap`.

```lean
import ConnectionLaplacian

namespace ConnectionLaplacian.ConnGraph

open Matrix BigOperators

theorem numBalancedComponents_monotone_remove_nonwrap_nonbridge'
    (G : ConnGraph) (e : G.graph.edgeSet)
    (_hnonwrap : ¬ G.wrap e)
    (hnonbridge : ¬ G.graph.IsBridge e.val) :
    G.numBalancedComponents ≤ (G.eraseEdge e).numBalancedComponents :=
  numBalancedComponents_monotone_remove_nonwrap_nonbridge G e _hnonwrap hnonbridge

end ConnGraph
```

**Paper counterpart:** there is **no main-text theorem** stating this. The only
links are (a) the appendix index row (`paper/paper.tex:1480-1481`) and (b)
Example 7.4 `ex:cross-merge` (`paper/paper.tex:1376-1392`), which is a
*counter-claim about edge addition* that the appendix row labels as refined by
this Lean theorem:

```latex
Ex.~\ref{ex:cross-merge} (R5 refinement, C1 $\tau=1$) &
  \texttt{numBalancedComponents\_monotone\_remove\_nonwrap\_nonbridge} & \texttt{L15\_BridgeMonotone.lean} \\
```

```latex
\begin{example}[Adding a non-wrap edge between components can
\emph{decrease} $\beta$]\label{ex:cross-merge}
The fuzzy-logic sweep (\S\ref{sec:formalisation}, claim
\texttt{C2}, $\tau=0.0000$) refutes the naive monotonicity
``adding a non-wrap edge can only preserve or increase
$\beta$''. On three isolated vertices ($W=\emptyset$, so
$\beta=3$), adding the non-wrap edge $\{v_0,v_1\}$ merges two
balanced components into one still-balanced component and drops
$\beta$ to $2$. The correct law is bidirectional: for a non-wrap
edge $e$ joining two distinct components,
$\beta(G+e)\in\{\beta(G)-1,\beta(G)\}$, with $-1$ when \emph{at
least one} endpoint lies in a balanced component and $0$ when both
endpoints lie in unbalanced components. (In the mixed
balanced-plus-unbalanced case, the merged component is unbalanced,
so the pre-existing balanced component is lost and $\beta$ drops
by~$1$.)
\end{example}
```

**Judgement:** The Lean claim — for every connection graph `G`, every edge `e`
with `¬ G.wrap e` and `¬ G.graph.IsBridge e.val`, one has
`β(G) ≤ β(G − e)` (where `β = numBalancedComponents` matches the paper's
`β(G) = #comp^bal(G)` and `G − e = eraseEdge e` is the canonical single-edge
deletion with wrap inherited) — is mathematically consistent with, but strictly
*different from*, anything stated in the paper's main text: the paper never
states the removal-monotonicity claim; the closest main-text statement is the
addition law `β(G+e) ∈ {β(G)−1, β(G)}` of Example 7.4, which is not the same
proposition. See Discrepancies, item 1.

---

## T5. `mobius_charpoly_roots_eq_union`

**Source:** `ConnectionLaplacian/L16_SpectrumUnion.lean:109-112`.
**Section context** (lines 39-46): `namespace ConnectionLaplacian`;
`open Matrix BigOperators`; `open Polynomial (C)`; `namespace ConnGraph`;
`variable (G : ConnGraph)`.

```lean
import ConnectionLaplacian

namespace ConnectionLaplacian.ConnGraph

open Matrix BigOperators
open Polynomial (C)

theorem mobius_charpoly_roots_eq_union' (G : ConnGraph) :
    (G.laplacian true).charpoly.roots =
      G.scalarLaplacian.charpoly.roots +
        G.signedLaplacianMobius.charpoly.roots :=
  G.mobius_charpoly_roots_eq_union

end ConnGraph
```

**Paper counterpart:** Remark 5.6 `rem:direct-bundle-charpoly`
(`paper/paper.tex:1155-1173`), "Direct-bundle factorisation" (the appendix
index, `paper.tex:1484-1485`, maps its "spec union" clause to this theorem):

```latex
\begin{remark}[Direct-bundle factorisation]\label{rem:direct-bundle-charpoly}
Composing Theorem~\ref{thm:cover-charpoly} with the similarity of
Theorem~\ref{thm:decomp} gives the same factorisation directly for
$L_{\mathrm{Mob}}$ without invoking the cover:
\[
  \det\bigl(\lambda\,\II - L_{\mathrm{Mob}}(G)\bigr)
  \;=\;
  \det\bigl(\lambda\,\II - \Lscalar(G)\bigr)\cdot
  \det\bigl(\lambda\,\II - \Lsigned(G)\bigr),
\]
and for every $\alpha\in\RR$,
$\det(L_{\mathrm{Mob}}+\alpha\II)=\det(\Lscalar+\alpha\II)\cdot
\det(\Lsigned+\alpha\II)$. As multisets,
$\operatorname{Spec}(L_{\mathrm{Mob}}) = \operatorname{Spec}(\Lscalar)
\uplus \operatorname{Spec}(\Lsigned)$. These are Lean theorems
\texttt{mobius\_charpoly\_eq\_scalar\_times\_signed},
\texttt{shiftedDet\_factorises} and
\texttt{mobius\_charpoly\_roots\_eq\_union}.
\end{remark}
```

**Judgement:** The Lean statement is the multiset ("spec union") clause of the
remark: by `mobius_charpoly_eq_scalar_times_signed` (the remark's first display)
and `Polynomial.roots_mul`, the multiset of charpoly roots of `L_Mob` equals the
multiset **sum** (`+` on `Multiset ℝ`, i.e. `⊎`) of the root multisets of
`L^sc` and `L^sg`, with multiplicity — the same mathematical claim as
`Spec(L_Mob) = Spec(L^sc) ⊎ Spec(L^sg)` for every connection graph, no
connectedness hypothesis, matching the paper. One convention caveat:
`Polynomial.roots` collects roots **in ℝ**, whereas the paper's `Spec` is over ℂ
(§2.3 regards the matrices as acting on ℂ^V); the two readings coincide here
only because the matrices are real symmetric, so all charpoly roots are real —
see Discrepancies, item 3.

---

## T6. `frobenius_laplacian_decomposes`

**Source:** `ConnectionLaplacian/L17_TracesAndLipschitz.lean:181-184`.
**Section context** (lines 30-36): `namespace ConnectionLaplacian`;
`open Matrix BigOperators`; `namespace ConnGraph`;
`variable (G : ConnGraph)`. (No `open Polynomial`.)

```lean
import ConnectionLaplacian

namespace ConnectionLaplacian.ConnGraph

open Matrix BigOperators

theorem frobenius_laplacian_decomposes' (G : ConnGraph) :
    ((G.laplacian true)ᵀ * (G.laplacian true)).trace
      = (G.scalarLaplacianᵀ * G.scalarLaplacian).trace +
        (G.signedLaplacianMobiusᵀ * G.signedLaplacianMobius).trace :=
  G.frobenius_laplacian_decomposes

end ConnGraph
```

**Paper counterpart:** Proposition 5.2 `prop:traces2`
(`paper/paper.tex:1037-1055`), "Quadratic trace and Frobenius identities"
(Frobenius line; the proof, `paper.tex:1066-1069`, names
`frobenius_laplacian_decomposes` explicitly):

```latex
\begin{proposition}[Quadratic trace and Frobenius
identities]\label{prop:traces2}
For every connection graph $G=(V,E,W)$,
\begin{align*}
  \tr\bigl(L_{\mathrm{Mob}}(G)^2\bigr)
  \;&=\; \tr\bigl(\Lscalar(G)^2\bigr)
       + \tr\bigl(\Lsigned(G)^2\bigr), \\
  \|L_{\mathrm{Mob}}(G)\|_F^2
  \;&=\; \|\Lscalar(G)\|_F^2 + \|\Lsigned(G)\|_F^2,
\end{align*}
and the cross term obeys the polarisation identity
\[
  2\,\tr\!\bigl(\Lscalar(G)\cdot\Lsigned(G)\bigr)
  \;=\;
  \tr\!\bigl((\Lscalar(G){+}\Lsigned(G))^2\bigr)
  - \tr\!\bigl(\Lscalar(G)^2\bigr)
  - \tr\!\bigl(\Lsigned(G)^2\bigr).
\]
\end{proposition}
```

**Judgement:** Same claim: the Lean statement is the Frobenius line with the norm
written in its defining trace form (`‖M‖²_F = tr(Mᵀ·M)`; the Lean proof reduces
to `trace_sq_laplacian_decomposes` via symmetry of the three matrices, exactly as
the paper's proof sketch says); the quantifier ("for every connection graph",
no connectedness hypothesis) and field (ℝ) match. No discrepancy beyond the
definitional unfolding of `‖·‖²_F`.

---

## T7. `trace_mul_scalar_signed_eq`

**Source:** `ConnectionLaplacian/L17_TracesAndLipschitz.lean:203-208`.
**Section context:** same file as T6 (`namespace ConnectionLaplacian`;
`open Matrix BigOperators`; `namespace ConnGraph`;
`variable (G : ConnGraph)`).

```lean
import ConnectionLaplacian

namespace ConnectionLaplacian.ConnGraph

open Matrix BigOperators

theorem trace_mul_scalar_signed_eq' (G : ConnGraph) :
    2 * (G.scalarLaplacian * G.signedLaplacianMobius).trace
      = ((G.scalarLaplacian + G.signedLaplacianMobius) *
           (G.scalarLaplacian + G.signedLaplacianMobius)).trace
        - (G.scalarLaplacian * G.scalarLaplacian).trace
        - (G.signedLaplacianMobius * G.signedLaplacianMobius).trace :=
  G.trace_mul_scalar_signed_eq

end ConnGraph
```

**Paper counterpart:** Proposition 5.2 `prop:traces2`, polarisation display
(`paper/paper.tex:1047-1054`; the proof names `trace_mul_scalar_signed_eq` at
`paper.tex:1069`):

```latex
and the cross term obeys the polarisation identity
\[
  2\,\tr\!\bigl(\Lscalar(G)\cdot\Lsigned(G)\bigr)
  \;=\;
  \tr\!\bigl((\Lscalar(G){+}\Lsigned(G))^2\bigr)
  - \tr\!\bigl(\Lscalar(G)^2\bigr)
  - \tr\!\bigl(\Lsigned(G)^2\bigr).
\]
```

**Judgement:** Exact match: Lean's `(M * M).trace` unfolds the paper's `M²`, the
two subtraction terms correspond term-by-term, the leading factor `2` matches,
and the claim is hypothesis-free for every connection graph over ℝ, as in the
paper. No discrepancy.

---

## Discrepancies

1. **T4 (bridge monotone) has no main-text paper statement.** The Lean theorem
   `numBalancedComponents_monotone_remove_nonwrap_nonbridge` (`β(G) ≤ β(G−e)`
   for non-wrap, non-bridge `e`) is mapped in the appendix index
   (`paper.tex:1480-1481`) only as the "R5 refinement" of Example
   `ex:cross-merge`, whose actual displayed statement concerns *edge addition*
   (`β(G+e) ∈ {β(G)−1, β(G)}`). The removal-monotonicity claim is never stated
   in the paper body; the transcription is therefore Lean-to-paper *implicit*.
   Additionally, the Lean file itself documents (`L15_BridgeMonotone.lean:18-20`,
   `251-253`) that the `_hnonwrap` hypothesis is **unused** — the theorem holds
   for removal of any non-bridge edge, wrap or not — so the Lean statement is
   formally weaker than what is proved (harmless, but a hypothesis/convention
   mismatch worth recording).
2. **T3 (PSD): the paper asserts more than the Lean statement.** Lemma
   `lem:signed-psd` states PSD *with* the explicit sum-of-squares quadratic-form
   identity; the public Lean statement is `PosSemidef` only. The identity is
   established inside the Lean file (`sLM_quadForm_raw`, `sLM_quadForm_nonneg`)
   but as `private` lemmas, so at the level of transcribable statements the Lean
   claim is strictly the PSD property.
3. **T5 (roots union): ℝ-roots versus ℂ-spectrum convention.** Lean's
   `Polynomial.roots` yields the multiset of roots *in ℝ*; the paper's
   `Spec(·)` is (per §2.3, `paper.tex:278-281`) a spectrum over ℂ. The two agree
   here because all three matrices are real symmetric (hence all eigenvalues
   real), but the Lean statement literally quantifies over real roots and would
   be weaker than the ℂ-spectrum reading for non-symmetric matrices. Relatedly,
   the paper bundles three Lean theorems into one remark (`charpoly product`,
   `shifted det`, `spec union`), of which only the multiset clause is T5.
4. **T1 (cover charpoly): the paper's "Equivalently … Spec ⊎ Spec" clause and
   Corollary `cor:mult-pointwise` (pointwise multiplicity, `paper.tex:1198-1205`)
   have no separately named Lean counterpart for the cover.** The appendix index
   (`paper.tex:1466-1467`) lists Cor. 5.7 only as an unnamed "corollary of
   `cover_charpoly_eq_scalar_times_mobius`". The transcribed Lean theorem itself
   matches the paper's determinant identity exactly; this item records only that
   the corollaries stated in the paper around it are not separately
   formalised for the cover (they are, for `L_Mob`, via T5).
5. **No connectedness assumptions anywhere** in either the seven Lean statements
   or their paper counterparts (all quantified over arbitrary connection
   graphs `G = (V, E, W)`), and no field discrepancies (everything over ℝ;
   the paper's ℂ passage for Fourier diagonalisation does not touch these seven
   results). `charpoly` sign convention `det(X•I − M)` matches the paper's
   `det(λI − ·)` throughout; the wrap-sign convention of `signedLaplacianMobius`
   (+1 wrap / −1 non-wrap off-diagonal) matches the paper's `L^sg` display
   (`paper.tex:254-260`) exactly.
