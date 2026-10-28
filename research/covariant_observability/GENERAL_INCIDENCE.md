# Global covariant incidence without collapsing the fibers

**Dev-only research note — 28 October 2026.** The mathematical statements here are conventional finite linear algebra (P-math, subject to independent review), not new Lean theorems unless explicitly named below. Tests are M. This does not amend the submitted HAL manuscript or main.

## 1. Exact identity: every finite fiber rank and graph

Let \(G=(V,E)\) be any finite simple graph (isolated vertices and disconnected components allowed), with Hermitian vertex fiber \(\mathbb C^r\) of arbitrary finite rank \(r\ge1\). Each directed adjacency \(u\to v\) carries a unitary transport \(U_{uv}\), satisfying \(U_{vu}=U_{uv}^*=U_{uv}^{-1}\).

Let \(\vec E\) contain **both orientations** of each undirected edge. Define the half-edge incidence
\[
(\mathcal D f)_{u\to v}=\frac{1}{\sqrt2}(f_u-U_{uv}f_v).
\]
This avoids an arbitrary global orientation; \(1/\sqrt2\) compensates for doubling the edges.

**Theorem (P-math, finite arbitrary-rank covariant factorization):**
\[
\boxed{\mathcal D^*\mathcal D=L_U,\qquad
(L_U f)_u=\deg(u)f_u-\sum_{v\sim u}U_{uv}f_v.}\tag{1}
\]

**Proof.** Each outgoing half-edge at vertex \(u\) contributes \(\frac12I_r\) to the diagonal Gram block. Each incoming half-edge contributes \(\frac12 U_{vu}^*U_{vu}=\frac12I_r\). There are \(\deg(u)\) of each, giving \(\deg(u)I_r\), including degree zero. For adjacent distinct \(u,v\), the two directions give \(-\frac12U_{uv}-\frac12U_{vu}^*=-U_{uv}\); for nonneighbors no row contributes. These are precisely the entries of \(L_U\). No commutativity, scalar diagonalization or connectivity assumption is used.

For vertex gauges \(g_u\in U(r)\), write \(U'_{uv}=g_uU_{uv}g_v^*\), \(G_V=\bigoplus_v g_v\), and \(G_{\vec E}=\bigoplus_{u\to v}g_u\). Then
\[
\boxed{\mathcal D'G_V=G_{\vec E}\mathcal D,\qquad L_{U'}=G_VL_UG_V^*.}\tag{2}
\]
Thus the spectrum is gauge invariant, though the spectrum need not reconstruct holonomy (see the wedge/theta negative controls).

**Lean boundary.** [ArbitraryFiberIncidence.lean](../../ConnectionLaplacian/Experimental/ArbitraryFiberIncidence.lean) defines edge rows of arbitrary real fiber rank and proves their global Gram *assembly*, not (1) for the actual manuscript ConnGraph.laplacian, and not the complex U(r) case. [GlobalEntries.lean](../../ConnectionLaplacian/Experimental/GlobalEntries.lean) already identifies the true manuscript Laplacian's diagonal, edge and nonedge blocks. The missing Lean step is the finite directed adjacency census, half-edge normalization and reverse-transport law. The full theorem (1) is a conventional algebraic result here, **not yet a formal Lean theorem**.

[Independent numerical oracle](test_arbitrary_rank_incidence.py): complex ranks 2, 3 and 4 on graphs with isolates, cycles and arbitrary transports; direct degree-minus-adjacency and oriented-incidence paths built separately, gauge intertwining and an injected omission of reverse directions.

## 2. A different algebraic geometry: split signature

Let the fiber have the nondegenerate **indefinite** real form
\[
Q=\operatorname{diag}(1,1,-1,-1).
\]
A form-preserving transport satisfies \(U^\mathsf T Q U=Q\). Its reverse is \(U^{-1}=Q^{-1}U^\mathsf T Q\), generally **not** \(U^\mathsf T\).

For a shared form in compatible vertex frames, define the **bilinear-form** Laplacian
\[
L_{Q,U}:=\mathcal D^\mathsf T\left(\bigoplus_{u\to v}Q\right)\mathcal D.
\]
The same edge census gives diagonal \((L_{Q,U})_{uu}=\deg(u)Q\) and off-diagonal \((L_{Q,U})_{uv}=-QU_{uv}\) on adjacent vertices. This uses \(U^\mathsf TQU=Q\), not positive-definite orthogonality.

**Crucial distinction:** this symmetric form is generally indefinite. It is not a positive-semidefinite Hilbert Gram; neither the Riesz isometry nor the heat-operator estimates from the positive case carry over automatically. A Krein/Pontryagin Hilbert realization, domain, metric-adjoint and a generalized eigenvalue problem must be specified first.

At the algebraic level, [IndefiniteFiber.lean](../../ConnectionLaplacian/Experimental/IndefiniteFiber.lean) defines form preservation under **ordered composition** and an explicit split (2,2) fiber form. [test_split22.py](test_split22.py) includes noncommuting pseudo-orthogonal boosts, a commuting matched null, proper inverse (rather than Euclidean transpose) gauge transport and a deliberately corrupted-form negative control.

For pseudo-orthogonal vertex gauges \(g_v\), the natural transformation is **congruence**:
\[
L'_{Q,U}=G_V^{-\mathsf T}L_{Q,U}G_V^{-1}.
\]
Ordinary Euclidean eigenvalues of the indefinite bilinear form are therefore not automatically gauge invariants. That would require specifying the correct generalized spectral problem.

## 3. A falsifiable geometric programme

The next object should carry: graph or complex \(X_\lambda\), changing fiber rank, local form \(Q_v\), compatible transports, comparison maps among stages, an admissible adjoint and an explicit family of *observers*. This avoids collapsing a variable geometry into one scalar limit. The proposed symbol \(D^{\dagger_Q}D\) is only meaningful after the indefinite adjoint has a precise definition.

**Kill rule:** when a proposed indefinite/hypercomplex observable is reproduced by a simpler commuting or positive-definite control at equal graph, input information and compute, retire the claimed advantage. Do not rescue a falsified hardness claim by adding a richer ontology.

**Evidence ledger:** P-math — (1), (2) and the finite Q-form block calculation under the stated assumptions; P-Lean — only separately compiled/axiom-audited declarations; M — finite numerical gauges and negative controls; H — the manuscript's global incidence identity in Lean, variable forms, metric/hyperbolic limits and nonassociative transports; R — the idea that scalar-cycle asymptotics or noncommutativity alone resolve the larger geometric question.
