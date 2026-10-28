# Covariant observability on finite unitary graph bundles

**Branch:** dev only. **Date:** 2026-10-28. **Status:** mathematical identities plus reproducible numerical checks; **not part of the submitted HAL manuscript** or the existing Lean proof spine. The v0.0.6 paper, tags, and main-branch theorems are not amended by this project.

**Motivation:** Terence Tao, [247A, Notes 3: Singular integral operators](https://terrytao.wordpress.com/2026/10/27/247a-notes-3-singular-integral-operators/) (2026-10-27), especially the Hilbert transform, vector-valued Calderon-Zygmund operators, and Littlewood-Paley square functions. Tao's Euclidean estimates are **not** claimed to extend automatically to finite graph families.

## 1. The model and its scope

Let \(G=(V,E)\) be a finite **connected** simple graph, orient its edges arbitrarily, and choose a fixed complex fiber \(\mathbb C^r\). Each edge \(e=(u,v)\) carries \(U_e\in U(r)\), transporting the fiber at \(v\) to the fiber at \(u\). Define

\[
(D_U f)_e=f_u-U_e f_v,\qquad L_U=D_U^*D_U.
\]

The vertex inner product is the unweighted sum of standard Hermitian fiber inner products; the edge inner product is similarly unweighted. The finite Hermitian matrix \(L_U\) is positive semidefinite by construction. For the manuscript's special \(\mathbb Z/2\) connection, \(r=2\) and \(U_e\) is either \(I_2\) or \(\sigma_x\). The identity of this construction with the existing Lean block-matrix definition is a **next formal bridge**, not a newly proved Lean statement here.

All statements below are classical finite-dimensional deductions, not claims of original singular-integral theorems.

## 2. Exact identities (P in ordinary mathematics; Lean formalization pending)

### A. Parallel sections and cycle holonomy

Because \(\langle f,L_Uf\rangle=\|D_U f\|_2^2\),

\[
\ker L_U=\ker D_U.
\]

Choose a spanning tree, a root \(o\), and unitary transport \(T_v:\mathbb C^r_o\to\mathbb C^r_v\) along the unique tree path, with \(T_o=I\). A parallel section must have \(f_v=T_v x\). For each non-tree edge \((u,v)\), define its fundamental-cycle holonomy in the root fiber by \(H_e=T_u^*U_eT_v\). The remaining equation becomes \(H_e x=x\), hence

\[
\dim\ker L_U=\dim\bigcap_{e\notin T}\ker(H_e-I_r).
\]

**Important correction control:** a tree with one marked \(\sigma_x\) edge has *no cycle holonomy* and still has two parallel modes; a one-wrap triangle has exactly one. Raw wrap-edge count per connected component does not determine balance. This matches the correction history in KernelDimension.lean and L8_Recognition.lean.

### B. Covariant Riesz partial isometry

Let \(P_0\) project orthogonally onto \(\ker L_U\). With spectral decomposition \(L_U=\sum_{\lambda\ge0}\lambda P_\lambda\), define

\[
S_U=L_U^{\dagger 1/2}:=\sum_{\lambda>0}\lambda^{-1/2}P_\lambda,\qquad
R_U=D_US_U.
\]

The notation denotes the square root of the Moore-Penrose pseudoinverse, *not* a power of the zero eigenvalue. Then

\[
R_U^*R_U
=S_U L_U S_U
=\sum_{\lambda>0}P_\lambda=I-P_0.
\]

Therefore \(\|R_Uf\|_2^2=\|(I-P_0)f\|_2^2\). It is an isometry on the orthogonal complement of parallel sections, and annihilates the kernel. The identity is exact at every finite size, irrespective of the smallest nonzero eigenvalue.

### C. Spectral Littlewood-Paley identity

For finite real-valued filters \(\psi_j\) with \(\psi_j(0)=0\) and \(\sum_j|\psi_j(\lambda)|^2=1\) on the *positive* spectrum, define \(F_j=\psi_j(L_U)\). Orthogonal spectral calculus gives

\[
P_0+\sum_jF_j^*F_j=I,\quad
\|f\|_2^2=\|P_0f\|_2^2+\sum_j\|F_jf\|_2^2.
\]

Since our filters are real, also \(f=P_0f+\sum_jF_j^2f\). For genuinely complex filters the reconstruction must use \(F_j^*F_j\), **not** \(F_j^2\). The implementation uses normalized finite Gaussian windows in \(\log_2\lambda\), not a transferred Euclidean Calderon-Zygmund theorem.

### D. Gauge covariance

For vertex gauges \(g_v\in U(r)\), define \(U'_{uv}=g_uU_{uv}g_v^*\), vertex block gauge \(\mathcal G=\bigoplus_v g_v\), and edge gauge \(\mathcal H=\bigoplus_{(u,v)}g_u\). Then

\[
D_{U'}\mathcal G=\mathcal H D_U,\quad
L_{U'}\mathcal G=\mathcal G L_U,\quad
R_{U'}\mathcal G=\mathcal H R_U,\quad
F'_j\mathcal G=\mathcal G F_j.
\]

The root holonomies transform by conjugation with \(g_o\). Their common fixed-space dimension is gauge invariant. The numerical harness checks these identities independently.

## 3. An essential scaling obstruction

For the scalar cycle \(C_n\) with total phase \(0<\theta\le\pi\), the eigenvalues (as a multiset) are

\[
\lambda_k=2-2\cos\left(\frac{2\pi k+\theta}{n}\right),\quad 0\le k<n,
\quad \lambda_{\min}=2-2\cos(\theta/n)\sim\theta^2/n^2.
\]

Consequently \(\|S_U\|_{2\to2}=1/\sqrt{\lambda_{\min}}\sim n/\theta\), while \(\|R_U\|_{2\to2}=1\). **Gap collapse does not by itself imply loss of the Riesz \(L^2\) bound**: the derivative cancels the normalization. In contrast, endpoint \(L^1/L^\infty\) estimates are not implied by the \(L^2\) identity.

For \(\theta=1.2\) and \(n=8,16,32,64,128\), the deterministic rank-one experiment finds a log-log gap slope approximately \(-1.9994\). Its finite \(\ell^\infty\to\ell^\infty\) matrix norms grow from approximately \(2.287\) to \(4.051\), about \(0.441\) per doubling in this range. The numerical trend is **M**, but a stronger **exact mathematical** result is now derived in [TWISTED_ENDPOINT.md](TWISTED_ENDPOINT.md): for every nontrivial rank-one holonomy phase, the endpoint norm is independent of the phase, equals the flat-cycle norm at twice the graph size, and diverges as \((2/\pi)\log n+O(1)\). This is checked for 24 finite configurations in *test_twisted_endpoint.py*. Separately, [ENDPOINT.md](ENDPOINT.md) derives the flat-cycle cotangent kernel, checked by *test_endpoint.py*. Neither statement is yet a Lean theorem or claimed as novel research.

## 4. Pre-registration and negative controls

- **Object:** \(D_U,L_U,P_0,S_U,R_U,\{F_j\}\); first \(\mathbb Z/2\), \(U(1)\), and \(U(2)\) fibers.
- **Prediction:** projector identity, spectral energy identity, gauge covariance and spanning-tree fixed-space dimension agree to floating-point error below \(2\times10^{-8}\) on the declared cases. Twisted cycle gaps follow the exact cosine formula below \(2\times10^{-10}\).
- **Instrument:** NumPy Hermitian eigendecomposition of \(D_U^*D_U\), with cutoff \(10^{-10}\max(1,\lambda_{\max})\); independent fundamental-cycle holonomy constraints via spanning tree and SVD. Roundoff is declared.
- **Controls:** flat rank-two cycle; single-wrap triangle; one-wrap tree (opposite nullity prediction to naive parity); noncommuting rank-two connection; random vertex gauges; same-topology paired flat/generic-\(U(2)\) graphs (sizes \(4,6,8\)); reject nonunitary edge data.
- **Scaling:** \(U(1)\) cycles \(n=8,16,32,64,128\), \(\theta=1.2\). Fixed seed \(20261028\); override supported for independent seeds.
- **Kill conditions:** any failed numerical identity, gauge mismatch, spectral-formula mismatch, or disagreement between holonomy and numerical nullity invalidates the implementation for that run. No proof claim follows from passing tests.
- **Promotion:** retain P only for the written finite-dimensional arguments; M for checked numerical instances; H for any uniform graph-family \(L^p\) estimate and its required geometry assumptions; S for broader Atlas/Riemann metaphors.
- **Scope exclusion:** no claims about P vs NP, the Tenth Discriminant, Riemann zeros, nonassociative fibers, asymptotic quantum advantage, or novel Calderon-Zygmund theory.

Run with a Python environment containing NumPy:

    python research/covariant_observability/experiment.py --verify

JSON output reports every case, errors, endpoint diagnostics, seed and NumPy version. CI uses a dedicated dev-only workflow.

## 5. Next formal bridge, without modifying the submitted paper

1. Prove in Lean that the existing real two-sheet block Laplacian is \(D_U^{\mathsf T}D_U\) for the graph's \(I_2/\sigma_x\) edge transports. Preserve the corrected cycle-balance definition.
2. Define \(\ker D_U\), a projector \(P_0\), and the positive-spectrum inverse square root with Mathlib's actual finite-dimensional spectral API. Prove \(R_U^*R_U=I-P_0\) without introducing a replacement axiom.
3. Formalize a finite family of spectral filters and the squared partition identity. General \(U(r)\) and dimension-uniform bounds belong to later versions, not this foundational proof.
4. Design a *separate* pre-registration for \(1<p<\infty\) bounds on specified graph families with degree, volume-growth, Poincare/heat-kernel assumptions; Tao's Euclidean theorems alone do not imply such bounds.

**Provenance boundary:** This directory is a post-submission research extension. The HAL/arXiv candidate remains the historical, separately verifiable \(\mathbb Z/2\) paper; do not describe the new experiments as having been part of that submission.

## 6. Polyholonomy: a controlled lift beyond the commuting manuscript fibers

[POLYHOLONOMY.md](POLYHOLONOMY.md) records a post-submission experiment on two-cycle graphs with noncommuting complex rank-two SU(2) transports. Individual holonomy eigenvalues are fixed while their relative axis changes. A wedge of two triangles is a **negative control**: the spectrum is unchanged despite noncommuting holonomy. A theta graph is a **positive control**: its mixed-cycle trace enters the fourth Laplacian moment, and its spectrum changes. Both effects have elementary finite-matrix derivations and direct numerical regression in [test_polyholonomy.py](test_polyholonomy.py).

The experimental Lean module [AbelianBoundary.lean](../../ConnectionLaplacian/Experimental/AbelianBoundary.lean) records why the submitted I₂ / σx model cannot encode this noncommutativity: its edge transports commute and share a common symmetric channel. The GitHub Actions axiom audit is the authority for whether those new declarations compile; this document is not a proof substitute.

The controls are matched **within each topology** (graph, fiber rank, individual conjugacy classes and compute dimension). The two different topologies do *not* share the same degree sequence, so differences across them cannot be attributed exclusively to topology without further controls. No general hyperbolic or hypercomplex limit, Riesz bound or complexity advantage follows.
