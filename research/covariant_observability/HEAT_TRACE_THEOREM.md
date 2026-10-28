# Covariant theta heat-trace convergence: a complete spectral-tail argument

**Status (2026-10-28):** P in conventional finite/spectral mathematics, not P-Lean or independent peer review. This development is dev-only and does not modify the HAL/arXiv paper. It *supersedes* the earlier H classification of heat-trace convergence in HEAT_VISIBILITY.md and METRIC_GRAPH_LIMIT.md for this ONE fixed theta-graph family. No general hypercomplex, hyperbolic or hardness implication is asserted.

## Exact theorem

Let \(L_s=D_s^*D_s\) be the unweighted rank-two complex SU(2) connection Laplacian on the theta graph in which each of the original six edges is subdivided into \(s\) edges. Its three pole-to-pole path transports are \(I,A,B\). Let \(H_s=s^2L_s\). Suppose

\[
0<\chi:=3+\operatorname{tr}(A)+\operatorname{tr}(B)+\operatorname{Re}\operatorname{tr}(AB^*)<9,\quad
\alpha=\arccos(\sqrt{\chi}/3)\in(0,\pi/2).
\]

Then for every real \(t>0\),

\[
\boxed{\lim_{s\to\infty}\operatorname{Tr}e^{-tH_s}
=2\sum_{m\in\mathbb Z}\exp[-t((m\pi+\alpha)/2)^2]
+2\sum_{m=1}^\infty\exp[-t(m\pi/2)^2].}\tag{1}
\]

This is the heat trace of the compact metric theta graph with three length-two paths, parallel SU(2) frames, transport \(I,A,B\), continuity of fiber values at each pole, and Kirchhoff sum-of-outgoing-derivatives zero. This trace is over the **whole fiber Hilbert space**, not normalized by the number of graph vertices.

For \(A=\exp(0.8i\sigma_z)\), \(B_0=\exp(i\sigma_z)\) and \(B_1=\exp(i\sigma_x)\), evaluating the analytic series at \(t=3\) gives the exact-model contrast (rounded)
\[
\boxed{\lim_{s\to\infty}\bigl[\operatorname{Tr}e^{-3H_s(B_1)}
-\operatorname{Tr}e^{-3H_s(B_0)}\bigr]\approx-0.191276891614986.}\tag{2}
\]
Previously held-out measurements at \(s=16,24\) were \(-0.193217884\) and \(-0.192573263\), respectively; they were not used to obtain the limit formula.

## Proof 1: root convergence with multiplicities

With \(M=2s\), \(p_{-1}=0\), \(p_0=1\), \(p_j(z)=(2-z)p_{j-1}(z)-p_{j-2}(z)\), and \(h_M(z)=(3-z)p_{M-1}(z)-3p_{M-2}(z)\), direct Schur elimination gives, **for every complex z**,
\[
\det(L_s-zI)=p_{M-1}(z)^2\,[h_M(z)^2-\chi]^2.
\]
See METRIC_GRAPH_LIMIT.md for the full finite derivation. On replacing \(z\) by \(\lambda/s^2\), the normalized determinants converge *locally uniformly as entire functions* to
\[
F_\chi(\lambda)=
\left[\frac{\sin(2\sqrt\lambda)}{\sqrt\lambda}\right]^2
[9\cos^2(2\sqrt\lambda)-\chi]^2.
\]
The square-root at zero is removable by the power series. For \(0<\chi<9\), its nonnegative zeros are distinct between families and have complex multiplicity two:
\[
(\alpha/2)^2;\quad
((m\pi-\alpha)/2)^2,\quad((m\pi+\alpha)/2)^2,\quad(m\pi/2)^2\quad(m\ge1).
\]
The argument principle / Rouché theorem on small nonintersecting zero contours proves convergence of every fixed ordered eigenvalue of \(H_s\) to the corresponding root, **with multiplicities**, and no additional bounded-energy eigenvalues. Positivity follows from the Gram form.

The specified metric graph has the same spectral list: away from Dirichlet frequencies, solve the edge ODE \(-f''=\lambda f\), impose Kirchhoff conditions at the two poles, and obtain the 4x4 boundary determinant \([9\cos^2(2\sqrt\lambda)-\chi]^2\). At \(\sqrt\lambda=m\pi/2\), the six path fiber amplitudes satisfy four independent Kirchhoff constraints when \(\chi<9\), leaving multiplicity two. This identifies the limit operator rather than merely naming roots.

## Proof 2: high-frequency tail, independent of the holonomy angles

The graph has \(N_s=12s-2\) complex fiber coordinates. Delete the **four** coordinates of the two rank-two pole fibers from \(H_s\). The resulting principal submatrix is, after independent unitary gauge choices on each interior path, the direct sum of **six** scalar Dirichlet path matrices with \(M-1=2s-1\) interior vertices.

The ordered eigenvalues of that principal submatrix are the numbers
\[
\mu_{j,s}=4s^2\sin^2\bigl(j\pi/(2M)\bigr),
\quad j=1,\ldots,M-1,
\]
each repeated SIX times. Denote the ordered eigenvalues of \(H_s\) by \(\lambda_{1,s},\ldots,\lambda_{N_s,s}\). Cauchy interlacing for a principal submatrix of codimension four implies
\[
\lambda_{i,s}\ge\mu_{i-4,s}^{\mathrm{ordered}}
\quad(i=5,\ldots,N_s).
\]
Since \(\sin x\ge2x/\pi\) on \([0,\pi/2]\) and \(M=2s\), every \(\mu_{j,s}\ge j^2\). Thus
\[
\boxed{\lambda_{i,s}\ge\left\lceil(i-4)/6\right\rceil^2,\qquad i\ge5.}\tag{3}
\]
This bound is **independent of s, A, and B**. In particular for any \(t>0\) and \(K\ge4\),
\[
0\le\sum_{i>K}^{N_s}e^{-t\lambda_{i,s}}
\le\sum_{i>K}e^{-t\lceil(i-4)/6\rceil^2}
\underset{K\to\infty}{\longrightarrow}0
\]
uniformly in \(s\). Combining fixed-index spectral convergence with this *uniform* Gaussian tail establishes (1) by finite-head / small-tail convergence. This closes the missing step previously left as H.

## Scope, tests and limitations

- **P ordinary mathematics:** exact secular determinant, compact-window root convergence, interlacing tail, and full heat-trace limit for this declared theta/Kirchhoff family. Distinguish from unproved independent external acceptance.
- **M bounded numerical witness:** test_metric_graph_limit.py checks direct block-matrix determinants, low-spectrum roots, interlacing inequalities and the independently computed analytic heat series. This is not a Lean proof.
- **H open:** uniform norm-resolvent/quasi-unitary operator convergence for the proposed interpolation \(J_s\); arbitrary graph families; changing fiber ranks; hyperbolic ambient manifolds; nonassociative transport.
- **R:** the earlier classification of heat-trace convergence for this *particular theta graph* as an unsupported asymptotic hypothesis. The previous finite measurements remain M.

The interpolation \(J_s\) is NOT isometric under the uniform vertex mass; the finite-element mass discrepancy at the junctions must be accounted for before any stronger operator-convergence claim. No SAT reduction, complexity bound, or solver advantage follows. The original graph-wide Lean theorem \(D^\mathsf{T}D=G.laplacian\) for the submitted Z/2 model remains unfinished.

This proof is a controlled explicit example within existing metric-graph and quaternion gain-graph spectral theory, not a priority or novelty claim.
