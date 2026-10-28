# Metric-graph bridge: an exact secular determinant for every theta subdivision

**Scope:** the concrete three-path theta connection, rank-two complex fundamental SU(2) representation, three paths of initial length two, every original edge subdivided into s equal combinatorial segments. **Dev only:** no change to main, HAL or arXiv submission. **Status:** the characteristic-polynomial formula and its compact spectral-parameter limit are proved by finite matrix elimination (P, ordinary mathematics); regression is M; heat-trace convergence for this theta family is now P in ordinary mathematics via an interlacing tail bound (see HEAT_TRACE_THEOREM.md), while stronger norm-resolvent/operator convergence remains H. No Lean theorem is claimed here.

## 1. Exact finite operator and observables

Fix A,B in SU(2), and let each of the three pole-to-pole paths carry respective *net transports* I,A,B. The path has M=2s graph edges and M-1 interior degree-two vertices. Define the unweighted connection Laplacian

\[
L_s=D_s^*D_s\in\operatorname{Herm}(\mathbb C^{2(6s-1)})
\]

by an off-diagonal \(-U_{uv}\) for every edge and its conjugate transpose in the reverse slot, and degrees times I on the diagonal. The scaled operator is \(H_s=s^2L_s\).

Set
\[
\chi=3+\operatorname{tr}A+\operatorname{tr}B+
    \operatorname{Re}\operatorname{tr}(AB^*),\qquad
p_{-1}=0,\quad p_0=1,\quad
p_j(z)=(2-z)p_{j-1}(z)-p_{j-2}(z).
\]
Thus \(p_j(z)=U_j(1-z/2)\), the Chebyshev polynomial of the second kind evaluated at \(1-z/2\). Define
\[
h_M(z)=(3-z)p_{M-1}(z)-3p_{M-2}(z).
\]

**Theorem (exact characteristic polynomial, P):** for every integer s>=1, with M=2s,

\[
\boxed{
\det(L_s-zI_{2(6s-1)}) =
   p_{M-1}(z)^2\bigl(h_M(z)^2-\chi\bigr)^2 .
}
\tag{1}
\]

This is a polynomial identity for *every complex* z. It includes eigenvalues in the high-frequency regime z>4 and all singular values of the interior path block, without numerically dividing by zero.

### Proof by Schur complement

For one path, put its M-1 interior vertices first. The interior scalar tridiagonal block is \(T_{M-1}(z)=\operatorname{tridiag}(-1,2-z,-1)\) with determinant \(p_{M-1}(z)\), so its rank-two fiber version has determinant \(p_{M-1}(z)^2\). Because the paths are independent away from the two poles, the full interior determinant is \(p_{M-1}(z)^6\).

For generic z with \(p_{M-1}(z)\ne0\), the endpoint entries of \(T_{M-1}^{-1}\) are \(p_{M-2}/p_{M-1}\) and \(1/p_{M-1}\). The four-dimensional Schur complement on the pole fibers has diagonal
\[
\left(3-z-3\frac{p_{M-2}}{p_{M-1}}\right)I_2
 = \frac{h_M}{p_{M-1}}I_2
\]
and off-diagonal \(-C/p_{M-1}\), where \(C=I+A+B\) (up to simultaneously conjugating/transposing the net transports, which does not change the determinant). For SU(2),
\[
CC^*=\chi I_2
\]
by the Cayley-Hamilton relation \(U+U^*=(\operatorname{tr}U)I_2\). The Schur determinant is \(p_{M-1}^{-4}(h_M^2-\chi)^2\). Multiplying by the interior determinant gives (1). Both sides are polynomials, so the identity extends to the originally excluded roots \(p_{M-1}=0\).

At M=2 (s=1), (1) reproduces the previously checked five-vertex theta determinant with \(q=2-z\) and \(h_2=(3-z)q-3\). The formula is NOT an unsupported extrapolation from that one example.

## 2. Precisely identified candidate continuum geometry

The candidate limit is a **compact metric theta graph** \(\Gamma\) with two poles and **three intervals of length 2**, each carrying a complex rank-two Hermitian fiber. On each interval choose a parallel trivialization. The connection is flat along its interior and is recorded in a unitary transport (I,A,B) between the pole frames.

The candidate covariant metric-graph Laplacian is \(-\nabla^2\) on \(\bigoplus_{e=1}^3 L^2((0,2);\mathbb C^2)\), with domain consisting of edge sections in \(H^2\), continuity of endpoint fiber values after the declared parallel transports, and the **sum of outgoing covariant derivatives equal to zero at each pole** (Kirchhoff condition). This is a concrete metric graph, not an arbitrarily curved/hyperbolic space, nonassociative algebra, or Worldlet dynamics.

A candidate comparison \(J_s\) takes a vertex section to piecewise-linear interpolation on every interval in its edge-parallel frame; a step has physical length \(1/s\). In discrete vertex coordinates use \(\langle f,g\rangle_s=s^{-1}\sum_{v}\langle f_v,g_v\rangle\), so its associated energy is exactly
\[
\mathcal E_s(f)=s\sum_{\{u,v\}}\|f_u-U_{uv}f_v\|^2,\quad
\frac{\mathcal E_s(f)}{\|f\|_s^2}
  =\frac{\langle f,s^2L_s f\rangle_s}{\|f\|_s^2}.
\]
The interpolation matches the *energy* exactly: \(\int_\Gamma|\nabla J_sf|^2=\mathcal E_s(f)\). Its \(L^2\) norm and the uniform discrete vertex norm are **not equal**: correct lumped-mass junction weights would be \(\deg(v)/(2s)\), and piecewise-linear consistent mass has off-diagonal contributions. Any later resolvent/semigroup convergence proof must account for this measure/inner-product remainder, rather than silently calling J_s unitary.

## 3. A compact-parameter spectral limit that can actually be proved

Fix complex \(\lambda\) in a compact set and put \(z=\lambda/s^2\). With \(q_s=\arccos(1-\lambda/(2s^2))\) in an analytic local branch near zero,

\[
\frac{p_{2s-1}(\lambda/s^2)}s
  =\frac{\sin(2s q_s)}{s\sin q_s}
  \longrightarrow\frac{\sin(2\sqrt\lambda)}{\sqrt\lambda}
\]
and
\[
h_{2s}(\lambda/s^2)
=3\cos(2s q_s)+\tan(q_s/2)\sin(2s q_s)
\longrightarrow 3\cos(2\sqrt\lambda).
\]
Each expression is interpreted as an *entire function of \(\lambda\)* via its power series; the apparent square-root singularity at zero is removable. Convergence is locally uniform on compact complex-\(\lambda\) sets.

Consequently **the normalized characteristic determinant has a proved compact limit (P)**:

\[
\boxed{
s^{-2}\det(L_s-\lambda s^{-2}I)\ \longrightarrow\
F_\chi(\lambda)
=\left(\frac{\sin(2\sqrt\lambda)}{\sqrt\lambda}\right)^2
 \left(9\cos^2(2\sqrt\lambda)-\chi\right)^2 .
}
\tag{2}
\]

For \(0<\chi<9\), the zeros on \(\lambda\ge0\) give the candidate covariant metric-graph spectrum. Write
\(\alpha=\arccos(\sqrt\chi/3)\in(0,\pi/2)\). The roots are
\[
\begin{array}{ll}
\lambda=(\alpha/2)^2,&\\
\lambda=((m\pi-\alpha)/2)^2,\quad
\lambda=((m\pi+\alpha)/2)^2,&m=1,2,\ldots,\\
\lambda=(m\pi/2)^2,&m=1,2,\ldots.
\end{array}
\]
For this generic chi regime, each root has complex multiplicity two. The first two families come from \(9\cos^2(2\sqrt\lambda)=\chi\), and the third from \(\sin(2\sqrt\lambda)=0\). There is no root at \(\lambda=0\) when \(\chi<9\).

Local uniform analytic convergence in (2), together with the multiplicity-sensitive root-continuity theorem (Hurwitz/Rouché on small disks around isolated zeros), yields the **bounded-window spectral convergence of the scaled eigenvalues** with multiplicities. It does not on its own control the *full spectral tail* in a trace.

### Superseding heat-trace theorem (P, ordinary mathematics; not Lean)

The earlier H status of the heat-trace limit for this precise theta family is **retired**. [HEAT_TRACE_THEOREM.md](HEAT_TRACE_THEOREM.md) supplies the previously missing uniform high-frequency tail estimate: delete the four pole-fiber coordinates of the scaled Hermitian matrix, apply Cauchy interlacing with six Dirichlet path blocks, and obtain \(\lambda_{i,s}\ge\lceil(i-4)/6\rceil^2\) for \(i\ge5\), uniformly in subdivisions and transports. Combining this summable Gaussian tail with the compact-window eigenvalue convergence already derived above proves full heat-trace convergence for every positive diffusion time. At time 3 the declared SU(2) contrast tends to approximately \(-0.191276891615\).

This **does not** prove norm-resolvent convergence or quasi-unitary equivalence, which remain H. The finite values at \(s=16,24\) remain M and are not the basis of the theorem.


## 4. Independent oracles and strict boundary

Run
\`python research/covariant_observability/test_metric_graph_limit.py\`.
The script constructs \(L_s\) by an independent direct block-adjacency path, compares \(\log\det(L_s-zI)\) with (1) for subdivisions s=1,2,3,4,6, four holonomy axes and six off-spectrum real parameters per setting, and prints candidate continuum low modes from (2) for s=4,8,16,24.

- **P:** (1), (2), compact-window root convergence, and the separate heat-trace theorem with a uniform interlacing tail (see HEAT_TRACE_THEOREM.md).
- **M:** bounded numerical determinant and low-spectrum checks with a pinned NumPy runtime and direct eigensolvers.
- **H:** norm-resolvent or quasi-unitary operator convergence under explicit \(J_s\); any general graph/hyperbolic/hypercomplex extension.
- **R:** interpreting a fixed low-order spectral-moment failure as an absolute information-theoretic obstruction.

A comparison to metric graph literature should be made before any novelty claim. In particular, this is one classical graph discretization in an established spectral family, not a result about SAT hardness or an escape from universal complexity limits.
