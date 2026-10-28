# Spectral identifiability audit: characteristic polynomials, nulls and literature

**Dev-only research note (2026-10-28).** The following are exact finite-matrix calculations for a specific 5-vertex SU(2) graph connection and are **not** Lean-proved, a new mathematical field, a hyperbolic limit, or a hardness lower bound. We distinguish a mathematical identity (P in ordinary mathematics) from its independent floating-point cross-check (M).

## Algebraic objects

Let \(A,B\in SU(2)\). With \(q=2-z\), \(p=3-z\), \(\tau_A=\operatorname{tr}(A)\), \(\tau_B=\operatorname{tr}(B)\) and \(\tau_{AB}=\operatorname{Re}\operatorname{tr}(AB^\dagger)\), define
\[
\chi=3+\tau_A+\tau_B+\tau_{AB}.
\]
The traces are real for SU(2). For the five-vertex theta graph \(K_{2,3}\), with two pole vertices and three length-two paths bearing transports \(I,A,B\), direct Schur elimination yields

\[
\boxed{\det(L_{\mathrm{theta}}-zI_{10})
=q^2\left[\left(pq-3\right)^2-\chi\right]^2.}
\]

Proof: the three internal degree-two vertices contribute \(qI_6\); the Schur complement on the two degree-three poles is the 4x4 block matrix with diagonal \((p-3/q)I_2\) and off-diagonal \(-(I+A+B)/q\). The SU(2) identity \(C C^\dagger=\chi I_2\), \(C=I+A+B\), follows by expanding and applying \(U+U^\dagger=(\operatorname{tr} U)I_2\). The Schur determinant simplifies to the displayed polynomial. The derivation is initially for \(q\ne0\); polynomial equality extends it to every \(z\).

For the wedge of two triangles sharing a root (degree sequence \(4,2,2,2,2\)), each pair of non-root vertices contributes \(\begin{psmallmatrix}qI&-U\\-U^\dagger&qI\end{psmallmatrix}\), whose determinant is \((q^2-1)^2\). Eliminating both pairs gives

\[
\boxed{\det(L_{\mathrm{wedge}}-zI_{10})
=(q^2-1)^2
\left[(4-z)(q^2-1)-4q-\tau_A-\tau_B\right]^2.}
\]

The wedge polynomial **has no mixed holonomy character** \(\tau_{AB}\); the theta polynomial does. This is a fully algebraic explanation for the matched negative control, not just the numerical observation from eigensolvers. It also makes the topology/degree confound explicit: we compare holonomies **within** each fixed graph, not causal topology effects across different graphs.

Both determinants are perfect squares in the ten-dimensional complex representation. The standard fundamental SU(2) representation is pseudoreal (equivalent to unit quaternions), producing paired eigenvalues; this is not an independent new feature.

[The separate numerical regression](test_spectral_charpoly.py) evaluates these exact polynomials against direct complex matrix determinants for two topologies, four relative holonomy angles, and six spectral parameters per configuration. The polynomial formulas are the mathematical oracle; numerical agreement is not a formal proof.

## Relation to known mathematical work: authority and novelty

This study is **within existing quaternionic/connection gain-graph spectral theory**.

- Belardo, Brunetti, Coble, Reff, Skogman (2022), *Spectra of quaternion unit gain graphs*, Linear Algebra and Its Applications **632**, 15–49, DOI **10.1016/j.laa.2021.09.009**. They already define quaternion-unit graph adjacency, Laplacian and incidence matrices and develop their spectral properties. Our SU(2) edge transport is equivalent to a unit-quaternion representation; the current experiment does not invent that mathematical setting. Publisher: https://www.sciencedirect.com/science/article/pii/S0024379521003426
- Kyrchei, Treister, Pelykh (2024), *The determinant of the Laplacian matrix of a quaternion unit gain graph*, Discrete Mathematics **347(6)**, 113955, DOI **10.1016/j.disc.2024.113955**. Existing noncommutative determinant theory must be distinguished from our ordinary complex determinant of an explicit 2x2 SU(2) matrix representation. Publisher: https://www.sciencedirect.com/science/article/abs/pii/S0012365X24000864
- Fabila-Carrasco, Lledó, Post (2023), *A geometric construction of isospectral magnetic graphs*, Analysis and Mathematical Physics **13**, article 64, DOI **10.1007/s13324-023-00823-9**. Distinct isospectral magnetic graph constructions are established; our wedge example is an illustrative controlled instance, not an assertion of first-ever isospectral holonomy. https://link.springer.com/article/10.1007/s13324-023-00823-9
- Zhou and Lu (2023), *Relation between the row left rank of a quaternion unit gain graph and the rank of its underlying graph*, Electronic Journal of Linear Algebra **39**, DOI **10.13001/ela.2023.7681**. Existing rank/cycle-space questions are directly adjacent to our proposed visibility-depth field. https://journals.uwyo.edu/index.php/ela/article/view/7681

**Important caveat:** quaternionic *left* and *right* spectral theories require careful typing. The squared complex characteristic polynomials here concern the standard complex representation. They must not be silently equated with an arbitrary quaternionic determinant or spectrum convention.

## Connection to the Manifold hardness studies

The constructed observable \(k_*(s)=4s\) is the **minimal order of a trace moment** detecting changes in the mixed cycle holonomy for this graph sequence. It is not an algorithmic time, complexity exponent, SAT proof depth, or universal invariant of all equivalent observational instruments.

A fixed-degree polynomial in \(L\) cannot distinguish the matched cases after sufficiently fine edge subdivision. A direct Wilson-loop or matrix-holonomy instrument can distinguish them without probing the Laplacian moments, so **the visibility depth is observer-relative**. In particular, it is not a fundamental information-theoretic lower bound and cannot be promoted into one by increasing dimension.

This last distinction is load-bearing: in our hardness programme a proposed non-scalar residual collapsed under matched controls. Here the mathematically discriminating object is the *mixed closed-walk character*, not the presence of noncommutativity as such.

## Bounded next step

Before asserting any hyperbolic, large-dimensional, or hypercomplex generalization:

1. Close the original finite graph \(\mathbb Z/2\) bridge \(D^\mathsf{T}D=L\) in Lean, including disconnected graphs and isolates.
2. On the new experimental track, replace ad hoc scalar endpoint reports by a **typed tuple**: based Wilson character traces, cycle/rank data, spectral moments and heat traces, gauge-covariant section dimensions, and explicit comparison maps under subdivision.
3. Verify each claimed comparison with fixed topology and degree sequence, same fiber rank, same budget, gauge invariance, and commuting as well as noncommuting matched controls.
4. Only then test whether any useful *new* non-scalar observable survives degree/density/size-matched nulls. Kill claims of nonabelian advantage if a commuting construction has equal information at equal cost.

All of this is post-submission on \`dev\`. No modification to the HAL/arXiv manuscript or \`main\` is implied.
