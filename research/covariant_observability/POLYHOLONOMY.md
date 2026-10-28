# Polyholonomy audit: the spectrum can see a loop interaction, or miss it completely

**2026-10-28, post-submission dev experiment.** Not in the HAL paper, not a new Lean theorem, and no claim of novelty. Evidence: P for the algebra below (ordinary finite matrix mathematics), M for bounded NumPy checks, H for scaling and general geometric extrapolations. Source checkpoint: dev a120043 (the preceding green CI baseline).

## Question and frozen controls

A one-cycle scalar Fourier calculation cannot decide whether a Laplacian on a multi-cycle graph recognizes **relative nonabelian holonomy**. We test two genuinely different cycle-interaction geometries, each with two independent cycles, against a commuting baseline with the same local individual holonomy eigenvalues.

Let X and Z be the 2x2 Pauli matrices. For fixed a=0.8, b=1.0 (radians) define

\[
A=e^{iaZ}=\cos(a)I+i\sin(a)Z,\qquad
B_t=e^{ib(\cos t\,Z+\sin t\,X)}.
\]

All matrices belong to SU(2). The conjugacy-class traces tr(A)=2cos(a) and tr(B_t)=2cos(b) do not change with t. Their commutator vanishes at t=0 and is nonzero at t>0. The mixed Wilson trace is

\[
w_t=\operatorname{tr}(A B_t^\dagger)
=2[\cos(a)\cos(b)+\sin(a)\sin(b)\cos(t)].
\]

This is invariant under **simultaneous conjugation** of the two based fundamental-cycle holonomies. It is not a claim that each edge-matrix commutator is gauge invariant.

The tested unweighted graph models have identical fiber rank (complex 2), unitary transports, edge weights and two-dimensional cycle spaces (first Betti number 2). Within each topology, commuting and noncommuting cases have **identical underlying graphs and compute size**. The two topologies each have 5 vertices and 6 edges before subdivision, but **different degree sequences**: wedge=(4,2,2,2,2), theta=(3,3,2,2,2). Comparisons between topologies are therefore *not* degree-controlled causal claims.

For each graph set L=D*D, with vertex inner product the sum of usual Hermitian fiber products. No hyperbolic manifold, nonassociative algebra, evolving fiber rank, or computational hardness phenomenon is implemented here.

## A. Wedge of two triangles: a genuine negative control

The graph consists of triangles (0,1,2) and (0,3,4), sharing only vertex 0. Choose identity transport on the four spokes and A,B_t on the two closing edges (1,2),(3,4).

**P (exact spectral invisibility):** all eigenvalues of the 10x10 Laplacian are independent of the relative axis t, although the two holonomies do not commute for t>0.

Proof. Set q=2-z, with spectral parameter z. Eliminating the two non-root vertices of a triangle yields the 4x4 block

\[
K_U(z)=\begin{pmatrix}qI&-U\\-U^\dagger&qI\end{pmatrix},
\quad
K_U(z)^{-1}=
\frac1{q^2-1}\begin{pmatrix}qI&U\\U^\dagger&qI\end{pmatrix}.
\]

At the common root its Schur contribution is

\[
[I\ I]K_U(z)^{-1}[I\ I]^T
=\frac{2q I+U+U^\dagger}{q^2-1}.
\]

For every SU(2) matrix U, Cayley-Hamilton gives U+U†=(tr U)I. Thus the root Schur complement depends on A and B_t only through tr(A) and tr(B_t), both fixed. Also det(K_U)=(q²-1)² does not depend on U. The resulting characteristic polynomial, initially calculated away from q=±1, agrees identically everywhere by polynomial continuation. Hence the full spectrum is independent of t.

This does **not** mean the connections are gauge-equivalent; their based holonomy commutators are different. It means that this spectral observable discards the distinction.

## B. Theta graph K(2,3): mixed holonomy is spectrally visible

Take poles 0 and 1 with three paths 0-2-1, 0-3-1, 0-4-1. Put I on the first path and A,B_t on the edges (1,3),(1,4), respectively. Individual fundamental-cycle holonomies are A and B_t; the third simple 4-cycle carries the mixed transport AB_t† (up to conjugation and path reversal).

Eliminating vertices 2,3,4 leads to a 4x4 Schur complement on poles with off-diagonal factor proportional to C_t=I+A+B_t. For SU(2),

\[
C_t C_t^\dagger
=[3+\operatorname{tr}(A)+\operatorname{tr}(B_t)
+\operatorname{tr}(AB_t^\dagger)]I.
\]

Consequently the spectrum depends on the mixed trace w_t even though the two individual holonomy spectra remain fixed.

**P (exact fourth-moment discriminator):** for the base K(2,3), with any two settings t and t0 keeping the individual conjugacy classes fixed,

\[
\boxed{\operatorname{tr}(L_t^4)-\operatorname{tr}(L_{t_0}^4)
=8\,[\operatorname{Re}\operatorname{tr}(AB_t^\dagger)
-\operatorname{Re}\operatorname{tr}(AB_{t_0}^\dagger)].}
\]

Reason: in the expansion of tr(L^4), degree and shorter/retracing walks do not depend on the relative axis. The mixed simple 4-cycle supplies four starting vertices times two orientations, giving coefficient 8. This is checked against the Schur-complement algebra and the direct block calculation. The first three trace moments remain fixed. No claim is made here that the entire spectrum uniquely reconstructs the underlying connection.

### A matched commuting-only falsifier

The theta spectral response **does not demonstrate that noncommutativity is necessary**. Fix A as above and replace B by either B_+=exp(ibZ) or B_-=exp(-ibZ). Both A/B pairs commute and have **exactly the same individual A and B eigenvalues**, but

\[
\operatorname{tr}(AB_+^\dagger)=2\cos(a-b),\qquad
\operatorname{tr}(AB_-^\dagger)=2\cos(a+b).
\]

The two commuting connections on the base theta graph have a numerical maximum eigenvalue displacement of approximately 0.281275 and a fourth-moment contrast of -19.316299. The wedge spectra remain identical to roundoff. The same moment formula in the previous section predicts the contrast exactly.

This is a decisive matched-null correction: *the mixed Wilson character*, not noncommutativity by itself, is the discriminating spectral quantity here. Noncommutativity is **neither necessary** (the commuting-only counterexample) **nor sufficient** (the noncommuting wedge counterexample) for a spectral change between otherwise matched members of these families. Do not infer a special hypercomplex advantage from these plots.

## C. Bounded numerical checks

Instrument: numpy==2.3.5, fixed seed 20261028, direct block degree-minus-adjacency construction, separate incidence-factorization check, Hermitian eigensolver, random U(2) vertex gauges and vertex relabelings.

- Relative-axis angles: t=0, pi/6, pi/3, pi/2.
- Equal edge subdivisions s=1,2,3 for both topologies. At scale s, |V|=6s-1 and |E|=6s.
- Total 24 topology/subdivision/angle cases, with 48 random gauge checks and 48 relabeling checks.
- Kill if wedge eigenvalues change by >=1e-10, theta n=5 fourth-moment identity fails by >=1e-8, theta s=1,2,3 end-angle spectra differ from commuting by <=0.01, or any gauge/relabel/invariance identity fails by >=1e-10.
- Two negative controls: the commuting t=0 case; and the noncommuting wedge case, whose spectrum remains flat in t.

At s=1 (5 vertices), the theta spectral gap changes from approx 0.055299 to 0.103049 between t=0 and pi/2; maximum eigenvalue displacement is ~0.145204. The wedge gap stays ~0.107852 across the same angles, with maximal eigenvalue change at numerical roundoff (~4.4e-15 over all three sizes). A nonzero commutator norm is thus **not sufficient** to produce a spectral signature.

At s=3 (17 vertices), theta gaps are approximately 0.005442 and 0.010176, respectively. Rescaling by s² suggests a stable finite-size contrast, but **no continuum or hyperbolic limit is proved** and the three sizes cannot establish an asymptotic exponent.

The checked results depend on a designed example and correlated model/test construction. They are not independent external replication or evidence of practical solver benefit.

Run:

    python research/covariant_observability/test_polyholonomy.py

## D. Spectral visibility depth under edge refinement

Let s>=1, replace **every** edge of the theta graph by a chain of s unit-weight edges, with the same net transport along the chain. This produces |V|=6s-1, |E|=6s, and girth 4s. Keep the individual holonomy conjugacy classes fixed and change only the relative axis t.

**P (ordinary finite walk-counting argument):** for the matched configurations,

\[
\operatorname{tr}(L_{s,t}^{k})=
\operatorname{tr}(L_{s,0}^{k})\quad(0\le k<4s),
\]

whereas the first distinguishing moment obeys

\[
\boxed{\operatorname{tr}(L_{s,t}^{4s})-
\operatorname{tr}(L_{s,0}^{4s})
=8s\,[\operatorname{tr}(AB_t^\dagger)-\operatorname{tr}(AB_0^\dagger)].}
\]

**Proof sketch with exact combinatorial content:** Expand tr(L^k) as closed vertex walks with diagonal stays carrying the vertex degree and off-diagonal steps carrying minus the edge transport. For k<4s a closed walk has no nonbacktracking cycle: after canceling immediate reversals, all transports are the identity. Thus its trace is independent of holonomy. At k=4s the three elementary simple cycles become available. Two have individual holonomy A or B (whose traces are unchanged), and the third has AB†. For this third cycle there are 4s choices of base point and two directions; the resulting 8s oriented terms contribute 8s Re tr(AB†) because traces of SU(2) matrices are real. No diagonal stay or backtracking detour fits at that order. Subtracting the matched configurations leaves the displayed formula.

The nonzero signal is deliberately **not** uniform in a fixed observation order k: for every fixed integer k, all sufficiently fine subdivisions (4s>k) are invisible to that spectral-moment probe. A larger-order observer can recover the mixed-cycle signal. This is a concrete mathematical analogue of the **visibility-depth** discipline from the corrected hardness studies, but is not a SAT reduction, information-theoretic hardness theorem, or complexity lower bound.

Instrument: [test_visibility_depth.py](test_visibility_depth.py) tests s=1,2,3 and relative angles pi/3,pi/2. The first contrasting orders are 4,8,12; the closed-walk formula is checked numerically with absolute tolerance 1e-5 because high matrix powers entail cancellation. A sixth-order observer distinguishes the s=1 graph but not s=2 or s=3. No claim about continuous, rescaled, hyperbolic, hypercomplex, or renormalization limits is made.

## Interpretation and relation to the hardness studies

- **P:** scalar-cycle Riesz formulas remain correct within their specified fixed-fiber, fixed-topology family. They cannot be promoted to a general no-go theorem for richer bundle geometries.
- **P:** the original I/sigma-X transports of the submitted real two-fiber paper all commute; noncommuting based holonomy is not represented by that original model.
- **P:** noncommuting holonomies can be spectrally invisible on the wedge and visible through a mixed trace on the theta graph.
- **M:** deterministic finite-size tests confirm these statements under the declared numerical instrument.
- **H:** identify which observable families, comparison maps and graph geometries retain nonabelian information under a meaningful scaling or limit.
- **S:** the polycosmic/Worldlet interpretation is a design lens, not a theorem or performance claim.
- **R (interpretation):** retire both implications that noncommutativity is sufficient or necessary for spectral variation. The mixed-cycle holonomy character and accessible closed walks are the load-bearing quantities in this finite example. The commuting-only test is a matched falsifier, not an auxiliary illustration.

This is consonant with the corrected Manifold hardness studies: ambient graph structure, degree and representation can dominate apparent geometric signals. No SAT-to-bundle reduction or complexity implication is supplied here. Do not extrapolate from spectral sensitivity to solver advantage.

## World comparison / attribution

This study is a controlled computational teaching example in established mathematics, *not* a claim to invent nonabelian gauge theory or spectral trace methods. Related literature includes:

- Burago, Ivanov, Kurylev & Lu, *Approximations of the connection Laplacian spectra*, Math. Z. (2022): https://link.springer.com/article/10.1007/s00209-022-03016-5
- Lin, Wan & Zhang, *Connection Laplacian on discrete tori with converging property*, J. Functional Analysis (2025): https://www.sciencedirect.com/science/article/pii/S0022123625001661
- *Discrete Bakry-Émery curvature tensors and matrices of connection graphs*, Advances in Applied Mathematics (2026): https://www.sciencedirect.com/science/article/abs/pii/S0196885826000655
- Faraji et al., *Foundations of Wilson Lines and Loops From Basic Concepts to Gauge Field Reconstruction* (2026): https://onlinelibrary.wiley.com/doi/10.1002/prop.70156

The next proof bridge is still the **global** graph identity D*D=L for the paper's actual Z/2 model, including isolates. The SU(2) test is an independent expansion of the observability programme, not a retroactive change to that theorem or to the HAL submission.

- Fabila-Carrasco, Lledó and Post, *A geometric construction of isospectral magnetic graphs* (2023): https://link.springer.com/article/10.1007/s13324-023-00823-9 (context for prior isospectral examples; not our construction)
