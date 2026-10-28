# Operator-sensitive scale: finite heat trace versus fixed-depth moments

**2026-10-28 — experimental, post-HAL-submission; dev branch only.** The main paper is not amended. This note is a bounded numerical scaling test, not a continuum theorem.

## What was found and what is now preregistered

Our theta-graph controls showed that a fixed degree-\(k\) spectral moment cannot observe a mixed holonomy once all path edges are subdivided \(s>k/4\) times, since the shortest mixed Wilson loop has length \(4s\). That is a restriction on the **polynomial-moment observer**, not a universal inability to distinguish connections.

Let \(L_{s,t}\) be the unweighted rank-two Hermitian Laplacian on the \(s\)-subdivided graph, and let \(t=0\) denote a commuting orientation baseline while \(t=\pi/2\) denotes the orthogonal holonomy-axis case. To prevent overloading notation, write \(u>0\) for diffusion time and define

\[
H_s(u,t):=\operatorname{tr}\exp(-u s^2 L_{s,t}),\qquad
\Delta H_s(u):=H_s(u,\pi/2)-H_s(u,0).
\]

The factor \(s^2\) follows the usual diffusive scaling for an edge of effective length \(1/s\). However, **we have not proved metric-graph convergence**, a particular boundary condition at the vertices, convergence of measures, or anything about a hyperbolic ambient geometry. The only implemented operator is the finite graph Laplacian.

### Exploratory sweep, not preregistered evidence of a limit

For \(s=1,2,3,4,6,8,12\), a local dense-eigensolver check at \(u=3\) produced:

- theta: \(\Delta H_s(3)\) around \(-0.22088,-0.20632,-0.20141,-0.19892,-0.19641,-0.19514,-0.19386\);
- wedge: \(\Delta H_s(3)\) zero to floating-point tolerance;
- theta unrescaled heat traces at *fixed physical matrix time* \(3\) lose the spectral difference as paths lengthen.

These samples suggest but do **not** establish a nonzero limiting heat trace contrast.

### Held-out gate (frozen before evaluation)

The independent follow-up uses previously unseen subdivision lengths \(s=16,24\) and the same fixed \(u=3\), two topologies, holonomy conjugacy classes, rank and adjacency weights.

1. **Primary prediction:** theta \(\Delta H_s(3)<-0.15\) for both held-out sizes; wedge \(|\Delta H_s(3)|<10^{-8}\).
2. **Observer contrast:** the theta *unrescaled-time* difference \(|\operatorname{tr}e^{-3L_{s,\pi/2}}-\operatorname{tr}e^{-3L_{s,0}}|\) is below \(10^{-7}\) for both held-out sizes.
3. **Competing control:** a commuting-only pair \(A=e^{0.8iZ}, B_\pm=e^{\pm iZ}\) at \(s=3\) also produces a nonzero theta heat difference; noncommutativity remains neither necessary nor sufficient for a spectral difference.
4. **Kill:** if the held-out theta signal is not detectable at the prescribed threshold, retire the suggested scale persistence rather than altering \(u\) or the threshold. If wedge becomes spectrally different, investigate the implementation and reduce the claim.
5. **Stop/promotion:** at most M for the finite sweep, H for any \(s\to\infty\) heat-trace limit; any theorem requires the limiting operator, appropriate domain and measure, a convergence mode, and control of the spectral tail.

The [test_heat_visibility.py](test_heat_visibility.py) reports full traces and the first rescaled gaps, making the result auditable. Direct dense diagonalization is used; Riesz and Littlewood-Paley operators are not part of this check.

### Relation to hardness visibility

The analogy is narrow: **different computational observers expose different structural information at different resolution scales**. A fixed-degree trace-moment probe is blind for large subdivisions, while the diffusive observer may retain sensitivity after a time rescaling. This mirrors the need to specify the depth \(r\) of a local hardness visibility instrument, but supplies no SAT instance encoding, resolution lower bound, causal solver benefit or new hardness universality class.

### Interpretation and evidence

- **P:** for each finite \(s\), the Hermitian heat trace is gauge invariant, because unitary gauge conjugation commutes with matrix functional calculus. This is established matrix mathematics, not a new Lean formalization.
- **M:** finite numerical contrasts in the declared instrument, including held-out checks if CI passes.
- **H:** a nonzero limiting contrast under diffusive scaling of the chosen graph bundle.
- **S:** a proposed observability tower that admits different spectral filters, local Wilson probes and changing geometries.
- **R:** the idea that fixed low polynomial moment blindness implies loss of all higher-observer information.

A stronger next analysis should compare the scaled trace with the corresponding metric-graph covariant Laplacian and its boundary conditions rather than inferring a continuum object from a logarithmic trend.
