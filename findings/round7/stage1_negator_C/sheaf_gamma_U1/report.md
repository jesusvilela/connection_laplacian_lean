# NEGATOR-C γ (U(1) continuous) — Round 7 Stage 1 Report

## 1. Setup summary

Let `G = (V,E)` be a finite simple graph with a chosen edge orientation. A U(1)-wrap `W : E -> R/Z` assigns a continuous phase; edge reversal negates the phase. The U(1) connection assigns `Phi(e) = exp(2 pi i W(e))` in the forward direction, `exp(-2 pi i W(e))` in reverse. The U(1) connection Laplacian `L_{U(1)}(G,W)` is the |V|x|V| complex Hermitian matrix with `(L)_{vv} = deg(v)`, `(L)_{uv} = -Phi(e)` for `e = u->v`, zero otherwise. Equivalently `L_{U(1)}` is `D^* D` where `(Df)(e) = f(u) - Phi(e) f(v)`. Throughout `comp(G)` is the component count, `b_1(G) = |E| - |V| + comp(G)` is the first Betti number, and `J(G) := Hom(H_1(G; Z), U(1)) = (R/Z)^{b_1}` is the Jacobian torus. A wrap is *flat* iff its holonomy on every cycle is trivial, iff `W = delta f + Z` for some `f : V -> R/Z`; equivalently the class `[W] in J(G)` vanishes on every component.

Relative to the discrete cases (Z/2, Z/k), U(1) is the continuous limit: `Z/k` embeds as `W in (1/k) Z / Z` and the corresponding Hermitian L_chi recovers the Z/k χ_1 fiber. U(1) admits continuous deformation, so spectral functions become continuous on the Jacobian torus — this is where the genuinely new γ claims live.

## 2. Tier-1 claims

**U1-M1 (kernel dichotomy).** For a *connected* graph `G` and any `W : E -> R/Z`, `dim_C ker L_{U(1)}(G,W) in {0, 1}`, and `= 1` iff `[W] = 0 in J(G)` (flat holonomy). For general `G`, `dim_C ker L_{U(1)}(G,W) = #{components C : [W|_C] = 0 in J(C)}`. Contrast Z/k: divisor-indexed `Σ_{d|k} φ(d)·β^(d)`. In U(1) the base ring is `C`, fibres are 1-dimensional per component, no φ(d) multiplicities.

**U1-M2 (gauge invariance through the Jacobian).** The spectrum `Spec(L_{U(1)}(G,W))` depends only on the class `[W] in J(G)`; equivalently, on the holonomy character `chi_W : H_1(G; Z) -> U(1)`. Explicit: the coboundary gauge `W -> W + delta f (mod Z)` for `f : V -> R/Z` conjugates `L_{U(1)}` by the unitary `U_f = diag(e^{2 pi i f(v)})`.

**U1-M3 (flat <=> coboundary).** `L_{U(1)}(G,W)` is unitarily equivalent to the scalar Laplacian `L_{scalar}(G)` iff `W` is a coboundary on every component, iff `[W] = 0 in J(G)`. Flat classes form the identity coset of `J(G)`; the other cosets are non-trivial characters.

**U1-M4 (Rellich analytic spectral flow).** Along any smooth path `t -> W_t` in the edge-space `R^E` (projecting to a loop in `(R/Z)^E`), the |V| eigenvalues of `L_{U(1)}(G, W_t)` admit a real-analytic labelling `lambda_k(t)`. Multiplicities can jump only at isolated crossings. Derivative at a non-degenerate eigenvalue: `d lambda_k / dW(e) = -2 Re(bar{psi_u(k)} · Phi(e) · psi_v(k))`, the Hellmann-Feynman coupling on edge `e`.

**U1-PSD (positive semidefiniteness and trace).** `L_{U(1)}(G,W) succeq 0` for all `W`; `tr(L_{U(1)}) = sum_v deg(v) = 2|E|`, independent of `W`. Proof: `L = D^* D`; trace is sum of unit-modulus-squared = sum of diagonal = 2|E|.

## 3. Tier-2 claims

**U1-rational (Z/k embedding).** For `W in (1/k) Z / Z subset R/Z`, `L_{U(1)}(G,W)` equals (up to unitary) the `chi_1` fiber of the Z/k Möbius Laplacian `L_{Mob,k}(G, k·W)`. All Z/k spectral facts inherit; no new content.

**U1-tree (forests).** On any forest `F`, every U(1)-bundle is trivialisable, so `L_{U(1)}(F, W)` is unitarily equivalent to `L_{scalar}(F)` for all `W`; `Spec(L_{U(1)})` and `dim ker = comp(F)` are `W`-independent. Proof: forests have `b_1 = 0`, so `J(F) = 0`.

**U1-cycle (C_n Bloch).** On `C_n` with holonomy `theta in R/Z` (total wrap around the cycle): `Spec(L_{U(1)}(C_n, W)) = {2 - 2 cos(2 pi (theta + j)/n) : j = 0, ..., n-1}`. Kernel non-trivial iff `theta in Z`, i.e. iff `W` represents the identity of `J(C_n) = R/Z`. Subsumes Z/k-cycle and Z/2-cycle results (rational theta specializations).

**U1-bridge (pure gauge).** Any wrap supported on a bridge (cut-edge) is a coboundary, hence trivial in `J(G)`. Therefore `Spec(L_{U(1)})` is insensitive to wrapping bridges. Relates to the Z/k sheaf via gcd-aware restatement.

**U1-Hellmann-Feynman (non-bridge sensitivity).** For an edge `e` in a cycle and a non-degenerate eigenpair `(lambda_k, psi_k)`, `d lambda_k / dW(e) ≠ 0` generically; the derivative is non-vanishing whenever `psi_k` has non-zero amplitude on both endpoints of `e`. Gives a constructive witness that bridges ARE the only gauge-trivial edges.

**U1-interlacing.** Sorted real spectra satisfy `lambda_k(L_{scalar}(G)) <= lambda_k(L_{U(1)}(G, W))` for all `k` and all `W`, with equality throughout iff `W` is a coboundary. Proof idea: on the Hermitian quadratic form, `<f, L_{scalar} f> <= <f, L_{U(1)} f>` after unitary change of variables uses `|f(u) - Phi(e) f(v)|^2 >= (|f(u)| - |f(v)|)^2`. Expected fragile — prime falsification target (same status as R7-Z3-O1).

**U1-Jacobian torus action.** The map `[W] in J(G) -> Spec(L_{U(1)}(G,W))` is a continuous function from the `b_1`-torus to the space of unordered |V|-tuples of reals; is smooth off a measure-zero crossing locus; and is invariant under the automorphism group of `J(G)` induced by graph automorphisms.

**U1-det-Kirchhoff (twisted matrix-tree).** For any fixed vertex `v_0`: the `(v_0, v_0)` principal minor of `L_{U(1)}(G,W)` equals `sum_{T spanning tree of G} prod_{e in T} |Phi(e)|^2 = tau(G)` (number of spanning trees), *independent of W*, because `|Phi(e)|^2 = 1`. More informatively, non-principal minors detect holonomies: `det(L_{U(1)} - lambda I)` evaluated at `lambda = 0` has a factorisation through characters of `H_1`.

**U1-trace-powers (Gauss-sum formula).** `tr(L_{U(1)}^p) = sum_{closed walks w of length p} prod_{e in w} Phi(e)^{sign_w(e)} = sum_w e^{2 pi i <W, winding(w)>}` with the sum over closed walks and real part extracted for the (real) trace. Generalises Z/k cubic-trace result; continuous extension to U(1).

## 4. Tier-3 observations (continuous-only / genuinely γ)

**U1-IDS (integrated density of states on covers).** On a Z^d-periodic infinite cover `tilde G -> G` with fixed flux per plaquette `phi`, the IDS `N(lambda; phi)` is continuous in `phi`. For rational `phi = p/q`, `N` is piecewise-smooth with gaps of width >= C/q (Gordon-type estimate).

**U1-Bloch-Floquet.** Let `G` be the quotient of a periodic graph `tilde G` by `Z^d`. Bloch-Floquet decomposition gives `L_{U(1)}(tilde G, W) ≅ integral_{T^d} L(k) dk` with fibres `L(k)` finite-dimensional on one fundamental domain, parameterised by Brillouin torus momentum. Flux `phi` shifts fibre momenta. Band functions are real-analytic on `T^d`.

**U1-Harper-Hofstadter.** On the Z^2 square lattice with uniform flux `phi` per plaquette: `Spec(L_{U(1)})` is the Hofstadter butterfly. Specialisations: rational `phi = p/q` gives band spectrum with q bands; irrational `phi` with Diophantine conditions gives Cantor spectrum (Ten Martini). *Finite-graph surrogates* of this live on tori `Z_n x Z_n` — falsifiable on small fuzzer targets.

**U1-random-phase.** For `W` drawn uniformly from `(R/Z)^E`, `Pr[ker L_{U(1)}(G,W) ≠ 0] = 0` on any connected `G` with `b_1 >= 1`. Almost-sure kernel dimension equals the number of components, but for a connected `G` with cycles it is 0.

**U1-tensor (Kronecker-Hadamard non-result).** There is *no* Kronecker-Hadamard decomposition analogous to Z/2. Structurally: the Z/2 case had a real-valued involution `P^2 = I` enabling a Hadamard block-diagonalization; U(1) has continuous parameter, no finite-dimensional eigenbasis decomposition of the connection. This is a deliberate γ non-result — flags that R7 PROVER-C should NOT attempt a blanket Hadamard import from the Z/k sheaf into U(1).

**U1-Cheeger-magnetic.** Magnetic Cheeger constant `h^{mag}(G,W) = min_S (|partial S| - 2 Re(sum_{e in partial S} Phi(e))) / |S|` satisfies `lambda_1(L_{U(1)}) >= h^{mag}(G,W)^2 / (2 deg_max)`. For flat `W`, reduces to the classical Cheeger inequality. Continuous interpolation between flat (`h^{mag} = h_{Cheeger}`) and maximally-frustrated (`h^{mag}` maximised) classes.

**U1-universality-small-n.** For `|V| <= 4`, the map `J(G) -> Spec(L_{U(1)}(G,·))` is completely classified. On `C_3`: spectrum circle parameter `theta in R/Z`, eigenvalues `{2-2cos(2pi(theta+j)/3) : j=0,1,2}`; on `K_4` with `b_1 = 3`, three-torus with explicit band structure derivable from symmetry.

**U1-symmetry-breaking.** At generic `W`, `Spec(L_{U(1)})` has trivial automorphism compared to `Spec(L_{scalar})`: non-trivial W breaks graph symmetries visible on L_scalar. Quantifies the surprise value of finding an accidental degeneracy.

## 5. Dependencies between claims

- `U1-M1` (kernel dichotomy) follows from `U1-M3` (flat <=> coboundary) plus the one-dimensional-kernel fact per connected `L_{scalar}`.
- `U1-M2` (gauge invariance) is foundational: implies spectrum is a function on `J(G)`, underlies `U1-M3, M4, M5, Jacobian-torus, Bloch-Floquet, Harper-Hofstadter`.
- `U1-M4` (Rellich flow) uses analyticity of eigenvalues of Hermitian analytic matrix families.
- `U1-PSD` independent (operator-theoretic); supports reality of `U1-M4`'s labelling.
- `U1-cycle, Hellmann-Feynman, det-Kirchhoff` are concrete instances.
- `U1-interlacing` is fragile (flagged for falsification).
- `U1-tensor` is a non-result, structurally important to flag.
- Tier-3 continuous-only claims (`U1-IDS, Bloch-Floquet, Harper-Hofstadter, Cheeger-magnetic`) require infinite-graph / periodic constructions and are tested against finite-graph surrogates.

## 6. Suggested fuzzer targets for Stage 2 (ranked by surprise value if false)

1. **U1-M1 kernel dichotomy** — 500 random `(G,W)` with `G` connected; kernel must be 0 except on a measure-zero flat locus. Exhaustively check `(1/k) Z / Z` sublattices for `k in {2,3,4,6}`.
2. **U1-M3 flat <=> coboundary** — verify kernel = 1 iff `W - delta f` vanishes for some `f`. Random `(G,W)` + random `f` pairs; null-space characterisation.
3. **U1-M2 gauge invariance** — for random `(G,W,f)`, `Spec(L(G,W))` must equal `Spec(L(G,W+delta f))`. Prime fragility test for holonomy formula.
4. **U1-cycle Bloch** — on `C_n`, `n = 3..10`, random `theta in R/Z`; eigenvalues should match `2-2cos(2pi(theta+j)/n)`.
5. **U1-M4 Hellmann-Feynman derivative** — numerical derivative of `lambda_k(t)` along smooth `W_t` paths; verify against `-2 Re(bar{psi} Phi psi)`.
6. **U1-interlacing** — likely false in some regime; high surprise value for both directions.
7. **U1-trace-powers** — `tr(L_{U(1)}^p)` must be real; match against closed-walk expansion for `p = 2, 3, 4`.
8. **U1-tree flatness** — random trees, random `W`; spectrum must match `L_{scalar}` exactly.
9. **U1-bridge insensitivity** — graphs with distinguished bridges; perturbing `W` only on bridges must leave `Spec` invariant.
10. **U1-tensor non-result** — *anti-fuzz*: construct candidate Kronecker-Hadamard factorisations and verify they all fail; protects PROVER-C from a bad reach.
