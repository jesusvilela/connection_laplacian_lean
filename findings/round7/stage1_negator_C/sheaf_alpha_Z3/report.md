# NEGATOR-C α (Z/3 pilot) — Round 7 Stage 1 Report

## 1. Setup summary

Let `G = (V,E)` be a finite simple graph with chosen edge orientation. A wrap `W : E -> Z/3` assigns a cyclic label; reversing an edge negates the label. Let `P` be the 3x3 cyclic permutation matrix (`P^3 = I`, eigenvalues `1, omega, omega^2` with `omega = e^{2 pi i/3}`). The connection assigns `Phi(e) = P^{W(e)}` on the forward direction and `P^{-W(e)}` on the reverse. The Möbius-Z/3 Laplacian `L_Mob3` acts on `R^{V x Fin 3}` (size `3|V|`) with diagonal block `deg(v) * I_3` and off-diagonal block `-Phi(e)` on edge `e = (u,v)`. The Z/3 DFT conjugates `L_Mob3` into `diag(L_{chi_0}, L_{chi_1}, L_{chi_2})` with `chi_m(w) = omega^{m w}`. `L_{chi_0} = L_scalar(G)`; `L_{chi_1}, L_{chi_2} = bar{L_{chi_1}}` are complex Hermitian Laplacians on `C^V` with edge weights `chi_m(W(e))`. Throughout `comp(G)` is the component count; `beta^{(3)}(G,W)` is the number of components whose Z/3-holonomy is trivial on every cycle (equivalently, whose restricted bundle is trivialisable).

## 2. Tier-1 claims

**Z3-M1 (kernel dimension).** `dim ker L_Mob3(G,W) = comp(G) + 2 * beta^{(3)}(G,W)`. Rationale: `L_{chi_0}` contributes `comp(G)`; the two non-trivial Galois-conjugate characters each contribute `beta^{(3)}`, hence factor 2. Contrast R6 Z/2: factor 1 because the sole non-trivial character is self-conjugate.

**Z3-M2 (characteristic polynomial factorisation).** `p_{L_Mob3}(x) = p_{L_scalar}(x) * p_{L_{chi_1}}(x) * p_{L_{chi_2}}(x)`, with `p_{L_{chi_2}} = bar{p_{L_{chi_1}}}`, so over `R[x]`: `p_{L_Mob3}(x) = p_{L_scalar}(x) * (p_{L_{chi_1}}(x) * bar{p_{L_{chi_1}}}(x))`. Degrees: `|V| + 2|V| = 3|V|`.

**Z3-M3 (shifted-det factorisation).** For every `t in R`, `det(t*I + L_Mob3) = det(t*I + L_scalar) * |det(t*I + L_{chi_1})|^2`. Natural Z/3 analogue of R6-M3; RHS real because the conjugate factors produce a modulus-squared.

**Z3-M4 (spectrum as multiset union).** `Spec(L_Mob3) = Spec(L_scalar) ⊎ Spec(L_{chi_1}) ⊎ Spec(L_{chi_2})` as multisets; each `Spec(L_{chi_m})` is real (Hermitian); `Spec(L_{chi_1}) = Spec(L_{chi_2})` as real multisets (Galois conjugation preserves real spectra). Every non-scalar eigenvalue of `L_Mob3` has even multiplicity.

**Z3-PSD.** `L_Mob3 succeq 0`; kernel as per Z3-M1. Proof sketch: `L_Mob3 = sum_e d_e^T d_e` with `d_e(f) = f(u) - Phi(e) f(v)`.

**Z3-strict (Möbius strict drop).** `dim ker L_Mob3 < 3 * comp(G)` iff some component has non-trivial Z/3-holonomy, i.e. the kernel equals `3 * comp(G)` iff the bundle is globally trivialisable.

**Z3-tree (forests are flat).** On any forest, every Z/3-bundle is trivialisable, so `dim ker L_Mob3(F, W) = 3 * comp(F)` for all `W`, and `Spec(L_Mob3) = Spec(L_scalar)` repeated three times. Cleanest sanity check for the fuzzer.

## 3. Tier-2 claims

**Z3-T1 (linear trace).** `tr(L_Mob3) = 3 * sum_v deg(v) = 6|E|`. Independent of `W`.

**Z3-T2 (quadratic trace).** `tr(L_Mob3^2) = 3 * sum_v deg(v)^2 + 6|E|`. Character-by-character: each `L_{chi_m}` has off-diagonal entries of unit modulus, so the edge contribution is `|chi_m(W(e))|^2 = 1`; identical across `m`. Independent of `W`.

**Z3-T3 (cubic trace, first W-dependent moment).** `tr(L_Mob3^3) = (degree-only terms independent of W) - 6 * #{oriented triangles whose W-sum is 0 mod 3}`. Because `sum_{m=0}^{2} omega^{m s} = 3 * [s ≡ 0 mod 3]`, non-balanced triangles cancel across the three characters; balanced triangles contribute triply.

**Z3-Frob (Hilbert-Schmidt norm).** `||L_Mob3||_F^2 = 3 * sum_v deg(v)^2 + 6|E|`; same as Z3-T2. Independent of `W`.

**Z3-cycle (single-edge wrap on C_n).** On `C_n` with one edge `W=1`, others `0`: `beta^{(3)}(C_n, W) = 1` iff `3 | n`; hence `dim ker L_Mob3 = 3` if `3 | n`, else `1`. Non-zero eigenvalues of `L_{chi_m}` on `C_n`: `2 - 2 Re(omega^m * e^{2 pi i j / n})`, `j = 0, ..., n-1`.

**Z3-K3 (triangle).** On `K_3` with all wraps zero: `Spec(L_Mob3) = {0,0,0, 3,3, 3,3, 3,3}` (three copies of `{0,3,3}`). With wraps summing to `1 mod 3` (non-balanced): `dim ker L_Mob3 = 1`, non-zero eigenvalues from Hermitian `L_{chi_m}` on `K_3` given by `3 - 2 Re(omega^{holonomy} * omega_{j})`.

**Z3-Kn (complete graph flat).** On `K_n` with all wraps zero, `Spec(L_Mob3) = {0^3, n^{3(n-1)}}`.

## 4. Tier-3 observations

**Z3-O1 (interlacing).** Sorted real spectra (ascending) satisfy `lambda_k(L_scalar) <= lambda_k(L_{chi_1})` for all `k`, for any `W`. Rationale: unit-modulus phases in `L_{chi_1}` obey a triangle inequality mirroring the signed Laplacian case. Expected to be fragile — prime falsification target.

**Z3-O2 (Gauss-sum / matrix-tree identity).** `det(L_Mob3 + I) = det(L_scalar + I) * |det(L_{chi_1} + I)|^2`; conjecturally `Re(det(L_{chi_1} + I))` admits a weighted-forest expansion where spanning forest `F` contributes `Re(prod_{e in F} chi_1(W(e)))`.

**Z3-O3 (orientation double cover interaction).** Z/3 has no order-2 element: flipping an edge conjugates `chi(w)`, swapping roles of `chi_1, chi_2`. Hence `Spec(L_{chi_1})` is orientation-dependent in general, but `Spec(L_{chi_1}) ⊎ Spec(L_{chi_2})` (and so `Spec(L_Mob3)`) is orientation-independent.

**Z3-O4 (generic simple spectrum).** For "generic" `W` on a connected graph with a cycle and `|V| >= 3`, non-zero eigenvalues of `L_Mob3` have multiplicity exactly 2 (size of the `{chi_1, chi_2}` Galois orbit). Multiplicity-1 only arises from accidental `L_{chi_1} ∩ L_scalar` spectrum overlaps.

**Z3-O5 (wheel graph).** On `W_n` (hub + `C_n`) with hub-edge wraps `0` and rim wraps `W_rim`: `dim ker L_Mob3 = 1 + 2 * [sum(W_rim) ≡ 0 mod 3]`.

## 5. Dependencies between claims

- `Z3-M2` (charpoly) is the master. `Z3-M3, M4, Frob, T1, T2, T3` all follow by reading off coefficients or traces of powers.
- `Z3-M1` uses `Z3-M4` plus `dim ker L_{chi_m} = beta^{(3)}` and Galois conjugation `ker L_{chi_1} ≅_C ker L_{chi_2}`.
- `Z3-strict` is `Z3-M1`'s equality case contrapositive.
- `Z3-tree` specialises `Z3-M1` (forests: every bundle trivial, `beta^{(3)} = comp`).
- `Z3-cycle, K3, Kn, O5` are concrete instances that falsify `Z3-M1`/`M4` under direct computation.
- `Z3-PSD` independent (operator-theoretic); supports the reality assertion in `Z3-M4`.
- `Z3-O2` is not implied by `M2` alone — it requires a new matrix-tree identity.

## 6. Suggested fuzzer targets for Stage 2 (ranked by surprise value if false)

1. **Z3-M1 kernel formula** — whole pilot depends on it. Exhaustive on `C_3, C_4, C_6, C_9` over all `W`; exhaustive `K_4, K_5`; 100 random ER `(n=7, p=0.5)` with random `W`.
2. **Z3-T2 W-independence** — `tr(L_Mob3^2)` must equal `3 sum deg^2 + 6|E|`. Any `W`-sensitivity falsifies the character-orthogonality skeleton.
3. **Z3-O4 generic multiplicity-2** — random graphs with random `W`; expect non-kernel multiplicity pattern dominated by 2.
4. **Z3-M2 charpoly factorisation** — numerically factor `p_{L_Mob3}` and verify divisibility by `p_{L_scalar}` and that the quotient is `|p(x)|^2` for a complex polynomial `p`.
5. **Z3-cycle C_n rule** — exhaustive `n = 3..10`. Catches off-by-one in holonomy convention.
6. **Z3-tree flatness** — random trees on 5..12 vertices with random `W`; kernel dim must always be `3 * comp`.
7. **Z3-PSD** — smallest eigenvalue `>= -eps` across 500 random `(G, W)`.
8. **Z3-O1 interlacing** — likely false in full generality; high surprise value.
9. **Z3-O2 Gauss-sum / MTT** — exploratory; fuzz `det(I + L_Mob3) / det(I + L_scalar)` vs weighted-forest sum.
10. **Z3-O3 orientation double-cover** — flip one edge of `W`; `Spec(L_Mob3)` must be invariant; individual `Spec(L_{chi_1})` should shift to `Spec(L_{chi_2})`.
