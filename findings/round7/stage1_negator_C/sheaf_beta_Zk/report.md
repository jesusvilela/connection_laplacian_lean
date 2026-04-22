# Round 7 — NEGATOR-C tile beta (Z/k structural)

**Role:** Generate falsifiable STRUCTURAL hypotheses for the connection Laplacian over an arbitrary finite cyclic group Z/k, k >= 2. Statements must contain k as a free parameter.

**Sibling tiles:** alpha (Z/3 pilot), gamma (U(1) limit). This tile produces the k-parametric skeleton they must both specialize to.

**Setup recap:** wraps w : E -> Z/k, phi(e) = P_k^{w(e)}, L_{Mob,k} in R^{kn x kn}; DFT on the fibre conjugates to block-diag of L_{chi_m} for m = 0, ..., k-1. beta^{(d)}(G,W) = number of d-balanced components (d | k).

---

## Tier 1 — Masters (unlock the Z/k story)

### Zk-M0 (Kronecker-DFT decomposition)
**Statement.** Let F_k be the k x k unitary DFT matrix and U = I_V ⊗ F_k. Then U^* L_{Mob,k}(G,W) U = block-diag over m = 0,...,k-1 of L_{chi_m}(G,W), where L_{chi_m} is the complex weighted scalar Laplacian with edge phase chi_m(w(e)) = exp(2π i m w(e)/k).
**Rationale.** The per-edge block P_k^{w(e)} is the regular representation of Z/k evaluated at w(e); DFT decomposes the regular rep into 1-dim irreps indexed by m.
**Proof sketch.** F_k^* P_k F_k = diag(ω^0,...,ω^{k-1}) with ω = e^{2π i/k}. I_V ⊗ F_k commutes with the V x V block structure. Direct block-entry computation shows the off-diagonal V x V block at (u,v) becomes diag_m(-chi_m(w(u,v))).
**Tier:** 1. Generalizes R6 L16 base isomorphism.

### Zk-M1 (kernel dimension — divisor-indexed balance tower)
**Statement.** dim ker L_{Mob,k}(G,W) = Σ_{m=0}^{k-1} β^{(k/gcd(m,k))}(G,W) = Σ_{d|k} φ(d) · β^{(d)}(G,W).
**Rationale.** chi_m factors through Z/(k/gcd(m,k)) so its scalar Laplacian detects (k/gcd(m,k))-balance. Counting m's with a given divisor gives Euler φ(d). Matches k=2 (#comp + β^{(2)}), k=3 (#comp + 2β^{(3)}), k=4 (#comp + β^{(2)} + 2β^{(4)}), k=6 (#comp + β^{(2)} + 2β^{(3)} + 2β^{(6)}).
**Proof sketch.** By Zk-M0, ker L_{Mob,k} = ⊕_m ker L_{chi_m}. Standard result at chi-level: dim ker L_{chi_m} = number of components whose cycle-holonomies lie in ker(chi_m) = (k/gcd(m,k))·Z/kZ.
**Tier:** 1. Master generalization of R6 signed/twin kernel formula.

### Zk-M2 (characteristic polynomial factorisation)
**Statement.** charpoly(L_{Mob,k}) = Π_{m=0}^{k-1} charpoly_C(L_{chi_m}). Complex-conjugate pairs (m, k-m) multiply to real-coefficient polynomials; if weights are rational the whole product is in Z[x].
**Rationale.** Zk-M0 + multiplicativity of det on block-diagonal. chi_m^bar = chi_{k-m} gives the conjugation pairing.
**Tier:** 1. Generalizes R6 L16.

### Zk-M3 (shifted determinant)
**Statement.** For all α, det(L_{Mob,k} + α I_{kn}) = Π_m det(L_{chi_m} + α I_n).
**Rationale.** Specialisation of charpoly factorisation at x = -α. Key for matrix-tree-style identities and signed resistance transforms.
**Tier:** 1.

---

## Tier 2 — Corollaries

### Zk-S1 (linear trace)
**Statement.** tr(L_{Mob,k}) = 2k|E|.
**Rationale.** Each vertex diagonal block is deg(v)·I_k (since Φ(e)^* Φ(e) = I_k); sum of traces = k·Σ deg(v) = 2k|E|. Independent of W.
**Tier:** 2. Generalizes R6 L17 trace.

### Zk-S2 (quadratic trace decomposition)
**Statement.** tr(L_{Mob,k}^2) = Σ_m tr(L_{chi_m}^2). Summed over m, character-orthogonality (Σ_m chi_m(w) = k·[w=0]) collapses off-diagonal contributions to k·#(closed length-2 walks with zero holonomy).
**Rationale.** Parseval on the fibre. First place Gauss-sum-type identities appear; absent for k=2.
**Tier:** 2.

### Zk-S3 (Frobenius sum)
**Statement.** ||L_{Mob,k}||_F^2 = Σ_m ||L_{chi_m}||_F^2 = 2k|E| + k·Σ_v deg(v)^2 + 2k·(count of 2-cycle walks with zero holonomy). Equals k·||L_scalar||_F^2 when every cycle is k-balanced.
**Rationale.** Unitary invariance under U = I ⊗ F_k plus character sum.
**Tier:** 2.

### Zk-PSD (positive semidefiniteness)
**Statement.** L_{Mob,k}(G,W) ⪰ 0 for all k, all (G,W); each L_{chi_m} is Hermitian PSD.
**Rationale.** L_{Mob,k} = B B^* with edge-oriented boundary blocks (I_k, -P_k^{w(e)}); each L_{chi_m} = B_m B_m^* analogously.
**Tier:** 2.

### Zk-tree (tree kernel maximality)
**Statement.** If G is a forest, dim ker L_{Mob,k}(G,W) = k·#components for every W and every k.
**Rationale.** No cycles ⇒ every component is d-balanced for every d | k ⇒ Σ_m β^{(·)} = k·#comp by Zk-M1.
**Tier:** 2.

### Zk-cycle (single-cycle balance)
**Statement.** For G = C_n with total wrap W mod k, β^{(d)}(C_n, w) = 1 iff d | W, else 0. Hence dim ker L_{Mob,k}(C_n, w) = #{m in 0..k-1 : (k/gcd(m,k)) | W} = gcd(W, k).
**Rationale.** chi_m(W) = 1 iff k | mW iff (k/gcd(m,k)) | W; count equals gcd(W,k). Absent for k=2 (answer is only 1 or 2).
**Tier:** 2.

### Zk-lift (Z/2 embedded in Z/k for even k)
**Statement.** If k is even, chi_{k/2}(w) = (-1)^w is real and L_{chi_{k/2}} equals the R6 signed Laplacian L_{sign}(G, w mod 2). Every R6 signed theorem pulls back to a Z/k statement at m = k/2.
**Rationale.** exp(π i w) = (-1)^w; Z/k → Z/2 is the natural quotient.
**Tier:** 2.

### Zk-functoriality-in-k (divisor refinement)
**Statement.** If k1 | k2, characters of Z/k1 embed in characters of Z/k2 via m' ↦ m'·(k2/k1). Hence each L_{chi_{m'}} for Z/k1 appears as an L_{chi_m} for Z/k2; the multi-set of Z/k1 eigenvalues is a sub-multi-set of the Z/k2 eigenvalues under the corresponding wrap lift.
**Rationale.** Pullback of characters along the surjection Z/k2 → Z/k1.
**Tier:** 2.

---

## Tier 3 — Empirical / needs fuzzer verification

### Zk-CRT (Chinese Remainder Theorem tensor)  [NEW, absent for k=2 alone]
**Statement.** For gcd(k1, k2) = 1, with pair-wraps (w1, w2) corresponding via CRT to W in Z/(k1 k2), L_{Mob,k1 k2}(G, W) is unitarily equivalent (after CRT permutation of the fibre) to a structured combination of L_{Mob,k1}(G, w1) and L_{Mob,k2}(G, w2); in particular β^{(d1 d2)}(G, W) = β^{(d1)}(G, w1)·β^{(d2)}(G, w2) for d1 | k1, d2 | k2.
**Rationale.** CRT factorises the regular rep. Multiplicativity of balance counts is a sharp empirical prediction.
**Tier:** 3.

### Zk-primes (prime-k collapse)  [NEW, absent for k=2 alone]
**Statement.** For k prime, every non-trivial character chi_m (m in 1..k-1) gives L_{chi_m} in the same (Z/k)^*-Galois orbit; hence they are pairwise Galois-conjugate over Q(ω_k) and isospectral over R. Therefore dim ker L_{Mob,k} = #comp + (k-1)·β^{(k)} and charpoly(L_{Mob,k}) = charpoly(L_scalar)·charpoly(L_{chi_1})^{k-1}.
**Rationale.** Non-trivial characters form one (Z/k)^*-orbit when k is prime; conjugation by Galois permutes their eigenvalues.
**Tier:** 3.

### Zk-GaussSum (higher trace character identity)  [NEW]
**Statement.** For every p ≥ 1, tr(L_{Mob,k}^p) = k·(number of closed length-p walks with total holonomy ≡ 0 mod k) + (k-independent correction from boundary terms). More precisely, Σ_m chi_m(h) = k·[h ≡ 0 mod k] collapses the walk sum character-by-character.
**Rationale.** Parseval / Gauss-sum orthogonality applied to trace of p-th power. For k=2 the identity degenerates; general k has strictly richer structure.
**Tier:** 3.

### Zk-moment-generating (resolvent / Ihara-zeta)
**Statement.** For |α| larger than spectral radius, log det(L_{Mob,k} + α I) admits a closed-walk expansion whose chi_m-weighted coefficients, after DFT inversion, give k·(count of closed walks with zero holonomy mod k).
**Rationale.** Standard log-det / zeta-function combinatorial identity applied character-by-character.
**Tier:** 3.

### Zk-conjugation-pair realness
**Statement.** For m in 1..k-1 with 2m ≠ k mod k, (L_{chi_m}, L_{chi_{k-m}}) are complex-conjugate; their combined 2n eigenvalues pair up, contributing a real-coefficient degree-2n factor of charpoly(L_{Mob,k}). Remaining factors: charpoly(L_scalar) always, plus charpoly(L_{sign}) when k is even (m = k/2 self-conjugate).
**Rationale.** Labels the real factorisation of charpoly into Galois chunks.
**Tier:** 3.

### Zk-spectral-symmetry (Galois orbit)  [NEW]
**Statement.** spec(L_{chi_m}) = spec(L_{chi_{-m}}) unconditionally; for vertex-transitive G the spec depends only on the (Z/k)^*-orbit of m.
**Rationale.** Hermitian conjugation gives m ↔ -m; Galois symmetry over Cayley graphs.
**Tier:** 3.

### Zk-degree-monotonicity (lift behaviour)
**Statement.** If k1 | k2 and W : E → Z/k1 is lifted to Z/k2 by inclusion, dim ker L_{Mob,k2}(G, lift W) = (k2/k1)·dim ker L_{Mob,k1}(G, W) + (k2 − k2/k1)·#comp.
**Rationale.** Characters of Z/k2 that kill the lifted image become trivial Laplacians contributing #comp each; the remaining k2/k1 characters factor through Z/k1.
**Tier:** 3.

### Zk-anti-balance (frustration floor)
**Statement.** For prime k, if G is connected and β^{(k)}(G,W) = 0 (no k-balanced component), dim ker L_{Mob,k}(G,W) = 1 exactly.
**Rationale.** By Zk-primes, non-trivial characters contribute (k-1)·0; chi_0 contributes #comp = 1.
**Tier:** 3.

---

## Cross-tile hooks

- **alpha (Z/3)** must verify Zk-primes, Zk-anti-balance, Zk-GaussSum at k=3.
- **gamma (U(1))** consumes Zk-M0/M1 in the limit: as k → ∞, the divisor sum becomes an integral over S^1, β^{(d)} becomes a spectral density of the holonomy representation; Zk-functoriality-in-k is the direct system whose colimit is U(1).
- **Gluer** verifies: R6 L16/L17 ≡ Zk-M2 + Zk-S1 at k=2; Zk-lift at even k reproduces R6 exactly.

## Primary falsification avenues

1. **Zk-M1** via fuzzer on random (G,W) for k in {3,4,5,6}: direct dim ker vs divisor sum.
2. **Zk-primes isospectrality**: compare spec(L_{chi_1}) vs spec(L_{chi_2}) for k prime.
3. **Zk-CRT** multiplicativity of balance counts on product graphs.
4. **Zk-GaussSum** cubic/quartic trace identity on small random graphs.

If any of M0–M3 fails on small random k, the entire Z/k pipeline must be re-scoped; S1–S3, PSD, tree, cycle, and lift are lower-risk corroborators.

---

**Claims NOT already present in Z/2 (required ≥4):** Zk-CRT, Zk-primes, Zk-GaussSum, Zk-spectral-symmetry (Galois-orbit), Zk-cycle (gcd-formula richer than {0, 2}), Zk-degree-monotonicity, Zk-anti-balance. (Seven new.)

**Counts:** 4 Tier-1 + 8 Tier-2 + 8 Tier-3 = 20 hypotheses.
