# NEGATOR-A R6 — Sheaf-section α (edge operations)

**Date:** 2026-04-22. **Envelope:** n ∈ {3,4,5} exhaustive × all wrap subsets (~3,453 configs); higher-arity claims (A7/A8/A9/A10/A12) capped at n ≤ 4. **Total fuzz trials:** 156,009 across 14 fresh α-tile claims.

## 1. Summary table (ranked by τ)

| # | claim | precondition | τ | supp / total |
|---|-------|--------------|---|--------------|
| A2  | Adding a pendant (new vertex) non-wrap edge preserves β | fresh vertex w, edge (v,w) ∉ W | **1.0000** | 17072/17072 |
| A3  | Adding a pendant wrap edge preserves β | fresh vertex w, edge (v,w) ∈ W | **1.0000** | 17072/17072 |
| A7  | Iterated k-fold subdivision of non-wrap edge preserves β (k ∈ {2,3}) | e ∉ W; k fresh vertices; all new edges non-wrap | **1.0000** | 796/796 |
| A8  | Subdivide edge e into k parts with wrap-count parity equal to [e ∈ W] preserves β | k ∈ {2,3}; Σ new-wrap bits ≡ [e ∈ W] (mod 2) | **1.0000** | 4776/4776 |
| A10 | Order of adding 2 new edges is irrelevant for β | e₁, e₂ ∉ E(G); any wrap assignment | **1.0000** | 1680/1680 |
| A12 | Theta-replacement of non-wrap edge by 2 parallel length-2 non-wrap paths preserves β | e ∉ W; replace by u–w₁–v, u–w₂–v; new edges non-wrap | **1.0000** | 398/398 |
| A13 | Vertex-switching invariance: β(G,W) = β(G, switch_v(W)) | any vertex v | **1.0000** | 17072/17072 |
| A1  | β(G,W) = β(G−e, W) for non-bridge non-wrap e (any G) | e ∉ W, e non-bridge | 0.9208 | 12062/13100 |
| A6  | Contract wrap edge e after switching at one endpoint preserves β | e ∈ W; switch at u; then contract | 0.8505 | 11138/13096 |
| A5  | Contracting a non-bridge non-wrap edge preserves β | e non-bridge, e ∉ W, G connected | 0.8461 | 10766/12724 |
| A14 | Flipping wrap status of a single non-bridge edge preserves β | e non-bridge, W' = W ⊕ {e} | 0.8415 | 22048/26200 |
| A4  | Non-wrap edge swap (remove e, add e') preserves β | G conn; e ∉ W non-bridge; e' ∉ E non-wrap non-br of G' | 0.8412 | 14132/16800 |
| A11 | β(G,W) = β(G, E\W) when W is itself bipartite as a graph on V | H = (V, W) is bipartite | 0.7512 | 1531/2038 |
| A9  | Adding 2 new non-wrap edges preserves β | e₁, e₂ ∉ E(G); both non-wrap | 0.1711 | 32/187 |

## 2. τ=1 claims — R7 prover candidates (≥ 50 supports each)

- **A2** pendant non-wrap add: `numBalancedComponents_add_pendant_nonwrap` (17072 supports). Dual of L15 bridge-deletion.
- **A3** pendant wrap add: `numBalancedComponents_add_pendant_wrap` (17072 supports). Follows from A2 ∘ A13 via leaf-switch.
- **A7** iterated non-wrap subdivision k ∈ {2,3} (796 supports). Trivial induction on R5 R6.
- **A8** parity-matching k-subdivision (4776 supports). **Cleanest unified lemma** — subsumes R5 R6, R5 R7, A7 as instances. Top α-tile R7 target.
- **A10** set-union commutativity of edge additions (1680 supports). Trivial; one-liner.
- **A12** theta-replacement of non-wrap edge (398 supports). Novel; not covered by R5. Proof traces new 4-cycle parity (γ flavour).
- **A13** vertex-switching invariance (17072 supports). Classical signed-graph fact; gluer should grep Lean for existing version; if absent, mandatory R7 addition `numBalancedComponents_switching_invariant`.

## 3. Claims in τ ∈ [0.5, 0.95] — refinement suggestions

- **A1 (0.9208)** — CE: K₃, W={(0,1)}, remove (0,2): β 0→1. Already addressed by L15 (one-sided ≤). Drops off R7 queue as equality; kept as cross-check.
- **A4 (0.8412)** — CE: n=4 paw graph with W={(0,1)}, swap (1,2)→(2,3): β 0→1. Refinement: require every unbalanced cycle survives in G−e+e'. Defer to β/γ.
- **A5 (0.8461)** — CE: K₃, W={(0,1)}, contract (0,2): β 0→1. Refinement: test monotone inequality β(G) ≤ β(G/e) — likely R7 paired with L15's deletion-monotonicity.
- **A6 (0.8505)** — Same mechanism as A5. Likely also admits β ≤ β(result).
- **A14 (0.8415)** — CE: K₃, W=∅, flip (0,1): β 1→0. Exact criterion: flip preserves β iff every fundamental cycle through e is parity-stable — pure γ data.
- **A11 (0.7512)** — CE: K₃, W=∅: trivially W-bipartite, E\W full K₃, β 1→0. Superseded by R5 R4 (need G bipartite).

## 4. τ < 0.1

- **A9 (0.1711)** — CE: empty G₃, W=∅, add (0,1)+(0,2): β 3→1. Deliberate falsifier — edges merge components. Covered by R5 R20 + L15.

## 5. Promotion ladder

- **Promote to R7 prover queue (τ=1, novel, ≥50 supports):** A2, A3, A7, A8, A12.
- **Already covered / trivial:** A10, A13 (gluer must check existing Lean switching-invariance).
- **Refuted as equality, monotone inequality likely τ=1:** A1 (done in L15), A5, A6 — recommend fuzz of β(G) ≤ β(G/e).
- **Refuted / superseded:** A11, A9.
- **Needs cross-sheaf refinement:** A4, A14.

**Top-3 high-novelty α R7 targets:** A8 (unified parity-matching subdivision), A12 (theta-replacement), A2/A3 (pendant-addition duals of L15).

## 6. Sheaf-boundary section (α ∩ β, α ∩ γ)

- **A4 (edge swap, τ=0.84)** — refinement via cycle-space embedding ⇒ **α ∩ γ**.
- **A5 / A6 (non-bridge / wrap contraction, τ≈0.85)** — companion monotone inequality via H¹(G;Z/2) → H¹(G/e;Z/2) surjectivity ⇒ **α ∩ γ**.
- **A12 (theta-replacement, τ=1)** — α-statement, γ-proof (4-cycle parity through H¹) ⇒ **α ∩ γ**.
- **A14 (wrap flip, τ=0.84)** — exact criterion is pure γ data on fundamental cycles through e ⇒ **α ∩ γ**.
- **A11 (W-bipartite complement, τ=0.75)** — cleanest refinement via "W is Z/2-coboundary" ⇒ **α ∩ γ**.
- **A13 (switching, τ=1)** — gauge invariance belongs to γ proper ⇒ **α ∩ γ**.
- **A5/A6 companion inequality** — if pursued spectrally, Cauchy interlacing under contraction (mirror of R5 R17 under deletion) ⇒ **α ∩ β**.

**Pure-α (no gluing):** A2, A3, A7, A8, A10.
