# NEGATOR report — `componentProj_fiber_card`

**Target** (`L6_Cohomology.lean:104`):
`|{D ∈ π₀(G.coverGraph) : componentProj D = C}| = if isBalanced C then 2 else 1`.

**Outcome: NO COUNTEREXAMPLE FOUND.** Statement appears correct.

## Method

Python brute-force checker using `networkx`:
- Constructs `coverGraph` on `V × {0,1}` with `(u,b)~(v,c)` iff `{u,v} ∈ E` and `(b = c) ↔ ¬wrap({u,v})`.
- Decides `isBalanced(C)` by brute-forcing `ε : V → {0,1}` on edges within `C`.
- Counts cover-components whose fst-projection equals `C` exactly.

## Configurations tested (all base components, per-component comparison)

| Family | \|V\| | \|E\| | Wrap subsets | CEs |
|---|---|---|---|---|
| K_2 | 2 | 1 | all 2 | 0 |
| P_3 | 3 | 2 | all 4 | 0 |
| C_3 / C_4 / C_5 | 3–5 | 3–5 | all (up to 32) | 0 |
| K_4 | 4 | 6 | all 64 | 0 |
| K_{3,3} | 6 | 9 | all 512 | 0 |
| theta graph | 5 | 6 | all 64 | 0 |
| C_3 ⊔ C_3 | 6 | 6 | all 64 | 0 |
| star K_{1,4} | 5 | 4 | all 16 | 0 |
| isolated + edge | 3 | 1 | all 2 | 0 |
| bowtie | 5 | 6 | all 64 | 0 |
| K_4 − e | 4 | 5 | all 32 | 0 |
| cube Q_3 | 8 | 12 | all 4096 | 0 |
| Petersen (random) | 10 | 15 | 5000 | 0 |
| Random G(n,p), n∈[4,8] | | ≤28 | 36086 | 0 |

**Total: 46 062 (G, wrap) configurations × all base components = 0 counterexamples.**

## Observations supporting the formula

- Cycles C_n: balanced iff even # wrap edges; cover is one 2n-cycle (fiber 1) if odd, splits into two n-cycles (fiber 2) if even.
- Trees: every wrap-subset is balanced (flip ε along any wrap edge); cover always splits.
- K_{3,3}, Q_3: bipartite double-cover analogue — coboundary wraps preserve two sheets (fiber 2); nontrivial Z/2-cohomology class merges sheets (fiber 1).
- Isolated `C = {v}`: vacuously balanced; cover has two isolated vertices over v; fiber = 2.

## Edge cases considered and dismissed

- Multiple components: formula checked per-component; independent.
- SimpleGraph loopless: no loop cases possible.
- Inter-component wrap: impossible (wrap is on edges of G.graph; never cross components).

## Conclusion

No refutation exists. PROVER's path-lifting / Z/2-cocycle sketch is strongly corroborated.
