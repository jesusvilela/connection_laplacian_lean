# Adversarial Report — `componentProj_fiber_card`

**Target:** `ConnectionLaplacian/L6_Cohomology.lean:104`. Audited from `findings/s3_fiber_card/actor_proof.lean` and `actor_notes.md`.

## Verdict
Strategy is mathematically sound on all small cases tested. Two **real Lean-level cracks** and two **proof-engineering hazards** surfaced; no statement-level counterexample.

## Cracks

### C1 (real, Lean-level). Mismatched `DecidableEq` instances.
The target wraps `letI : DecidableEq G.graph.ConnectedComponent := Classical.decEq _` in the goal (L6_Cohomology.lean:105). The candidate proof opens with `classical`. Both produce instances, but `classical` introduces `Classical.dec (a = b)` per-call, while the `letI` binds `Classical.decEq _` at goal level. The `Fintype` instance on `{ D // componentProj D = C }` (used in `Fintype.card …`) is synthesised from whichever `DecidableEq` is in scope; the `hcard` line rewrites using an *inner* instance, but the goal `if G.isBalanced … then 2 else 1` still sees the *outer* `letI`. Lean may refuse unification. **Fix:** drop `classical`; let the outer `letI` govern, or `convert` at the end. Not a math bug but will bite the first build.

### C2 (real, Lean-level). `subst hv₀` after `Quot.exists_rep`.
`hv₀ : G.graph.connectedComponentMk v₀ = C`. `subst` requires the LHS or RHS to be a free local. `C` is free, so `subst` substitutes it globally. This works, but every subsequent `G.isBalanced C` becomes `G.isBalanced (mk v₀)`, and `hD : componentProj D = C` becomes `… = mk v₀`. The sketch's `fiber_subset_candidates _ v₀ rfl D hD` call is consistent with this post-subst shape. No bug, just a caller note.

### C3 (engineering). RS1 existence is enough; RS2 is the real hole.
RS1 as stated (`∃ b', Reachable (w,b) (v₀,b')`) suffices for the upper bound fiber ≤ 2. The strategy does **not** need `b'` to be determined by walk parity for the card theorem — that only matters for defining ε in RS2. So RS1 is a clean induction on a base walk (low risk). RS2 `←` (unbalanced ⇒ merge) is the hard direction: given unbalanced, one must *construct* a cover-walk `(v₀,false) ⇝ (v₀,true)`. The sketch says "walk through a failure edge," but `isBalanced`'s negation is `∀ ε, ∃ failure edge(ε)`. You must pick one ε (e.g., parity via a chosen spanning-tree walk from v₀), find the failure edge for *that* ε, then close the cycle via the tree. Full Zaslavsky-style argument, not a one-liner.

### C4 (engineering). Edge-subtype symmetry boilerplate.
In `isBalanced`, the edge is `⟨s(u,v), mem_edgeSet.mpr h⟩` with `h : Adj u v`. Swapping endpoints requires `Subtype.ext` + `Sym2.eq_swap` (pattern at `Basic.lean:134–138`, `L5_Cover.lean:71–75`). RS2 induction will step across edges in walk direction and needs this rewrite at least twice (ε-constancy in `→`; failure edge read-off in `←`).

## Non-cracks (verified)

- **v₀-independence of merge ↔ unbalanced.** Balancedness is a property of C, not v₀. By RS1 + deck-symmetry, merge-property is invariant under choice of v₀ ∈ C. The per-v₀ statement suffices (one v₀ picked via `Quot.exists_rep`).
- **Isolated vertex C = {v}.** `isBalanced` vacuous → true. Cover has no edges at (v,·), so `(v,false)` and `(v,true)` are in distinct cover-components. Fiber = 2 = `if true then 2 else 1`. ✓
- **ε scope over all G.V.** The `mk u = C →` guard restricts the constraint to C; other components are unconstrained. No over-constraint.
- **C_3, 2 wraps (even).** Balanced: ε = (0,1,0) works. ✓
- **C_3, 1 wrap (odd).** Unbalanced; single cover-component (sheet flip once around cycle). ✓
- **Self-loops.** `SimpleGraph` is `loopless`; no trap.
- **API names confirmed present at `Mathlib/Combinatorics/SimpleGraph/Path.lean`:** `ConnectedComponent.sound` (816), `ind` (806), `map_mk` (876) — `map_mk` is `rfl`, so `componentProj_candidateLift` is clean.

## Residual risk
RS2 `←` is the honest combinatorial core — budget ~80% of total proof effort. RS1 + scaffolding ~20%.
