# Critic Report — `componentProj_fiber_card` (L6)

Target: `ConnectionLaplacian/L6_Cohomology.lean:104-108`. No code modified.

## 1. `isBalanced` quantifier scope — correct but worth flagging
The definition (lines 52-55) quantifies `∀ u v, ∀ h : Adj u v,
connectedComponentMk u = C → (wrap ⟨s(u,v),_⟩ ↔ ε u ≠ ε v)`. Since
`Adj u v` forces `mk u = mk v`, testing only `mk u = C` is equivalent to
testing `mk v = C`. Edges outside `C` are vacuously unconstrained, so ε is
effectively local on `C`. Semantics match Zaslavsky-balanced. No bug, but
a proof using path-based ε-construction will need to supply a global ε
(e.g. `False` off `C`), adding bookkeeping.

## 2. Symmetry of edge witness — no bug, but fragile
Swapping `(u,v,h)` to `(v,u,h.symm)` yields edge
`⟨s(v,u), mem_edgeSet.mpr h.symm⟩`. Equality to the original requires
`Subtype.ext` + `Sym2.eq_swap` (same pattern used in `Basic.lean:134-138`
and `L5_Cover.lean:71-75`). This is propositional, not definitional, so
any tactic proof invoking the symmetry must `rw` explicitly through
`Subtype.ext`. Flag as boilerplate, not bug.

## 3. Isolated-vertex edge case — passes
`C = {v}` with no incident edges: `isBalanced C` is vacuously true (any
ε works). In `coverGraph`, `(v,false)` and `(v,true)` have no neighbors
(`coverAdj` demands `G.graph.Adj v v` which is refuted by `loopless`),
so they live in distinct components. Fiber size = 2, matching
`if true then 2 else 1`. Consistent.

## 4. Self-loops — non-issue
`SimpleGraph` is `loopless`; no hidden trap.

## 5. Fiber size ≤ 2 — short argument works
For any `D = mk (v, b)` with `mk v = C`, pick a G-walk `v ⇝ v₀` in `C`;
it lifts (uniquely, given starting sheet `b`) to a cover-walk ending at
`(v₀, b')`. Hence every `D` in the fiber equals `mk (v₀, false)` or
`mk (v₀, true)`. No need for an injection into `Bool`; just note the
fiber is a subset of the image of `Bool → CoverComponents, b ↦ mk (v₀,b)`.

## 6. `coverProj.map_rel'` — correct
Lines 81-89. In the `hadj` positive branch, the returned term is `hadj`
itself; the body of `coverAdj` is irrelevant, so the `dif_pos` rewrite
isn't actually needed (the `by_cases` suffices). Negative branch uses
`dif_neg hadj` to reduce `h` to `False`. Direction u→v is respected;
`Prod.fst` is symmetric in the required sense because `coverAdj_symm`
is installed on `coverGraph.Adj`.

## 7. `G.componentProj D = G.componentProj D` by `rfl` — OK
`ConnectedComponent.map_mk` (Mathlib Path.lean:876) is tagged `@[simp]`
and holds by `rfl`. The `⟨G.componentProj D, D, rfl⟩` constructor in
`numComponents_cover` (line 131) typechecks.

## 8. **Primary gap — the missing bridge lemma**
The `sorry` at line 108 is not a statement bug; it is a missing
biconditional:
```
isBalanced C ↔
  ∀ v, mk v = C → (G.coverGraph.connectedComponentMk (v,false)
                 ≠ G.coverGraph.connectedComponentMk (v,true))
```
The `→` direction: ε induces a sheet-coloring that would have to flip
along any cover-path (v,false)⇝(v,true), forcing a wrap-count parity
contradiction. The `←` direction: define ε by sheet of a chosen lift.
Neither direction is short; the proof needs `Walk.transfer`/path-lifting
on the cover. No shortcut via Mathlib's existing API visible.

## 9. Decidable-fiber subtype — check `DecidableEq ConnectedComponent`
`{ D // G.componentProj D = C }` needs `Fintype`, which needs
`DecidableEq G.graph.ConnectedComponent`. Mathlib supplies this for
finite graphs with decidable Reachable (present via `decrel`). Not
broken, but if the proof is built without `classical`, verify the
instance resolves without `Classical.dec`.

## Verdict
`isBalanced` and `coverProj` are correct as stated. The sorry is a
real mathematical gap (path-lifting lemma), not a definition bug. No
corrected definition is needed.
