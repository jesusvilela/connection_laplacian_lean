# PROVER-WALKH1 — Round 4 Report

## Deliverable

Landed `ConnectionLaplacian/L12_WalkH1.lean` (322 lines, zero `sorry`, builds clean under `leanprover/lean4:v4.11.0`). Registered in top-level import manifest. Full-project `lake build` passes.

## Main theorem (T4) — both directions proved

```lean
theorem isBalanced_iff_closedWalk_wrap_even
    (C : G.graph.ConnectedComponent) : G.isBalanced C ↔
      ∀ (v : G.V) (p : G.graph.Walk v v),
        G.graph.connectedComponentMk v = C →
        Even (p.edges.countP
                (fun e => decide (∃ h : e ∈ G.graph.edgeSet, G.wrap ⟨e, h⟩)))
```

Exact signature requested; no weakening.

## Proof architecture

- Helper `wrapEdgeBool : Sym2 V → Bool` reifying the decidable wrap predicate.
- `walkWrapCount p := p.edges.countP wrapEdgeBool` with cons/nil simp lemmas.
- `natParity n := n.bodd` plus a hand-built `even_iff_natParity_false` bridge (via `Nat.even_iff` + `Nat.bodd_add`; Mathlib v4.11 lacks `Nat.bodd_eq_false_iff_even`).
- **(⇒)** `walkWrapCount_xor_of_balance`: induction on the base walk telescopes `xor (ε u) (ε v) = natParity (walkWrapCount p)`. Closed walk ⇒ xor = false ⇒ even.
- **(⇐)** `projectCoverWalk` drops sheet coordinates from a cover walk. `projectCoverWalk_wrap_parity`: sheet-XOR of endpoints equals parity of projected wrap count. A cover walk `(v₀, false) ⇝ (v₀, true)` would project to a closed walk with parity `true`, contradicting closed-walk-evenness. So the two candidate sheets above `v₀` are distinct. A shim `balanced_of_candidate_sheets_ne` converts sheet separation to balance via the public `componentProj_fiber_card`.

## Cycle corollary (T10) — not landed

Omitted rather than stubbed. Constructing a fundamental-cycle walk on `SimpleGraph.cycleGraph n` whose edges enumerate `Finset.univ` exactly once would need several hundred lines of `Fin n` index bookkeeping. The walk-sum detector is exactly the interface one would instantiate.

## Key dependencies pulled from L6

`isBalanced`, `CoverV`, `coverGraph`, `coverAdj`, `candidateLift`, `componentProj`, `componentProj_fiber_card`, `connectedComponentMk_eq_of_adj`.
