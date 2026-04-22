# ADVERSARIAL-FIBER — Discovery Round 3 Findings

**Target**: `ConnGraph.componentProj_fiber_card` in `L6_Cohomology.lean:344-409`, plus supporting lemmas `walkLift`, `reachable_{from,to}_rep_sheet`, `fiber_subset_candidates`, `coverGraph_walk_deck`, `walk_preserves_xor_invariant`, `sheets_ne_of_balanced`, `unique_sheet_above`, `balanced_of_sheets_separated`.

**Scope**: read-only attack.

## 1. Walk-lift determinism — ROBUST
`walkLift` is genuinely walk-dependent (on unbalanced C_3 with one wrap, nil gives b'=b, once-around gives !b). Three call sites are nonetheless safe:
- `reachable_{from,to}_rep_sheet` (L148-162): produces ∃ b''. Reachable... — any witness valid.
- `fiber_subset_candidates` (L166-191): uses reachability only through `ConnectedComponent.sound`.
- `balanced_of_sheets_separated` (L288-332): uses `Classical.choose`; uniqueness re-proved via deck involution + hsep, independent of which walk was chosen.

## 2. Balance ε scope (off-component) — ROBUST (design note)
`isBalanced C` leaves ε unconstrained off C. Audit confirms `hε` always applied under `connectedComponentMk _ = C` guard. The guard propagates through `cons` case via `connectedComponentMk_eq_of_adj` (L250-252).
**Design note**: latent footgun for future contributors. Document at definition or restrict ε to C.supp.

## 3. `coverGraph_walk_deck` correctness — ROBUST
Structural recursion: nil ↦ nil, cons via `deck_coverAdj h` (bidirectional from `deck_adj_iff`). Terminates. Faithfully pushes walk through deck automorphism.

## 4. Edge cases — ROBUST
- Isolated vertex: vacuously balanced, fiber=2. ✓
- Self-loop: excluded by SimpleGraph.loopless, used explicitly in `coverAdj_irrefl`. ✓
- Single edge: trivially balanced. ✓
- Triangle one wrap: unbalanced, fiber=1. ✓
- Triangle two wraps: balanced (ε=0,1,0), fiber=2. ✓

## 5. Sheet-flipping logic — ROBUST
Avoids orbit language. Surjection φ:Bool→fiber. Balanced ⇒ injective (sheets_ne_of_balanced) ⇒ card=2. Unbalanced ⇒ candidateLift v₀ false = candidateLift v₀ true ⇒ card=1. Deck involution enters only in `unique_sheet_above`: contradicts hsep correctly.

## 6. `ConnectedComponent.ind` motive — ROBUST
Motive is Prop-valued (`Quot.ind`). Post-revert goal `∀ hD. ...` elaborates cleanly; no manual rec squeezing.

## 7. Fintype / classical-ε leak — ROBUST
`letI : DecidableEq ConnectedComponent := Classical.decEq _` at type-scope. `Fintype.card` on subtype is instance-invariant. ε is internal to `balanced_of_sheets_separated`; never flows into Nat RHS. No leak.

## 8. Minor observations
- `simpa [deck]` at L280-282 relies on `deck x = (x.1, !x.2)`. Purely structural.
- `unique_sheet_above` is private but is the conceptual heart. Worth exposing for cycle-case corollary reuse.

## Verdict

| Attack vector | Verdict |
|---|---|
| Walk-lift non-determinism exploited? | ROBUST |
| ε applied off its component? | ROBUST |
| `coverGraph_walk_deck` correct? | ROBUST |
| Isolated vertex / self-loop / small cycles? | ROBUST |
| Sheet-flipping / orbit logic sound? | ROBUST |
| `ConnectedComponent.ind` motive well-typed? | ROBUST |
| Fintype / classical leak into card? | ROBUST |
| `isBalanced` ε scope convention (design) | POTENTIAL WEAKNESS |
| **Confirmed bugs** | **NONE** |

## Recommendations (non-blocking)
1. Doc comment at `isBalanced` explaining intentional under-specification.
2. Make `unique_sheet_above` non-private.
3. When cycle-case corollary is filled in §L6.5, verify ε from `balanced_of_sheets_separated` agrees with even-wrap-prefix-count coloring on cycles — bridge to `numOddWrapComponents`.
