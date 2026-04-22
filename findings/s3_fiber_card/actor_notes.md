# s3_fiber_card — actor notes

## Target
`L6_Cohomology.lean:104 componentProj_fiber_card`: fiber = 2 if
balanced, 1 if unbalanced.

## Strategy
Pick `v₀` rep of `C`. Candidate lifts
`candidateLift v₀ b := connectedComponentMk (v₀, b)`. Steps:

- (A) both candidates project to `C` — `ConnectedComponent.map_mk`;
- (B) fiber ⊆ {both candidates} — uses path-lift RS1;
- (C) candidates coincide ↔ unbalanced — RS2.

Then `φ : Bool → fiber, b ↦ candidateLift v₀ b` is surjective always;
injective iff balanced; constant iff unbalanced. Card = 2 or 1.

## New helpers
`candidateLift`, `coverProj_apply`, `componentProj_candidateLift`,
`reachable_to_rep_sheet` (RS1, sorry), `fiber_subset_candidates`,
`sheets_merge_iff_unbalanced` (RS2, sorry),
`componentProj_fiber_card_candidate` (closed modulo RS1+RS2).

## Residual sorries

**RS1 path-lift.** Helper
`∃ b', Nonempty (coverGraph.Walk (u, b) (v, b'))`; induction on base
walk, `cons h q` case computes next sheet from wrap of `h`, recurses,
prepends.

**RS2 balanced ↔ separated.**
- `→`: invariant `f (u, c) := ε u != c` constant on cover-edges;
  distinguishes `(v₀, false)`, `(v₀, true)`.
- `←`: sheets separated implies `ε u := parity of any v₀ ⇝ u walk`
  is well-defined and satisfies the balanced axiom.

## Cross-check vs. `critic_report.md`
- §5 fiber ≤ 2 matches our `fiber_subset_candidates`.
- §8 primary gap matches RS1/RS2.
- §1 ε scope: extend ε arbitrarily off `C`; noted.
- §9 DecidableEq: neutralised by `classical`.

## Risks
- `coverProj_apply := rfl` via RelHom/FunLike; fallback
  `simp [coverProj]`.
- `Fintype.card Bool = 2` via `decide`.
- `Unique.mk'` in `Mathlib/Logic/Unique.lean:23`.
- Top-level `open SimpleGraph`; live source may need the same.

## sorry / sorryAx grep
`rg sorry|sorryAx|admit actor_proof.lean` → two sorries (lines 100,
177), both named `RS1`, `RS2` with sketches. No hidden sorries in
helper `have` terms. `componentProj_fiber_card_candidate` is sorry-free
as its own tactic block and closes the target once RS1+RS2 close.
