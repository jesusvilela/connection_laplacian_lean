# ADVERSARIAL-SPLITS Round 3 — Audit of `ConnGraph.scalarLap_cover_splits`

**Target:** `L5_Cover.lean:548–583` (statement + proof). Supporting: `KernelDimension.lean`.

## Summary verdict

No counterexample found, no step computes the wrong value. Proof architecture is correct:
- Hadamard convention is self-consistent with `scalarLaplacian`/`signedLaplacianMobius`
- `Pcov² = 2·I` is the only fact used about `Pcov` beyond `Pcov_apply`
- Four terminal `ring` closers reduce to trivial real equalities

## Concern 1 — Typeclass synthesis (ROBUST, style wart)

- `Fintype G.CoverV` at L5:47 declared `noncomputable` though `G.V × Bool` admits computable Fintype. Superfluous; not a bug.
- `DecidableEq G.CoverV` (L50), `DecidableRel G.coverAdj` (L62), `DecidableRel G.coverGraph.Adj` (L107): rely on manual `unfold` + `infer_instance` because `CoverV`/`coverAdj` are `def`s not `abbrev`s. Fragile to refactor.
- `orientationDoubleCover.wrap := fun _ => False`: bundled `DecidablePred` works via core `Decidable False`.

## Concern 2 — Defeq CoverV ↔ orientationDoubleCover.V (ROBUST, ergonomics wart)

`orientationDoubleCover.V := G.CoverV` at L113 is rfl-defeq. `show Matrix G.CoverV G.CoverV ℝ from G.orientationDoubleCover.scalarLaplacian` at L552 passes elaborator defeq check.

**POTENTIAL WEAKNESS** (ergonomics): Downstream consumers must `change hreindex` to strip the `show` before `rw`. Already handled at L608-610 in `scalarLap_cover_kernel_dim`. Minor usability wart.

## Concern 3 — Symmetry of wrap / coverAdj_symm (ROBUST)

`coverAdj_symm` bridges via `Subtype.ext; exact Sym2.eq_swap` (L74-75). All `coverAdj_iff` callsites consistent with wrap hypothesis orientation `⟨s(u,v), …⟩`. No orientation confusion.

## Concern 4 — Empty / small graph edge cases (ROBUST)

- |V|=0: matrices empty, `Pcov = 1`, det=1, `ext` vacuous.
- |V|=1, |E|=0: `CoverV` has 2 elements, no edges, `Pcov = RhatBool`.
- |V|≥2, |E|=0: `covBlock_nonadj` for u≠v. Both Laplacians zero.

## Concern 5 — Four terminal ring calls (ROBUST)

| Branch | Goal |
|--------|------|
| inl,inl | (1/2)*(2*scalarLap u v) = scalarLap u v |
| inl,inr | (1/2)*0 = 0 |
| inr,inl | (1/2)*0 = 0 |
| inr,inr | (1/2)*(2*signedLap u v) = signedLap u v |

All trivial. No `-0`/`0` subtlety: `0` comes from `rotated_entry`'s `else 0` = literal `(0 : ℝ)`. Off-diagonal blocks produce `(0 : Matrix G.V G.V ℝ) u v` → `Matrix.zero_apply`.

## Concern 6 — Hadamard convention (ROBUST, load-bearing)

Current: `RhatBool true true = -1`, others = 1. Column indexed by `false` → scalar Laplacian; `true` → signed Laplacian.

Verified wrap edge u≠v: `RhatBool * wrapOffMat * RhatBool = [[-2,0],[0,2]]`. Matches 2·scalarLap and 2·signedLap under wrap convention.

`prodBoolEquivSum.symm (inl w) = (w, false)` (L562 rfl), so `inl` ↔ `false` sheet ↔ scalar Laplacian = top-left block. Consistent.

**POTENTIAL WEAKNESS:** Convention `false ↔ scalar, true ↔ signed` is distributed across `RhatBool`, `prodBoolEquivSum`, `rotated_entry`. No single lemma pins it. Refactoring any one requires re-checking the other two. Recommend alignment lemma or comment near `RhatBool`.

## Concern 7 — L̃ invariance under Sym2 swap (ROBUST)

`G.wrap` on subtype `edgeSet`; `Sym2.eq_swap` + proof-irrelevant `Subtype.ext` give representative-independence.

## Additional checks (all ROBUST)

- Extra 8: `Pcov_det_ne_zero` via `det(Pcov·(1/2)Pcov) = 1`.
- Extra 9: Nested-sum rewrites via `Finset.sum_eq_single`.
- Extra 10: `reindex_apply`/`submatrix_apply` are rfl-lemmas.
- Extra 11: `Matrix.mul_smul` orientation correct.

## Hand-verified counterexample attempts (all passed)

1. K₂ with 1 wrap edge: conjugation gives `fromBlocks [[1,-1],[-1,1]] 0 0 [[1,+1],[+1,1]]`. ✓
2. P₃ no wrap: cover is two disjoint P₃'s. ✓
3. K₃ all-wrap: cover is 6-cycle. ✓

## Unverified future risks

- `ring` timeout if Mathlib unfolds `signedLaplacianMobius`/`scalarLaplacian`. Mitigation: use `rfl` or `linarith`.
- `Matrix.mul_smul` renaming could break L558 rewrite.

## Final classification

- **CONFIRMED BUGS:** None.
- **POTENTIAL WEAKNESSES:** 2 (ergonomic/refactor fragility, not soundness):
  - 2.1: `show ... from ...` cast forces downstream `change`.
  - 6.1: Hadamard ↔ scalar/signed convention implicit across three defs.
- **ROBUST:** 7/7 main concerns + 4 extras.

Proof is mathematically and Lean-syntactically sound under current pinned Mathlib. No bug produces wrong statement; no case in four-way split can be broken by an adversarial input satisfying ConnGraph invariants.
