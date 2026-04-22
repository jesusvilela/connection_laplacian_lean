# Critic report — `scalarLap_cover_kernel_dim` + meta-audit of `numComponents_cover`

Scope audited:
- `ConnectionLaplacian/L5_Cover.lean` lines 191–207 (target statement)
- `ConnectionLaplacian/L6_Cohomology.lean` lines 104–148 (meta-audit)
- Supporting: `Basic.lean`, `KernelDimension.lean`

## Target statement findings

1. **Mathematical truth — CLEAN under checked cases.** Traced empty / single-vertex / K2 non-wrap / K2 wrap / K3 all-wrap / K3 one-wrap. In every case LHS = RHS. The statement is equivalent (via Mathlib's `card_CC_eq_rank_ker_lapMatrix` on G̃) to `dim ker signedLapMob = numBalancedComponents`, which is the L8 recognition theorem and is expected to hold on every `ConnGraph`. **No counterexample found under scope: all `ConnGraph G` with finite `G.V`.**
   - File: `L5_Cover.lean:198-204` — severity: clean (statement).

2. **Missing `Nonempty G.V` is a non-issue.** `Basic.lean:57-64` does NOT require `Nonempty V`. Empty-V case: all three kernels are 0-dim, `0 = 0 + 0` holds. Severity: clean.

3. **Proof-route hazard (smell).** The docstring at `L5_Cover.lean:184-197` advertises deriving the statement from `scalarLap_cover_splits` (itself `sorry` at :182) via "rank_reindex + similarity-invariance + block-diagonal kernel decomposition." But `scalarLap_cover_splits` gives `P * L̃ * P⁻¹` reindexed, which only preserves kernel dim if `P` is invertible (OK, `P.det ≠ 0`) AND if one then invokes a lemma of shape `finrank (ker (toLin' (fromBlocks A 0 0 B))) = finrank (ker (toLin' A)) + finrank (ker (toLin' B))` — this is not cited in Mathlib imports of L5/KernelDim and must be produced. Severity: smell.

4. **`DecidableEq` trap (crack-lite).** `toLin' M` needs `DecidableEq` on the index of `M`'s columns. For `G.orientationDoubleCover.scalarLaplacian`, the index is `G.CoverV`. Instance at `L5_Cover.lean:50-51` is by `unfold CoverV; infer_instance`. Fine at call site, but any attempt to manipulate via `prodBoolEquivSum` reindex will introduce `DecidableEq (G.V ⊕ G.V)` obligations and a second, possibly non-defeq, `DecidableEq (G.V × Bool)` instance produced via `Equiv.decidableEq`. Severity: smell.

5. **`signedLaplacianMobius` symmetry not proved here.** `KernelDimension.lean:74-80` defines it but no `IsSymm` lemma exists for it in isolation (only `laplacian_symmetric` for the *block* Laplacian). `toLin'` does not require symmetry, so the statement still types — but any spectral-theorem step needs symmetry. Severity: smell (risk for the proof, not the statement).

6. **Universe level.** `G.V : Type*` (universe-polymorphic in `ConnGraph`). `G.CoverV := G.V × Bool` stays at the same level. No universe issue detected. Severity: clean.

## Meta-audit of `numComponents_cover` (L6:119-148)

7. **CRACK: depends on a `sorry`.** `numComponents_cover` calls `G.componentProj_fiber_card` at line 137, which is `sorry` at `L6_Cohomology.lean:108`. The theorem therefore is NOT actually closed — Lean will accept the proof only because the `sorry` lives in the dependency. Severity: **crack** (the claim "recently closed, no sorry" is false).

8. **Sigma bijection direction — CLEAN.** Toward `Σ C, {D // projD = C}`: `D ↦ ⟨projD, D, rfl⟩`; inverse `⟨_,D,_⟩ ↦ D`. `right_inv` uses `subst hDC; rfl`. Direction and equations check out. File: `L6_Cohomology.lean:125-134`.

9. **`simp_rw [componentProj_fiber_card]` target — CLEAN.** After `Fintype.card_sigma`, goal has shape `∑ C, Fintype.card {D // projD = C}`. The lemma's LHS matches exactly, producing `∑ C, if isBalanced C then 2 else 1`.

10. **`Finset.sum_boole` final match — SMELL.** Mathlib's `Finset.sum_boole` (Ring.lean:32) states `∑ x ∈ s, (if p x then 1 else 0) = (s.filter p).card`. After `Fintype.card_subtype` + `← sum_boole` the goal is syntactically `∑ C, (if isBalanced C then 1 else 0) = ∑ C, (if isBalanced C then 1 else 0)` — but the two occurrences use different `DecidablePred` instances: one from `decIsBalanced` (`Classical.dec`, `L6:57-58`) and one synthesized by `Finset.sum_boole`'s `[DecidablePred p]` binder (also `Classical.dec` via classical inference). These are defeq up to proof irrelevance of `Decidable` in `Prop`, and the `rfl` at line 148 succeeds — but it is close to the edge; any future refactor that makes one instance `decide`-based will break the `rfl`. Severity: smell.

11. **Coerced `1` in `sum_const`.** Line 144: `Finset.sum_const` produces `s.card • c`; here `c = 1 : ℕ`, giving `s.card • 1`. `smul_eq_mul` + `mul_one` close it. CLEAN, but note the `• 1` would break for a non-semiring codomain. Not applicable here (ℕ).

## Counterexample

No counterexample found to `scalarLap_cover_kernel_dim` under scope: arbitrary `G : ConnGraph` with finite `G.V` and arbitrary `wrap : edgeSet → Prop`. Hand-checked: empty, single-vertex, K2 (both wrap modes), K3 (zero/one/three wrap edges). All satisfy LHS = RHS.
