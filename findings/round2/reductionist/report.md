# Reductionist Round 2 Report

Target: close T1 / T2 / T3 by citation, not by bespoke proof. Mathlib scanned at `.lake/packages/mathlib/Mathlib/`.

## Top-line summary

- **Mathlib has no signed-graph, gain-graph, graph-cover, or balanced-component library.** Grep for `SignedGraph|GainGraph|signedLaplacian` empty; `cover|Cover` in `Combinatorics/SimpleGraph` only hits `Hasse.lean` (order theory, not graph covers).
- The only directly relevant mathlib theorem is the scalar Laplacian kernel-dim theorem.

Key Mathlib anchor:
`Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean:189` — `SimpleGraph.card_ConnectedComponent_eq_rank_ker_lapMatrix`.

---

## T1 — `scalarLap_cover_splits`

**Mathlib lemmas that apply:**
- `Matrix.mul_kronecker_mul` — `Data/Matrix/Kronecker.lean:345`.
- `Matrix.kroneckerMap_one_one` (`:132`), `Matrix.one_kronecker_one` (`:331`), `Matrix.inv_kronecker` (`:397`).
- `Matrix.det_reindex_self` — `LinearAlgebra/Matrix/Determinant/Basic.lean:235`.
- `Matrix.fromBlocks_apply₁₁..₂₂` — `Data/Matrix/Block.lean:46-62`.
- `Matrix.reindex_apply`, `Matrix.submatrix_apply` — standard.

`Mathlib/Data/Matrix/Hadamard.lean` is Hadamard *product*, not Hadamard *matrix*. 2×2 Hadamard built locally.

**Literature.** Chung §1.5; Bilu-Linial 2006; Zaslavsky 1982 Thm 5.1.

**Close by citing?** **No.** Bespoke 4-block entrywise identity under non-trivial reindex. Best shape: `ext ⟨i,b⟩ ⟨j,c⟩; fin_cases b <;> fin_cases c <;> simp [coverAdj, ...]`.

**Effort saved:** ~15%.

---

## T2 — `scalarLap_cover_kernel_dim`

**Mathlib lemmas that apply:**
- `LinearMap.ker_prodMap` — `LinearAlgebra/Prod.lean:287`.
- `Matrix.rank_reindex` — `Data/Matrix/Rank.lean:116`.
- `Submodule.finrank_prod` and rank-nullity.
- `LinearEquiv.conj` — `LinearAlgebra/Matrix/ToLin.lean:920`.

**Close by citing?** **Partially — and only given T1.** Given T1, T2 reduces to ~10 lines of plumbing: missing bridge `toLin'_fromBlocks_eq_prodMap` plus `ker_prodMap` plus `finrank_prod` plus similarity-invariance.

**Recommendation: prove T2 from T1 rather than independently.** Standalone it is as hard as T1.

**Effort saved:** ~60% when T1 is in hand.

**Mathlib gap:** `Matrix.toLin'_fromBlocks : (fromBlocks A 0 0 D).toLin' = A.toLin'.prodMap D.toLin'`.

---

## T3 — `componentProj_fiber_card`

**Mathlib lemmas that apply:**
- `SimpleGraph.ConnectedComponent.map` — `Path.lean:871`.
- `ConnectedComponent.map_mk` (`:876`), `.ind` (`:806`), `.exists` (`:845`), `.lift` (`:835`).
- `ConnectedComponent.eq`, `SimpleGraph.Walk.map`, `SimpleGraph.Iso.reachable_iff`.
- `Fintype.card_congr`, `Fintype.card_eq_one_iff`, `Fintype.card_eq_two_iff`.

**Literature.** Zaslavsky 1982 Thm 3.2: for a connected signed graph, orientation double cover disconnected iff balanced. Cvetković-Doob-Sachs 1980 §1.3; Chung §8.1. **Not in Mathlib.**

**Close by citing?** **No.** Mathlib has no cover/balanced/double-cover API. Must be built from scratch: define ε from spanning-tree wrap-parity; show `(v,false) ⇝ (v,true)` iff some closed walk has odd wrap-count iff C unbalanced.

**Effort saved:** ~5%. Eliminators only.

**Mathlib gaps (worth upstreaming):**
1. `SimpleGraph` covers / Galois covers / deck group.
2. Balanced / 2-colouring characterisation.
3. `ConnectedComponent.map` fiber cardinality under a covering map.

---

## Overall verdict

- Mathlib saves essentially **only plumbing**.
- Mathematical nuclei of T1 and T3 are unique to the Zaslavsky setting and **absent** from Mathlib.
- **Strongest leverage:** derive T2 from T1 (~60% saving).
- T1 is ~15% mechanized by Kronecker + reindex; T3 is ~5% by ConnectedComponent eliminators.
- No target reduces to a single Mathlib invocation.
