# Adversarial report — `scalarLap_cover_kernel_dim` strategy

Target: `ConnectionLaplacian/L5_Cover.lean:199-205`.
Strategy audited: `kerCoverEquiv` via `symProj`/`antiProj` + `combine (g,h) (v,b) = if b then g v − h v else g v + h v`.

## Numerical sanity: PASSES

Concrete tests (SymPy/numpy) on K2-wrap and C3-one-wrap:
- K2 wrap: dim ker coverLap=2, scalarLap=1, signedLapMob=1. 2=1+1. OK.
- C3 one wrap: 1=1+0. OK (`signedLapMob` has det 4, so ker=0).
- Every `f ∈ ker(coverLap)` tested produces `scalarLap (symProj f)=0` AND `signedLapMob (antiProj f)=0`. Signs/scales in `combine` are self-consistent: `symProj(combine g h)=g`, `antiProj(combine g h)=h`, and `combine(symProj f)(antiProj f)=f`.

No counterexample found. All cracks are formalization-level.

## Formalization cracks (severity-ordered)

### C1 [HIGH]. `signedLaplacianMobius_toLin'_apply_eq_zero_iff` must be proved from scratch.
Actor treats this as an off-the-shelf signed analogue of Mathlib's `SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_adj`. It is NOT in Mathlib. Mathlib derives its version via `posSemidef_lapMatrix` + `PosSemidef.toLinearMap₂'_zero_iff`. For the signed matrix the required PSD form is
`⟨x, L_sign x⟩ = Σ_{non-wrap edges} (x u − x v)² + Σ_{wrap edges} (x u + x v)²`.
Neither the symmetry nor the PSD decomposition exists in the project. Porting Mathlib's proof requires rederiving (a) symmetry, (b) PSD witness, (c) edge-by-edge quadratic-form expansion with wrap/non-wrap split. Estimate: ~80 proof lines.

### C2 [MED]. `G.orientationDoubleCover.scalarLaplacian = G.coverGraph.lapMatrix ℝ` is not obviously `rfl`.
Both defs are `noncomputable`, creating reducibility barriers under `rfl`. Expect `show _ = _; rfl` or explicit `unfold`.

### C3 [MED]. `DecidableEq` instance mismatch hazard.
`toLin' M` requires `DecidableEq` on the column index. Project synthesizes `DecidableEq G.CoverV` via `unfold CoverV; infer_instance`. Kernel rewrites may synthesize two non-defeq `DecidableEq (G.V × Bool)` instances. Latent `convert`/`congr` tax.

### C4 [LOW-MED]. Linear-structure bookkeeping is voluminous.
`symProj`, `antiProj`, `combine` each need `map_add` + `map_smul` (6 lemmas). Composites with `/2` scale factors reduce via `ring`/`field_simp` but ~8 distinct equations. Estimate ~80-120 lines for `LinearEquiv` scaffolding.

### C5 [MED]. Cover-adjacency decoding to base-edge conditions is combinatorially deep.
Applying `lapMatrix_toLin'_apply_eq_zero_iff_forall_adj` on `coverGraph` yields `∀ (u,b)(v,c), G.coverAdj (u,b) (v,c) → f(u,b)=f(v,c)`. `coverAdj` unfolds to `dif_pos`/`dif_neg` on `Adj u v`, further depends on `G.wrap ⟨s(u,v), _⟩`. Extracting the four facts `f(u,F)=f(v,F)`, `f(u,T)=f(v,T)` (non-wrap) / `f(u,F)=f(v,T)`, `f(u,T)=f(v,F)` (wrap) requires case-splits on `b,c,wrap`. Doubled for forward/reverse. Estimate ~160 lines.

### C6 [NOTE, not a crack]. Sign convention consistency.
`combine (v,false)=g v + h v, combine (v,true)=g v − h v`. Composites verify symbolically.

## Estimated gap

The theorem is NOT "3 lines from `kerCoverEquiv`" — `kerCoverEquiv` itself is ~300–400 lines:
- PSD / kernel-iff lemma for signedLapMob (C1): ~80
- Combinatorial kernel split forward+reverse (C5): ~160
- LinearMap bookkeeping (C4): ~80
- Type-plumbing / DecidableEq friction: ~20

The single `sorry` in `actor_proof.lean:92` understates the work by ~100× (one sorry hiding ~300+ lines).

## Recommendation

Prove C1 (`signedLaplacianMobius_toLin'_apply_eq_zero_iff`) FIRST as a standalone lemma in `KernelDimension.lean`. It also unlocks the L8 signed-kernel-dim path. After that, `kerCoverEquiv` is feasible but still sizeable.

Key file paths:
- `ConnectionLaplacian/L5_Cover.lean:147-205` (targets, symProj/antiProj)
- `ConnectionLaplacian/KernelDimension.lean:66-80` (scalarLap, signedLapMob defs)
- `.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean:100-123` (template to port for C1)
- `findings/s1_cover_ker_dim/actor_proof.lean:75-92` (the disputed single-sorry `kerCoverEquiv`)
