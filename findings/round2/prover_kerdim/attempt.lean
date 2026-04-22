/-
findings/round2/prover_kerdim/attempt.lean

Direct proof of `ConnectionLaplacian.ConnGraph.scalarLap_cover_kernel_dim`
via an explicit linear equivalence

  kerCoverEquiv : ker(toLin' L̃) ≃ₗ[ℝ] ker(toLin' L_scalar) × ker(toLin' L_signed)

built from the deck-symmetrization/antisymmetrization projections
`symProj`, `antiProj`, paired with the combine map
`(g, h) ↦ fun (v, b) ↦ g v + (if b then -h v else h v)`.

We do NOT depend on `scalarLap_cover_splits` (still `sorry` in L5).

**Residual sorry**: one helper, `signedLap_toLin'_apply_eq_zero_iff`,
stating that the signed Laplacian annihilates `x` iff the adjacency
sign condition holds on every base edge. This is the signed analogue
of Mathlib's `SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_adj`
and requires PSD-ness + quadratic-form computation that we have not
completed here.

All other pieces are closed.
-/

import ConnectionLaplacian.L5_Cover

namespace ConnectionLaplacian

open Matrix BigOperators
open scoped Kronecker

namespace ConnGraph

variable (G : ConnGraph)

/-! ### Cover-adjacency unfolding. -/

private lemma coverAdj_nonwrap_same {u v : G.V} (hadj : G.graph.Adj u v)
    (hnw : ¬ G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩) :
    G.coverGraph.Adj (u, false) (v, false) ∧ G.coverGraph.Adj (u, true) (v, true) := by
  refine ⟨?_, ?_⟩ <;>
  · show G.coverAdj _ _
    unfold coverAdj
    rw [dif_pos hadj]
    simp [hnw]

private lemma coverAdj_wrap_flip {u v : G.V} (hadj : G.graph.Adj u v)
    (hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩) :
    G.coverGraph.Adj (u, false) (v, true) ∧ G.coverGraph.Adj (u, true) (v, false) := by
  refine ⟨?_, ?_⟩ <;>
  · show G.coverAdj _ _
    unfold coverAdj
    rw [dif_pos hadj]
    simp [hw]

/-! ### Combine helper. -/

/-- Combine two base-graph functions into a cover function:
`combine g h (v, false) = g v + h v`, `combine g h (v, true) = g v - h v`. -/
noncomputable def combineCover (g h : G.V → ℝ) : G.CoverV → ℝ :=
  fun (vb : G.CoverV) => g vb.1 + (if vb.2 then -h vb.1 else h vb.1)

private lemma combine_apply_false (g h : G.V → ℝ) (v : G.V) :
    G.combineCover g h (v, false) = g v + h v := by
  unfold combineCover; simp

private lemma combine_apply_true (g h : G.V → ℝ) (v : G.V) :
    G.combineCover g h (v, true) = g v - h v := by
  unfold combineCover; simp [sub_eq_add_neg]

/-! ### Linearity of projections. -/

private lemma symProj_add (f₁ f₂ : G.CoverV → ℝ) :
    G.symProj (f₁ + f₂) = G.symProj f₁ + G.symProj f₂ := by
  funext v; simp [symProj, Pi.add_apply]; ring

private lemma symProj_smul (c : ℝ) (f : G.CoverV → ℝ) :
    G.symProj (c • f) = c • G.symProj f := by
  funext v; simp [symProj, Pi.smul_apply, smul_eq_mul]; ring

private lemma antiProj_add (f₁ f₂ : G.CoverV → ℝ) :
    G.antiProj (f₁ + f₂) = G.antiProj f₁ + G.antiProj f₂ := by
  funext v; simp [antiProj, Pi.add_apply]; ring

private lemma antiProj_smul (c : ℝ) (f : G.CoverV → ℝ) :
    G.antiProj (c • f) = c • G.antiProj f := by
  funext v; simp [antiProj, Pi.smul_apply, smul_eq_mul]; ring

/-! ### The residual helper: signed Laplacian zero-kernel characterization.

Proof strategy via PSD quadratic form.

**Quadratic form identity** (proved by Finset sum rearrangement):
  2 · x ⬝ᵥ (L_sgn *ᵥ x) =
    ∑_{u,v} adj uv non-wrap (x u - x v)² + ∑_{u,v} adj uv wrap (x u + x v)²
(as a sum over ordered pairs).

This is ≥ 0, so `L_sgn` is PSD. Then by `PosSemidef.toLinearMap₂'_zero_iff`,
`L_sgn x = 0 ↔ x^T L_sgn x = 0`. The RHS vanishes iff each squared term is
zero, i.e. the signed adjacency condition holds. -/

/-- Signed Laplacian entry: diagonal = degree; off-diagonal adj non-wrap = -1,
adj wrap = +1, non-adj = 0. -/
private lemma signedLap_entry (u v : G.V) :
    G.signedLaplacianMobius u v =
      (if u = v then (G.graph.degree u : ℝ) else 0)
      - (if h : G.graph.Adj u v then
            (if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ then -1 else 1)
         else 0) := by
  unfold signedLaplacianMobius SimpleGraph.degree
  by_cases huv : u = v
  · subst huv
    have hnoadj : ¬ G.graph.Adj u u := SimpleGraph.irrefl _
    simp [hnoadj]
  · simp [huv]
    by_cases hadj : G.graph.Adj u v
    · simp [hadj]
      by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
      · simp [hw]
      · simp [hw]
    · simp [hadj]

/-- Quadratic-form identity for the signed Laplacian.

**DEFERRED (residual sorry).** The identity
  2 · x^T L_sgn x = ∑_u ∑_v (if adj u v then (wrap ? (xu+xv)² : (xu-xv)²) else 0)
is the signed analogue of Mathlib's `lapMatrix_toLinearMap₂'` with a
wrap-edge sign flip. Proof outline:
  1. Expand LHS via `signedLap_entry`: split diagonal (= 2 ∑ deg u · x u²)
     from off-diagonal (= -2 ∑_{non-wrap} xu xv + 2 ∑_{wrap} xu xv).
  2. Expand RHS: (xu ± xv)² = xu² + xv² ± 2 xu xv.
  3. ∑_{u,v adj} (xu² + xv²) = 2 ∑_u deg u · xu² (swap symmetry + degree identity).
  4. Cross terms match by sign.
Full formalization follows Mathlib's pattern but with extra `dif` machinery
for the wrap predicate; deferred here. -/
private lemma signedLap_quadForm (x : G.V → ℝ) :
    (2 : ℝ) * dotProduct x (G.signedLaplacianMobius *ᵥ x) =
      ∑ u : G.V, ∑ v : G.V,
        if h : G.graph.Adj u v then
          if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
          then (x u + x v)^2 else (x u - x v)^2
        else 0 := by
  sorry

/-- The signed Laplacian is symmetric. -/
private lemma signedLap_isSymm : G.signedLaplacianMobius.IsSymm := by
  ext u v
  unfold signedLaplacianMobius
  by_cases huv : u = v
  · subst huv; simp
  · have hvu : v ≠ u := Ne.symm huv
    rw [Matrix.transpose_apply]
    simp only [if_neg huv, if_neg hvu]
    by_cases hadj : G.graph.Adj u v
    · have hadj' : G.graph.Adj v u := hadj.symm
      rw [dif_pos hadj, dif_pos hadj']
      have hedge_eq :
          (⟨s(v, u), (SimpleGraph.mem_edgeSet G.graph).mpr hadj'⟩ :
              G.graph.edgeSet)
            = ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩ := by
        apply Subtype.ext; exact Sym2.eq_swap
      rw [hedge_eq]
    · have hnadjvu : ¬ G.graph.Adj v u := fun h => hadj h.symm
      rw [dif_neg hadj, dif_neg hnadjvu]

/-- The signed Laplacian is positive semidefinite. -/
private lemma signedLap_posSemidef : G.signedLaplacianMobius.PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- Hermitian (= symmetric for real)
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact G.signedLap_isSymm
  · intro x
    rw [star_trivial]
    -- 2 * (x ⬝ᵥ Lx) ≥ 0 → x ⬝ᵥ Lx ≥ 0
    have hq := G.signedLap_quadForm x
    have hnn : (0 : ℝ) ≤ ∑ u : G.V, ∑ v : G.V,
        if h : G.graph.Adj u v then
          if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
          then (x u + x v)^2 else (x u - x v)^2
        else 0 := by
      apply Finset.sum_nonneg
      intros u _
      apply Finset.sum_nonneg
      intros v _
      split_ifs <;> positivity
    linarith

/-- Zero-kernel characterization for the signed Laplacian. -/
private lemma signedLap_toLin'_apply_eq_zero_iff (x : G.V → ℝ) :
    Matrix.toLin' G.signedLaplacianMobius x = 0 ↔
      ∀ u v : G.V, ∀ (h : G.graph.Adj u v),
        (if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
          then x u = -(x v) else x u = x v) := by
  rw [← G.signedLap_posSemidef.toLinearMap₂'_zero_iff]
  rw [star_trivial, Matrix.toLinearMap₂'_apply']
  -- ⇐ x ⬝ᵥ (L_sgn *ᵥ x) = 0 ↔ adjacency conditions
  -- Use the quadratic-form identity.
  have hq := G.signedLap_quadForm x
  constructor
  · intro hz u v hadj
    -- From x ⬝ᵥ (L_sgn *ᵥ x) = 0, deduce 2 · 0 = 0, so quadratic form = 0.
    have h2 : (2 : ℝ) * dotProduct x (G.signedLaplacianMobius *ᵥ x) = 0 := by
      rw [hz]; ring
    rw [hq] at h2
    -- Each summand is nonneg
    have hnn_each : ∀ u v : G.V, (0 : ℝ) ≤
        (if h : G.graph.Adj u v then
          if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
          then (x u + x v)^2 else (x u - x v)^2
        else 0) := by
      intros; split_ifs <;> positivity
    have hnn_sum_v : ∀ u : G.V, (0 : ℝ) ≤ (∑ v : G.V,
        (if h : G.graph.Adj u v then
          if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩
          then (x u + x v)^2 else (x u - x v)^2
        else 0)) := by
      intro u; apply Finset.sum_nonneg; intros; exact hnn_each _ _
    -- From h2, outer sum = 0, so each inner sum = 0
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun u _ => hnn_sum_v u)] at h2
    have hinner_u := h2 u (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hnn_each u v)] at hinner_u
    have := hinner_u v (Finset.mem_univ _)
    rw [dif_pos hadj] at this
    by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
    · rw [if_pos hw] at this
      rw [if_pos hw]
      have hxv : x u + x v = 0 := sq_eq_zero_iff.mp this
      linarith
    · rw [if_neg hw] at this
      rw [if_neg hw]
      have hxv : x u - x v = 0 := sq_eq_zero_iff.mp this
      linarith
  · intro hcond
    -- If the adjacency conditions hold, the quadratic form vanishes.
    have h2 : (2 : ℝ) * dotProduct x (G.signedLaplacianMobius *ᵥ x) = 0 := by
      rw [hq]
      apply Finset.sum_eq_zero
      intros u _
      apply Finset.sum_eq_zero
      intros v _
      by_cases hadj : G.graph.Adj u v
      · rw [dif_pos hadj]
        have := hcond u v hadj
        by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
        · rw [if_pos hw] at this ⊢; rw [this]; ring
        · rw [if_neg hw] at this ⊢; rw [this]; ring
      · rw [dif_neg hadj]
    linarith

/-! ### Kernel closure: the three core lemmas. -/

private lemma symProj_mem_ker_of_cover (f : G.CoverV → ℝ)
    (hf : Matrix.toLin' G.orientationDoubleCover.scalarLaplacian f = 0) :
    Matrix.toLin' G.scalarLaplacian (G.symProj f) = 0 := by
  have hcov : G.orientationDoubleCover.scalarLaplacian = G.coverGraph.lapMatrix ℝ := rfl
  rw [hcov] at hf
  rw [SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_adj] at hf
  show Matrix.toLin' (G.graph.lapMatrix ℝ) (G.symProj f) = 0
  rw [SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_adj]
  intro u v hadj
  by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
  · obtain ⟨h1, h2⟩ := G.coverAdj_wrap_flip hadj hw
    have e1 : f (u, false) = f (v, true) := hf _ _ h1
    have e2 : f (u, true) = f (v, false) := hf _ _ h2
    simp [symProj, e1, e2]; ring
  · obtain ⟨h1, h2⟩ := G.coverAdj_nonwrap_same hadj hw
    have e1 : f (u, false) = f (v, false) := hf _ _ h1
    have e2 : f (u, true) = f (v, true) := hf _ _ h2
    simp [symProj, e1, e2]

private lemma antiProj_mem_ker_of_cover (f : G.CoverV → ℝ)
    (hf : Matrix.toLin' G.orientationDoubleCover.scalarLaplacian f = 0) :
    Matrix.toLin' G.signedLaplacianMobius (G.antiProj f) = 0 := by
  have hcov : G.orientationDoubleCover.scalarLaplacian = G.coverGraph.lapMatrix ℝ := rfl
  rw [hcov] at hf
  rw [SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_adj] at hf
  rw [G.signedLap_toLin'_apply_eq_zero_iff]
  intro u v hadj
  by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
  · rw [if_pos hw]
    obtain ⟨h1, h2⟩ := G.coverAdj_wrap_flip hadj hw
    have e1 : f (u, false) = f (v, true) := hf _ _ h1
    have e2 : f (u, true) = f (v, false) := hf _ _ h2
    simp [antiProj, e1, e2]; ring
  · rw [if_neg hw]
    obtain ⟨h1, h2⟩ := G.coverAdj_nonwrap_same hadj hw
    have e1 : f (u, false) = f (v, false) := hf _ _ h1
    have e2 : f (u, true) = f (v, true) := hf _ _ h2
    simp [antiProj, e1, e2]

private lemma combine_mem_ker_cover (g h : G.V → ℝ)
    (hg : Matrix.toLin' G.scalarLaplacian g = 0)
    (hh : Matrix.toLin' G.signedLaplacianMobius h = 0) :
    Matrix.toLin' G.orientationDoubleCover.scalarLaplacian (G.combineCover g h) = 0 := by
  have hcov : G.orientationDoubleCover.scalarLaplacian = G.coverGraph.lapMatrix ℝ := rfl
  show Matrix.toLin' (G.coverGraph.lapMatrix ℝ) (G.combineCover g h) = 0
  rw [SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_adj]
  have hg' : ∀ i j : G.V, G.graph.Adj i j → g i = g j := by
    have hhh : Matrix.toLin' (G.graph.lapMatrix ℝ) g = 0 := hg
    rwa [SimpleGraph.lapMatrix_toLin'_apply_eq_zero_iff_forall_adj] at hhh
  have hh' := (G.signedLap_toLin'_apply_eq_zero_iff h).mp hh
  rintro ⟨u, b⟩ ⟨v, c⟩ hcovadj
  have hcovadj' : G.coverAdj (u, b) (v, c) := hcovadj
  unfold coverAdj at hcovadj'
  by_cases hadj : G.graph.Adj u v
  · rw [dif_pos hadj] at hcovadj'
    by_cases hw : G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
    · have hbc : b ≠ c := hcovadj'.mp hw
      have hgeq : g u = g v := hg' u v hadj
      have hhrel := hh' u v hadj
      rw [if_pos hw] at hhrel
      cases b <;> cases c
      · exact absurd rfl hbc
      · simp only [combineCover, if_true, if_false, Bool.false_eq_true]
        linarith
      · simp only [combineCover, if_true, if_false, Bool.false_eq_true]
        linarith
      · exact absurd rfl hbc
    · have hbc : b = c := by
        by_contra hne
        exact hw (hcovadj'.mpr hne)
      subst hbc
      have hgeq : g u = g v := hg' u v hadj
      have hhrel := hh' u v hadj
      rw [if_neg hw] at hhrel
      cases b <;> simp [combineCover, hgeq, hhrel]
  · rw [dif_neg hadj] at hcovadj'
    exact absurd hcovadj' id

/-! ### The linear equivalence. -/

noncomputable def kerCoverEquivFun :
    LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian) →
      LinearMap.ker (toLin' G.scalarLaplacian) ×
        LinearMap.ker (toLin' G.signedLaplacianMobius) :=
  fun f =>
    (⟨G.symProj f.1, by
        rw [LinearMap.mem_ker]
        exact G.symProj_mem_ker_of_cover f.1 (LinearMap.mem_ker.mp f.2)⟩,
     ⟨G.antiProj f.1, by
        rw [LinearMap.mem_ker]
        exact G.antiProj_mem_ker_of_cover f.1 (LinearMap.mem_ker.mp f.2)⟩)

noncomputable def kerCoverEquivInv :
    LinearMap.ker (toLin' G.scalarLaplacian) ×
      LinearMap.ker (toLin' G.signedLaplacianMobius) →
    LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian) :=
  fun p =>
    ⟨G.combineCover p.1.1 p.2.1, by
      rw [LinearMap.mem_ker]
      exact G.combine_mem_ker_cover p.1.1 p.2.1
        (LinearMap.mem_ker.mp p.1.2) (LinearMap.mem_ker.mp p.2.2)⟩

private lemma combine_sym_anti (f : G.CoverV → ℝ) (v : G.V) (b : Bool) :
    G.combineCover (G.symProj f) (G.antiProj f) (v, b) = f (v, b) := by
  cases b
  · rw [combine_apply_false]
    simp [symProj, antiProj]; ring
  · rw [combine_apply_true]
    simp [symProj, antiProj]; ring

noncomputable def kerCoverEquiv :
    LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian) ≃ₗ[ℝ]
      LinearMap.ker (toLin' G.scalarLaplacian) ×
      LinearMap.ker (toLin' G.signedLaplacianMobius) where
  toFun := G.kerCoverEquivFun
  invFun := G.kerCoverEquivInv
  map_add' := by
    intro f₁ f₂
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show G.symProj (f₁.1 + f₂.1) = G.symProj f₁.1 + G.symProj f₂.1
      exact G.symProj_add f₁.1 f₂.1
    · apply Subtype.ext
      show G.antiProj (f₁.1 + f₂.1) = G.antiProj f₁.1 + G.antiProj f₂.1
      exact G.antiProj_add f₁.1 f₂.1
  map_smul' := by
    intro c f
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show G.symProj (c • f.1) = c • G.symProj f.1
      exact G.symProj_smul c f.1
    · apply Subtype.ext
      show G.antiProj (c • f.1) = c • G.antiProj f.1
      exact G.antiProj_smul c f.1
  left_inv := by
    intro f
    apply Subtype.ext
    funext vb
    obtain ⟨v, b⟩ := vb
    exact G.combine_sym_anti f.1 v b
  right_inv := by
    intro p
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      funext v
      show G.symProj (G.combineCover p.1.1 p.2.1) v = p.1.1 v
      simp only [symProj, combineCover]; ring
    · apply Subtype.ext
      funext v
      show G.antiProj (G.combineCover p.1.1 p.2.1) v = p.2.1 v
      simp only [antiProj, combineCover]; ring

/-! ### The main theorem. -/

theorem scalarLap_cover_kernel_dim_candidate :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian)) =
      FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' G.scalarLaplacian)) +
      FiniteDimensional.finrank ℝ
          (LinearMap.ker (toLin' G.signedLaplacianMobius)) := by
  rw [LinearEquiv.finrank_eq G.kerCoverEquiv, FiniteDimensional.finrank_prod]

end ConnGraph

end ConnectionLaplacian
