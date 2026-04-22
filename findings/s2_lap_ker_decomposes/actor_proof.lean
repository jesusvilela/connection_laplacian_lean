/-
Candidate proof for `laplacian_kernel_dim_decomposes` (L8_Recognition.lean:85).

Scope: self-contained. Assumes only the existing theorem
`ConnGraph.laplacian_decomposes` (KernelDimension.lean:229) and Mathlib.

Strategy (three helper lemmas, then one-line assembly):
  (i)   `finrank_ker_toLin'_conj` — similarity by an invertible matrix
        preserves `finrank (ker (toLin' ·))`.
  (ii)  `finrank_ker_toLin'_reindex` — `reindex e e` preserves
        `finrank (ker (toLin' ·))`.
  (iii) `finrank_ker_toLin'_fromBlocks_diag` — for block-diagonal
        `fromBlocks A 0 0 B`, kernel finrank adds.

All helpers are stated over an arbitrary field and finite index types,
so they are reusable for the twin sorry in `L5_Cover.scalarLap_cover_kernel_dim`.

Drop-in target: paste the three helper lemmas (in the root namespace or
in `ConnectionLaplacian`) and the theorem body (everything after `by`)
of `laplacian_kernel_dim_decomposes` into `L8_Recognition.lean`, in
place of the current `sorry`. No other file needs to change.
-/

import ConnectionLaplacian.KernelDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Pi

namespace ConnectionLaplacian

open Matrix BigOperators FiniteDimensional

/-! ### Helper lemma (i) — similarity preserves `finrank (ker (toLin' ·))` -/

/-- Similarity by an invertible matrix preserves the kernel dimension.
Used here: the conjugated matrix `P * L * P⁻¹` (with `P.det ≠ 0`) has the
same `finrank` of kernel as `L`. -/
lemma finrank_ker_toLin'_conj
    {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (P L : Matrix n n K) (hP : P.det ≠ 0) :
    finrank K (LinearMap.ker (Matrix.toLin' (P * L * P⁻¹))) =
      finrank K (LinearMap.ker (Matrix.toLin' L)) := by
  have hPunit : IsUnit P.det := Ne.isUnit hP
  have hmul₁ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPunit
  have hmul₂ : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPunit
  -- Build the LinearEquiv induced by `P`.
  let e : (n → K) ≃ₗ[K] (n → K) :=
    LinearEquiv.ofLinear (Matrix.toLin' P) (Matrix.toLin' P⁻¹)
      (by
        -- toLin' P ∘ toLin' P⁻¹ = toLin' (P * P⁻¹) = toLin' 1 = id
        rw [← Matrix.toLin'_mul, hmul₁, Matrix.toLin'_one])
      (by
        rw [← Matrix.toLin'_mul, hmul₂, Matrix.toLin'_one])
  -- Factor `toLin' (P * L * P⁻¹)` as (toLin' P).comp ((toLin' L).comp (toLin' P⁻¹)).
  -- Both `e` and `e.symm` as linear maps are definitionally `toLin' P` and `toLin' P⁻¹`
  -- by the `ofLinear_toLinearMap` / `ofLinear_symm_toLinearMap` lemmas.
  have hfact :
      Matrix.toLin' (P * L * P⁻¹) =
        ((e : (n → K) →ₗ[K] (n → K))).comp
          ((Matrix.toLin' L).comp ((e.symm : (n → K) →ₗ[K] (n → K)))) := by
    show Matrix.toLin' (P * L * P⁻¹) =
      (Matrix.toLin' P).comp ((Matrix.toLin' L).comp (Matrix.toLin' P⁻¹))
    ext x
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply,
               ← Matrix.mulVec_mulVec]
  rw [hfact]
  -- Step A: `ker (e.comp g) = ker g` since `e` is a LinearEquiv.
  rw [LinearEquiv.ker_comp e]
  -- Step B: `ker (g.comp e.symm) = (ker g).comap e.symm`.
  rw [LinearMap.ker_comp]
  -- comap under e.symm = map under e.symm.symm = map under e.
  rw [Submodule.comap_equiv_eq_map_symm e.symm (LinearMap.ker (Matrix.toLin' L))]
  simp only [LinearEquiv.symm_symm]
  exact LinearEquiv.finrank_map_eq e (LinearMap.ker (Matrix.toLin' L))

/-! ### Helper lemma (ii) — `Matrix.reindex` preserves `finrank (ker (toLin' ·))` -/

/-- Reindexing via an equivalence on both sides preserves the kernel dimension. -/
lemma finrank_ker_toLin'_reindex
    {K : Type*} [Field K]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m K) :
    finrank K (LinearMap.ker (Matrix.toLin' (Matrix.reindex e e M))) =
      finrank K (LinearMap.ker (Matrix.toLin' M)) := by
  -- From Mathlib: `toLin' (reindex e e M) = funCongrLeft e.symm ∘ toLin' M ∘ funCongrLeft e`
  -- where both `funCongrLeft` are `LinearEquiv`s.
  -- Mathlib's toLin'_reindex gives the factorization explicitly.
  rw [Matrix.toLin'_reindex]
  -- Goal: finrank (ker ((funCongrLeft K K e.symm) ∘ₗ toLin' M ∘ₗ (funCongrLeft K K e)))
  --     = finrank (ker (toLin' M))
  -- Step A: `ker (LinearEquiv.comp g) = ker g`
  rw [LinearEquiv.ker_comp (LinearEquiv.funCongrLeft K K e.symm)]
  -- Step B: `ker (f.comp eL) = (ker f).comap eL`
  rw [LinearMap.ker_comp]
  -- comap under forward of a LinearEquiv = map under symm
  rw [Submodule.comap_equiv_eq_map_symm
    (LinearEquiv.funCongrLeft K K e) (LinearMap.ker (Matrix.toLin' M))]
  exact LinearEquiv.finrank_map_eq
    (LinearEquiv.funCongrLeft K K e).symm (LinearMap.ker (Matrix.toLin' M))

/-! ### Helper lemma (iii) — block-diagonal `fromBlocks A 0 0 B` -/

/-- For a block-diagonal matrix `fromBlocks A 0 0 B`, the kernel of the
corresponding linear map on `(ι ⊕ κ → K)` splits as a product of the
individual kernels, and so finrank adds. -/
lemma finrank_ker_toLin'_fromBlocks_diag
    {K : Type*} [Field K]
    {l m : Type*} [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m]
    (A : Matrix l l K) (B : Matrix m m K) :
    finrank K
        (LinearMap.ker (Matrix.toLin'
          (Matrix.fromBlocks A (0 : Matrix l m K) (0 : Matrix m l K) B))) =
      finrank K (LinearMap.ker (Matrix.toLin' A)) +
        finrank K (LinearMap.ker (Matrix.toLin' B)) := by
  -- Build an explicit LinearEquiv
  --   ker (toLin' (fromBlocks A 0 0 B)) ≃ₗ ker (toLin' A) × ker (toLin' B)
  set T : Matrix (l ⊕ m) (l ⊕ m) K :=
    Matrix.fromBlocks A (0 : Matrix l m K) (0 : Matrix m l K) B with hT_def
  -- Kernel characterisation.
  have hker_iff :
      ∀ x : l ⊕ m → K, x ∈ LinearMap.ker (Matrix.toLin' T) ↔
        (fun i => x (Sum.inl i)) ∈ LinearMap.ker (Matrix.toLin' A) ∧
        (fun j => x (Sum.inr j)) ∈ LinearMap.ker (Matrix.toLin' B) := by
    intro x
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    have hT_mulvec :
        T *ᵥ x =
          Sum.elim (A *ᵥ (fun i => x (Sum.inl i)))
                   (B *ᵥ (fun j => x (Sum.inr j))) := by
      rw [hT_def, Matrix.fromBlocks_mulVec]
      -- The `+ 0` and `0 *ᵥ _` terms vanish.
      ext i
      cases i with
      | inl i => simp [Matrix.zero_mulVec]
      | inr j => simp [Matrix.zero_mulVec]
    rw [hT_mulvec]
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · funext i
        have := congrFun hx (Sum.inl i)
        simpa using this
      · funext j
        have := congrFun hx (Sum.inr j)
        simpa using this
    · rintro ⟨hA, hB⟩
      ext i
      cases i with
      | inl i =>
          have := congrFun hA i
          simpa using this
      | inr j =>
          have := congrFun hB j
          simpa using this
  -- Build LinearEquiv ker (toLin' T) ≃ₗ ker (toLin' A) × ker (toLin' B).
  let kerEq :
      LinearMap.ker (Matrix.toLin' T) ≃ₗ[K]
        (LinearMap.ker (Matrix.toLin' A)) × (LinearMap.ker (Matrix.toLin' B)) :=
  { toFun := fun v =>
      (⟨fun i => v.1 (Sum.inl i), ((hker_iff v.1).mp v.2).1⟩,
       ⟨fun j => v.1 (Sum.inr j), ((hker_iff v.1).mp v.2).2⟩),
    map_add' := fun v w =>
      Prod.ext (by apply Subtype.ext; funext _; rfl)
               (by apply Subtype.ext; funext _; rfl),
    map_smul' := fun c v =>
      Prod.ext (by apply Subtype.ext; funext _; rfl)
               (by apply Subtype.ext; funext _; rfl),
    invFun := fun p =>
      ⟨Sum.elim p.1.1 p.2.1, by
        rw [hker_iff]
        exact ⟨p.1.2, p.2.2⟩⟩,
    left_inv := fun v => by
      apply Subtype.ext
      funext i
      rcases i with i | j <;> rfl,
    right_inv := fun p => by
      rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      -- Goal: (⟨fun i => Sum.elim a b (inl i), _⟩, ⟨fun j => Sum.elim a b (inr j), _⟩) = (⟨a,ha⟩, ⟨b,hb⟩)
      refine Prod.ext ?_ ?_
      · apply Subtype.ext; funext i; rfl
      · apply Subtype.ext; funext j; rfl }
  rw [kerEq.finrank_eq, FiniteDimensional.finrank_prod]

/-! ### Main assembly -/

namespace ConnGraph

variable (G : ConnGraph)

/-- **Kernel-dim corollary of `laplacian_decomposes`** (closes L8_Recognition line 92).

Proof: apply the three helper lemmas (similarity-invariance, reindex-invariance,
block-diagonal splitting) to the similarity/reindex identity from
`laplacian_decomposes`. -/
theorem laplacian_kernel_dim_decomposes (mobius : Bool) :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian mobius))) =
      FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' G.scalarLaplacian)) +
      FiniteDimensional.finrank ℝ
          (LinearMap.ker (toLin'
              (if mobius then G.signedLaplacianMobius else G.scalarLaplacian))) := by
  -- Unpack the existing similarity / reindex identity.
  obtain ⟨P, hPdet, hreindex⟩ := G.laplacian_decomposes mobius
  -- (i) similarity: kernel dim of L = kernel dim of P * L * P⁻¹
  have hsim : finrank ℝ (LinearMap.ker (Matrix.toLin' (P * G.laplacian mobius * P⁻¹))) =
              finrank ℝ (LinearMap.ker (Matrix.toLin' (G.laplacian mobius))) :=
    finrank_ker_toLin'_conj P (G.laplacian mobius) hPdet
  -- (ii) reindex: kernel dim preserved by reindex e e.
  have hreidx :
      finrank ℝ (LinearMap.ker (Matrix.toLin'
        (Matrix.reindex G.prodFinTwoEquivSum G.prodFinTwoEquivSum
          (P * G.laplacian mobius * P⁻¹)))) =
      finrank ℝ (LinearMap.ker (Matrix.toLin' (P * G.laplacian mobius * P⁻¹))) :=
    finrank_ker_toLin'_reindex G.prodFinTwoEquivSum _
  -- Transport the kernel-dim equality across the reindex identity hreindex.
  rw [hreindex] at hreidx
  -- (iii) block-diagonal split.
  have hsplit :=
    finrank_ker_toLin'_fromBlocks_diag (K := ℝ)
      G.scalarLaplacian
      (if mobius then G.signedLaplacianMobius else G.scalarLaplacian)
  -- Chain: hsplit = hreidx (via rw) = hsim.
  -- hsim   : finrank(ker(toLin'(P*L*P⁻¹))) = finrank(ker(toLin' L))
  -- hreidx : finrank(ker(toLin'(fromBlocks ...))) = finrank(ker(toLin'(P*L*P⁻¹)))
  -- hsplit : finrank(ker(toLin'(fromBlocks ...))) = finrank(ker(toLin' scalar)) + finrank(ker(toLin' B))
  linarith [hsim, hreidx, hsplit]

end ConnGraph

end ConnectionLaplacian
