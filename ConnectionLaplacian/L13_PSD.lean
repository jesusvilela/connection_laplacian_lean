/-
ConnectionLaplacian/L13_PSD.lean

**Stratum L13 — Positive semidefiniteness of the signed Möbius Laplacian.**

Mirrors the paper proof at `paper.tex:996-1030` (Lemma: Positive
semidefiniteness of the signed Laplacian):

    ⟨x, L^sg(G) x⟩ = Σ_{e={u,v}∈E∖W}(x_u − x_v)² + Σ_{e={u,v}∈W}(x_u + x_v)²

for all `x ∈ ℝ^V`, hence `L^sg(G) ⪰ 0`.

**Proof route (A — direct sum-of-squares).**

We express `x ⬝ᵥ (M *ᵥ x) = (1/2) · Σ_{i,j} (if Adj i j then (x_i + s(i,j) x_j)² else 0)`
where `s(i,j) = +1` on wrap edges, `-1` on non-wrap, and use the (i↔j)
averaging trick. Since `s² = 1` the square identity holds entry-wise.
-/

import ConnectionLaplacian.KernelDimension
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L13.1 — Signed edge-weight helper. -/

/-- The signed adjacency weight: `+1` on wrap edges, `−1` on non-wrap
edges (among adjacent pairs), and `0` on non-edges. -/
private noncomputable def signedWeight (u v : G.V) : ℝ :=
  if h : G.graph.Adj u v then
    if G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ then (1 : ℝ) else -1
  else 0

private lemma signedWeight_sq (u v : G.V) (hadj : G.graph.Adj u v) :
    G.signedWeight u v * G.signedWeight u v = 1 := by
  unfold signedWeight
  rw [dif_pos hadj]
  split_ifs <;> norm_num

/-- Wrap-ness only depends on the unordered edge: `s(u,v) = s(v,u)` in
`Sym2`, so `G.wrap ⟨s(u,v), _⟩ ↔ G.wrap ⟨s(v,u), _⟩`. -/
private lemma wrap_symm {u v : G.V} (hadj : G.graph.Adj u v) :
    G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩ ↔
      G.wrap ⟨s(v, u), (SimpleGraph.mem_edgeSet G.graph).mpr hadj.symm⟩ := by
  have hedge_eq :
      (⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩ :
          G.graph.edgeSet)
        = ⟨s(v, u), (SimpleGraph.mem_edgeSet G.graph).mpr hadj.symm⟩ := by
    apply Subtype.ext; exact Sym2.eq_swap
  rw [hedge_eq]

private lemma signedWeight_symm (u v : G.V) :
    G.signedWeight u v = G.signedWeight v u := by
  unfold signedWeight
  by_cases hadj : G.graph.Adj u v
  · rw [dif_pos hadj, dif_pos hadj.symm]
    have hw := G.wrap_symm hadj
    by_cases hw_uv :
        G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr hadj⟩
    · rw [if_pos hw_uv, if_pos (hw.mp hw_uv)]
    · rw [if_neg hw_uv, if_neg (fun h => hw_uv (hw.mpr h))]
  · have hnvu : ¬ G.graph.Adj v u := fun h => hadj h.symm
    rw [dif_neg hadj, dif_neg hnvu]

/-! ### L13.2 — Symmetry. -/

/-- On the diagonal `signedLaplacianMobius v v = deg(v)`. -/
private lemma sLM_diag (v : G.V) :
    G.signedLaplacianMobius v v = ((G.graph.neighborFinset v).card : ℝ) := by
  unfold signedLaplacianMobius
  rw [if_pos rfl]

/-- Off the diagonal, `signedLaplacianMobius u v = signedWeight u v`. -/
private lemma sLM_offdiag {u v : G.V} (huv : u ≠ v) :
    G.signedLaplacianMobius u v = G.signedWeight u v := by
  unfold signedLaplacianMobius signedWeight
  rw [if_neg huv]

/-- The signed Möbius Laplacian is symmetric. -/
theorem signedLaplacianMobius_isSymm :
    G.signedLaplacianMobius.IsSymm := by
  ext u v
  show G.signedLaplacianMobius v u = G.signedLaplacianMobius u v
  by_cases huv : u = v
  · subst huv; rfl
  · rw [G.sLM_offdiag huv, G.sLM_offdiag (Ne.symm huv), G.signedWeight_symm]

/-- The signed Möbius Laplacian is Hermitian (over ℝ, equivalent to `IsSymm`). -/
theorem signedLaplacianMobius_isHermitian :
    G.signedLaplacianMobius.IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact G.signedLaplacianMobius_isSymm

/-! ### L13.3 — Quadratic-form computation. -/

/-- Per-entry expansion of `signedLaplacianMobius i j * x i * x j`:
on the diagonal this is `(∑_{k adj i} 1) * x_i²`; off the diagonal and
adjacent, this is `s(i,j) * x_i * x_j`; otherwise 0. The point is to
write it uniformly as an `if Adj` sum after replacing the diagonal. -/
private lemma sLM_entry_eq (x : G.V → ℝ) (i j : G.V) :
    G.signedLaplacianMobius i j * x j =
      (if i = j then ((G.graph.neighborFinset i).card : ℝ) * x i else 0)
      + (if i = j then 0 else
          if G.graph.Adj i j then G.signedWeight i j * x j else 0) := by
  by_cases hij : i = j
  · subst hij
    rw [G.sLM_diag i, if_pos rfl, if_pos rfl, add_zero]
  · rw [if_neg hij, if_neg hij, zero_add]
    rw [G.sLM_offdiag hij]
    unfold signedWeight
    by_cases hadj : G.graph.Adj i j
    · rw [dif_pos hadj, if_pos hadj]
    · rw [dif_neg hadj, if_neg hadj]
      ring

/-- Quadratic form: `x ⬝ᵥ (L_sg *ᵥ x) = Σ_i deg(i) * x_i² +
Σ_{i,j: Adj i j} s(i,j) * x_i * x_j`. -/
private lemma sLM_quadForm_raw (x : G.V → ℝ) :
    x ⬝ᵥ (G.signedLaplacianMobius *ᵥ x) =
      (∑ i : G.V, ((G.graph.neighborFinset i).card : ℝ) * (x i * x i))
        + ∑ i : G.V, ∑ j : G.V,
            if G.graph.Adj i j then G.signedWeight i j * x i * x j else 0 := by
  unfold dotProduct mulVec
  simp only [Matrix.dotProduct]
  -- Step 1: Rewrite x i * (∑_j M i j * x j) = ∑_j x_i * (M i j * x j).
  have step1 : ∀ i : G.V,
      x i * (∑ j : G.V, G.signedLaplacianMobius i j * x j) =
        ∑ j : G.V, x i * (G.signedLaplacianMobius i j * x j) := by
    intro i; rw [Finset.mul_sum]
  simp only [step1]
  -- Step 2: Apply sLM_entry_eq inside.
  have step2 : ∀ i j : G.V, x i * (G.signedLaplacianMobius i j * x j) =
      (if i = j then ((G.graph.neighborFinset i).card : ℝ) * (x i * x i) else 0)
      + (if i = j then 0 else
          if G.graph.Adj i j then G.signedWeight i j * x i * x j else 0) := by
    intro i j
    rw [← mul_assoc, show x i * G.signedLaplacianMobius i j =
          G.signedLaplacianMobius i j * x i from mul_comm _ _]
    rw [mul_assoc, show G.signedLaplacianMobius i j * (x i * x j) =
          (G.signedLaplacianMobius i j * x j) * x i from by ring]
    -- Now use sLM_entry_eq.
    have hentry := G.sLM_entry_eq x i j
    -- Goal: (M i j * x j) * x i = diag + off
    by_cases hij : i = j
    · subst hij
      rw [G.sLM_diag i, if_pos rfl, if_pos rfl, add_zero]
      ring
    · rw [if_neg hij, if_neg hij, zero_add]
      rw [G.sLM_offdiag hij]
      unfold signedWeight
      by_cases hadj : G.graph.Adj i j
      · rw [dif_pos hadj, if_pos hadj]; ring
      · rw [dif_neg hadj, if_neg hadj]; ring
  simp only [step2]
  -- Step 3: For each i, the inner Σ_j simplifies via:
  --   Σ_j [if i=j then deg(i)*x_i² else 0] = deg(i)*x_i²
  --   Σ_j [if i=j then 0 else (if adj then s·x_i·x_j else 0)]
  --     = Σ_j [if adj then s·x_i·x_j else 0]  (self-loops absent)
  have hstep3 : ∀ i : G.V,
      (∑ j : G.V,
          ((if i = j then ((G.graph.neighborFinset i).card : ℝ) * (x i * x i) else 0)
            + (if i = j then 0 else
                if G.graph.Adj i j then G.signedWeight i j * x i * x j else 0))) =
        ((G.graph.neighborFinset i).card : ℝ) * (x i * x i)
          + ∑ j : G.V,
              if G.graph.Adj i j then G.signedWeight i j * x i * x j else 0 := by
    intro i
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_ite_eq Finset.univ i (fun _ => ((G.graph.neighborFinset i).card : ℝ) * (x i * x i))]
      rw [if_pos (Finset.mem_univ i)]
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_neg (SimpleGraph.irrefl _)]
      · rw [if_neg hij]
  rw [Finset.sum_congr rfl (fun i _ => hstep3 i)]
  -- Now split `Σ_i (a_i + b_i) = Σ a_i + Σ b_i`.
  rw [Finset.sum_add_distrib]

/-- **Key identity.** Using `deg(i) = ∑_j [if Adj i j then 1 else 0]`:

  Σ_i deg(i)*x_i² = Σ_{i,j: Adj} x_i²

and symmetrising (i↔j) yields

  x ⬝ᵥ (L_sg *ᵥ x) = (1/2) · Σ_{i,j: Adj} (x_i + s(i,j) x_j)²,

in particular ≥ 0. -/
private theorem sLM_quadForm_nonneg (x : G.V → ℝ) :
    0 ≤ x ⬝ᵥ (G.signedLaplacianMobius *ᵥ x) := by
  rw [G.sLM_quadForm_raw x]
  -- Rewrite degree as a sum of indicator, then combine.
  have hdeg : ∀ i : G.V, ((G.graph.neighborFinset i).card : ℝ) * (x i * x i) =
      ∑ j : G.V, if G.graph.Adj i j then x i * x i else 0 := by
    intro i
    have := G.graph.degree_eq_sum_if_adj (R := ℝ) i
    show (G.graph.degree i : ℝ) * (x i * x i) = _
    rw [this, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : G.graph.Adj i j
    · rw [if_pos hij, if_pos hij]; ring
    · rw [if_neg hij, if_neg hij]; ring
  rw [show (∑ i : G.V, ((G.graph.neighborFinset i).card : ℝ) * (x i * x i)) =
          ∑ i : G.V, ∑ j : G.V, if G.graph.Adj i j then x i * x i else 0 from
          Finset.sum_congr rfl (fun i _ => hdeg i)]
  -- Combine the two double sums into one.
  rw [← Finset.sum_add_distrib]
  have hcombine : ∀ i : G.V,
      ((∑ j : G.V, if G.graph.Adj i j then x i * x i else 0) +
        ∑ j : G.V, if G.graph.Adj i j then G.signedWeight i j * x i * x j else 0) =
      ∑ j : G.V, if G.graph.Adj i j then
        x i * x i + G.signedWeight i j * x i * x j else 0 := by
    intro i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : G.graph.Adj i j
    · rw [if_pos hij, if_pos hij, if_pos hij]
    · rw [if_neg hij, if_neg hij, if_neg hij, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => hcombine i)]
  -- Apply the (i↔j) averaging trick:
  --   2 · S = ∑_{i,j: Adj} (x_i² + x_j² + 2 s x_i x_j) = ∑_{i,j: Adj} (x_i + s x_j)².
  -- Hence S = (1/2) · ∑_{i,j: Adj} (x_i + s x_j)² ≥ 0.
  set S : ℝ := ∑ i : G.V, ∑ j : G.V,
      if G.graph.Adj i j then x i * x i + G.signedWeight i j * x i * x j else 0
    with hSdef
  set Q : ℝ := ∑ i : G.V, ∑ j : G.V,
      if G.graph.Adj i j then (x i + G.signedWeight i j * x j) ^ 2 else 0
    with hQdef
  have hQ_nonneg : 0 ≤ Q := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  suffices h : 2 * S = Q by
    have : S = Q / 2 := by linarith
    rw [this]
    exact div_nonneg hQ_nonneg (by norm_num)
  -- Prove 2 * S = Q by double-counting: swap (i ↔ j) gives S again.
  have hswap : S = ∑ i : G.V, ∑ j : G.V,
      if G.graph.Adj i j then x j * x j + G.signedWeight i j * x i * x j else 0 := by
    rw [hSdef]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : G.graph.Adj j i
    · have hji : G.graph.Adj i j := hij.symm
      rw [if_pos hij, if_pos hji]
      rw [G.signedWeight_symm j i]
      ring
    · have hji : ¬ G.graph.Adj i j := fun h => hij h.symm
      rw [if_neg hij, if_neg hji]
  have htwoS : 2 * S = S + S := two_mul S
  rw [htwoS]
  conv_lhs => rw [show S + S = (S) + (S) from rfl]
  nth_rewrite 2 [hswap]
  rw [hSdef, hQdef]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : G.graph.Adj i j
  · rw [if_pos hij, if_pos hij, if_pos hij]
    have hs2 : G.signedWeight i j * G.signedWeight i j = 1 :=
      G.signedWeight_sq i j hij
    have hsq : (x i + G.signedWeight i j * x j) ^ 2 =
        x i * x i + x j * x j + 2 * (G.signedWeight i j * x i * x j) := by
      have hexp : (x i + G.signedWeight i j * x j) ^ 2 =
          x i * x i + 2 * (x i * (G.signedWeight i j * x j))
            + (G.signedWeight i j * x j) * (G.signedWeight i j * x j) := by ring
      have hs_sq : (G.signedWeight i j * x j) * (G.signedWeight i j * x j)
          = x j * x j := by
        have hmul : (G.signedWeight i j * x j) * (G.signedWeight i j * x j)
            = (G.signedWeight i j * G.signedWeight i j) * (x j * x j) := by ring
        rw [hmul, hs2, one_mul]
      rw [hexp, hs_sq]; ring
    rw [hsq]; ring
  · rw [if_neg hij, if_neg hij, if_neg hij, add_zero]

/-! ### L13.4 — Main theorem. -/

/-- **Main theorem.** The signed Möbius Laplacian is positive
semidefinite. -/
theorem signedLaplacianMobius_posSemidef :
    G.signedLaplacianMobius.PosSemidef := by
  refine ⟨G.signedLaplacianMobius_isHermitian, ?_⟩
  intro x
  -- On ℝ, `star x = x` (trivial star). Reduce to the real-valued form.
  have hstar : (star x : G.V → ℝ) = x := by
    funext i; exact star_trivial (x i)
  rw [hstar]
  exact G.sLM_quadForm_nonneg x

end ConnGraph

end ConnectionLaplacian
