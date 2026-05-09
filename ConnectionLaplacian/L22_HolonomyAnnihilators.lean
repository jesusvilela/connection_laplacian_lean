/-
ConnectionLaplacian/L22_HolonomyAnnihilators.lean

**Stratum L22 — Holonomy and Annihilators.**

This file relates the kernel of the character-twisted Laplacian L_k
to the annihilator of the holonomy subgroup H_C.
-/

import ConnectionLaplacian.L21_SectoralDecomposition
import Mathlib.Combinatorics.SimpleGraph.Path

namespace ConnectionLaplacian

open Matrix BigOperators Complex

variable {n : Nat} [NeZero n] (Z : ZnConnGraph n)

/-- The value of a walk under the connection α. List-sum (NOT finset-sum):
    going around a cycle k times contributes k·(holonomy) so additivity
    under concatenation holds and reverse-walk gives the negation by
    Z/n antisymmetry of α.

    Note: this fixes a σ₃ catch on the previous `toFinset`-based definition,
    which would have deduplicated darts and broken additivity under
    concatenation. List-sum is the correct definition for Z/n-cocycle
    holonomy on walks. -/
def walkValue {u v : Z.V} (p : Z.graph.Walk u v) : ZMod n :=
  (p.darts.map Z.α).sum

/-- walkValue of the nil walk is zero. -/
@[simp]
lemma walkValue_nil (v : Z.V) : walkValue Z (SimpleGraph.Walk.nil : Z.graph.Walk v v) = 0 := by
  simp [walkValue]

/-- walkValue is additive under walk concatenation. -/
lemma walkValue_append {u v w : Z.V}
    (p : Z.graph.Walk u v) (q : Z.graph.Walk v w) :
    walkValue Z (p.append q) = walkValue Z p + walkValue Z q := by
  simp [walkValue, SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]

/-- α evaluated on the symm of a dart equals -α. Direct from antisymmetry. -/
lemma α_symm (d : Z.graph.Dart) : Z.α d.symm = - Z.α d :=
  eq_neg_of_add_eq_zero_right (Z.antisym d)

/-- walkValue of the reverse is the negation, by Z/n antisymmetry of α. -/
lemma walkValue_reverse {u v : Z.V} (p : Z.graph.Walk u v) :
    walkValue Z p.reverse = - walkValue Z p := by
  simp only [walkValue, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.map_map,
             List.sum_reverse]
  have h_pointwise : (Z.α ∘ SimpleGraph.Dart.symm) = (fun d => - Z.α d) := by
    funext d
    exact α_symm Z d
  rw [h_pointwise]
  induction p.darts with
  | nil => simp
  | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- The annihilator of an additive subgroup in ZMod n. -/
def subgroupAnnihilator (H : AddSubgroup (ZMod n)) : Set (ZMod n) :=
  { k | ∀ h ∈ H, k * h = 0 }

/-- The holonomy subgroup H_C of a connected component C ⊆ V.
    It is defined as the image of all closed walks starting at any vertex v ∈ C.
    By walkValue_nil, walkValue_append, walkValue_reverse, this set forms an
    additive subgroup of ZMod n. -/
def holonomySubgroup (C : Z.graph.ConnectedComponent) : AddSubgroup (ZMod n) :=
  let v : Z.V := Quot.out C
  { carrier := { k | ∃ p : Z.graph.Walk v v, walkValue Z p = k }
    add_mem' := by
      rintro a b ⟨p, hp⟩ ⟨q, hq⟩
      refine ⟨p.append q, ?_⟩
      rw [walkValue_append, hp, hq]
    zero_mem' := ⟨SimpleGraph.Walk.nil, walkValue_nil Z _⟩
    neg_mem' := by
      rintro a ⟨p, hp⟩
      refine ⟨p.reverse, ?_⟩
      rw [walkValue_reverse, hp]
  }

/-- A character χ_k is trivial on H_C iff L_k has a non-trivial kernel on C. -/
theorem mem_annihilator_iff_kernel_pos (C : Z.graph.ConnectedComponent) (k : Fin n) :
    (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C) ↔
    LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) ≠ ⊥ := by
  /-
  Proof sketch.

  Forward direction: if `k` annihilates the holonomy subgroup, then the phase
  `χ_k ∘ walkValue` is path-independent on a spanning tree of `C`. Choosing a
  root `r`, one defines

    `f(v) = exp(2π i k * walkValue(path(r,v)) / n)`.

  Path-independence follows because closed walks in `C` have holonomy in
  `holonomySubgroup Z C`, and `h_ann` forces `k` to kill that holonomy. The
  twisted edge relation then shows `sectoralLaplacian Z k • f = 0`, while
  `f(r) = 1` gives a nonzero kernel vector.

  Backward direction: if `f ≠ 0` lies in the kernel, the equation

    `deg(u) * f(u) = ∑_{v adj u} ω^(k·α(u,v)) * f(v)`

  propagates values uniquely along a spanning tree of the connected component.
  Going around a closed walk shows the accumulated phase must be trivial, so
  every element of `holonomySubgroup Z C` is annihilated by `k`.

  Remaining Lean gap: formalize the spanning-tree transport construction on
  `SimpleGraph.Walk` and the cycle-consistency argument for connected components.
  -/
  sorry

/--
The sectoral kernel dimension placeholder for a component/character pair.

The component argument is retained because the intended theorem is componentwise,
but the current formalization still measures the global kernel of
`sectoralLaplacian Z k`; restricting the operator to `Comp` is part of the
remaining L22 work.
-/
noncomputable def componentSectoralKernelDim (_Comp : Z.graph.ConnectedComponent) (k : Fin n) : Nat :=
  FiniteDimensional.finrank ℂ (LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)))

/-- Theorem: Character Sector Kernel Binary Property.
    The sectoral kernel dimension is 1 if k is in the annihilator, 0 otherwise. -/
theorem sectoral_kernel_dim_binary (Comp : Z.graph.ConnectedComponent) (k : Fin n) :
    componentSectoralKernelDim Z Comp k = 
    let _inst := Classical.propDecidable ((k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z Comp))
    if (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z Comp) then 1 else 0 := by
  /-
  This is the finite-dimensional refinement of
  `mem_annihilator_iff_kernel_pos`.

  * If `k` annihilates `holonomySubgroup Z Comp`, the previous theorem gives a
    nonzero kernel vector, hence the kernel has dimension at least `1`.
  * On a connected component, fixing the value at one root should determine a
    twisted-harmonic eigenfunction uniquely along a spanning tree, giving the
    complementary upper bound `finrank ≤ 1`.
  * If `k` does not annihilate the holonomy, the iff theorem should force the
    kernel to be trivial, hence finrank `0`.

  Remaining Lean gap: formalize the uniqueness-of-extension argument and convert
  the `ker = ⊥` / `ker ≠ ⊥` dichotomy into the finrank values `0` / `1`.
  -/
  sorry

end ConnectionLaplacian
