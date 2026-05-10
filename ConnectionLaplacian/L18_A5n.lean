/-
ConnectionLaplacian/L18_A5n.lean

A5_n scaffold.

This file does not prove the full `Z/n` connection-Laplacian kernel theorem.
It formalizes the typing correction found by the finite fuzzer:

  the A5_n.5(i) count is a regular/full `Z/n` sector sum, not the nullity of
  one magnetic character sector on `C^V`.

This file now wires that shell to L22: `sectorContribution C k` is identified
with the componentwise kernel dimension of the `k`-th magnetic Laplacian, and
for connected graphs the sector sum collapses to the annihilator cardinality.
-/

import ConnectionLaplacian.L22_HolonomyAnnihilators
import Mathlib.Data.Finset.Basic

namespace ConnectionLaplacian

open BigOperators

namespace A5n

/-- A finite component-level shell for the A5_n sector count.

`sectorContribution C k = 1` means: on component `C`, the `k`-th character
sector contributes one zero mode. In the intended graph model this is exactly
the condition `k ∈ Ann(H_C)`.
-/
structure SectorKernelData (Component : Type*) (n : Nat) where
  sectorContribution : Component → Fin n → Nat
  sectorContribution_is_indicator :
    ∀ (C : Component) (k : Fin n), sectorContribution C k = 0 ∨ sectorContribution C k = 1

variable {Component : Type*} [Fintype Component] {n : Nat} (D : SectorKernelData Component n)

/-- The annihilator sectors of a component, represented extensionally by the
sector-contribution indicator. -/
noncomputable def annSectors (C : Component) : Finset (Fin n) :=
  Finset.univ.filter fun k => D.sectorContribution C k = 1

/-- The full regular-sector kernel count: sum all character-sector
contributions over all components. -/
noncomputable def regularSectorKernelCount : Nat :=
  ∑ C : Component, ∑ k : Fin n, D.sectorContribution C k

/-- The annihilator-side count: for each component, count the sectors that
contribute one zero mode. -/
noncomputable def annihilatorKernelCount : Nat :=
  ∑ C : Component, (annSectors D C).card

omit [Fintype Component] in
private lemma indicator_sum_eq_filter_card (C : Component) :
    (∑ k : Fin n, D.sectorContribution C k) = (annSectors D C).card := by
  classical
  let f : Fin n → Nat := fun k => D.sectorContribution C k
  have h01 : ∀ k : Fin n, f k = 0 ∨ f k = 1 := by
    intro k
    exact D.sectorContribution_is_indicator C k
  have h :
      (∑ k in (Finset.univ : Finset (Fin n)), f k) =
        ((Finset.univ : Finset (Fin n)).filter fun k => f k = 1).card := by
    refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?base ?step
    · simp
    · intro a s has ih
      have h01a : f a = 0 ∨ f a = 1 := h01 a
      cases h01a with
      | inl hzero =>
          rw [Finset.filter_insert]
          simp [has, hzero, ih]
      | inr hone =>
          rw [Finset.filter_insert]
          simp [has, hone, ih, Nat.add_comm]
  simpa [annSectors, f] using h

/-- A5_n.5(i), sector-sum typing layer.

Once the graph bridge proves that `sectorContribution C k = 1` iff
`k ∈ Ann(H_C)`, this theorem turns the full regular `Z/n` kernel count into
the annihilator count. -/
theorem regularSectorKernelCount_eq_annihilatorKernelCount :
    regularSectorKernelCount D = annihilatorKernelCount D := by
  classical
  unfold regularSectorKernelCount annihilatorKernelCount
  exact Finset.sum_congr rfl (fun C _ => indicator_sum_eq_filter_card D C)

end A5n

namespace ZnConnGraph

variable {n : Nat} [NeZero n] (Z : ZnConnGraph n)

/-- The annihilator sectors of a connected component as a finite set of
characters. -/
noncomputable def annihilator (C : Z.graph.ConnectedComponent) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k =>
    (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)

end ZnConnGraph

variable {n : Nat} [NeZero n]

/-- The connected-component sector count appearing in A5_n.5(i). -/
noncomputable def annihilatorKernelCount (Z : ZnConnGraph n)
    (C : Z.graph.ConnectedComponent) : Nat :=
  ∑ k : Fin n, componentSectoralKernelDim Z C k

lemma componentSectoralKernelDim_indicator (Z : ZnConnGraph n) (k : Fin n)
    (C : Z.graph.ConnectedComponent) (hconn : Z.graph.Connected) :
    componentSectoralKernelDim Z C k =
      if k ∈ ZnConnGraph.annihilator Z C then 1 else 0 := by
  classical
  simp [ZnConnGraph.annihilator, sectoral_kernel_dim_binary, hconn]

noncomputable def a5nSectorKernelData (Z : ZnConnGraph n)
    (hconn : Z.graph.Connected) : A5n.SectorKernelData Z.graph.ConnectedComponent n where
  sectorContribution C k := componentSectoralKernelDim Z C k
  sectorContribution_is_indicator := by
    intro C k
    by_cases hk : k ∈ ZnConnGraph.annihilator Z C
    · right
      simp [componentSectoralKernelDim_indicator (Z := Z) (k := k) (C := C) (hconn := hconn), hk]
    · left
      simp [componentSectoralKernelDim_indicator (Z := Z) (k := k) (C := C) (hconn := hconn), hk]

lemma annSectors_eq_annihilator (Z : ZnConnGraph n) (C : Z.graph.ConnectedComponent)
    (hconn : Z.graph.Connected) :
    A5n.annSectors (a5nSectorKernelData Z hconn) C = ZnConnGraph.annihilator Z C := by
  classical
  ext k
  simp [A5n.annSectors, a5nSectorKernelData, componentSectoralKernelDim_indicator,
    ZnConnGraph.annihilator, hconn]

theorem annihilatorKernelCount_eq (Z : ZnConnGraph n) (C : Z.graph.ConnectedComponent)
    (hconn : Z.graph.Connected) :
    annihilatorKernelCount Z C = (ZnConnGraph.annihilator Z C).card := by
  classical
  let D : A5n.SectorKernelData Z.graph.ConnectedComponent n := a5nSectorKernelData Z hconn
  haveI : Subsingleton Z.graph.ConnectedComponent :=
    hconn.preconnected.subsingleton_connectedComponent
  letI : Unique Z.graph.ConnectedComponent :=
    { default := C, uniq := fun _ => Subsingleton.elim _ _ }
  have hdefault : (default : Z.graph.ConnectedComponent) = C := rfl
  have hA5 : A5n.regularSectorKernelCount D = A5n.annihilatorKernelCount D := by
    simpa [D] using A5n.regularSectorKernelCount_eq_annihilatorKernelCount (D := D)
  have hleft : A5n.regularSectorKernelCount D = annihilatorKernelCount Z C := by
    simp [D, A5n.regularSectorKernelCount, annihilatorKernelCount, a5nSectorKernelData, hdefault]
  have hright : A5n.annihilatorKernelCount D = (ZnConnGraph.annihilator Z C).card := by
    simp [D, A5n.annihilatorKernelCount, annSectors_eq_annihilator, hconn, hdefault]
  exact hleft.symm.trans (hA5.trans hright)

end ConnectionLaplacian
