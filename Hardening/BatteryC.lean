/-
Convention battery SHARD C (generated).
See Hardening/ConventionBattery.lean header for provenance.
-/
import Hardening.BatteryPrelude

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators

set_option maxHeartbeats 4000000


def E_B3 : Finset (Fin 2 × Fin 2) := {(0, 1), (1, 0)}
def A_B3 (u v : Fin 2) : Prop := (u, v) ∈ E_B3
instance : DecidableRel A_B3 := fun _ _ => Finset.decidableMem _ _
def W_B3 : Finset (Sym2 (Fin 2)) := {s(0, 1)}
def G_B3 : ConnGraph where
  V := Fin 2
  graph :=
    { Adj := A_B3
      symm := by
        intro u v h
        simp [A_B3, E_B3, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B3, E_B3, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B3
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 2) (Fin 2) ℝ from G_B3.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 2) => if u = 0 then if v = 0 then (1 : ℝ) else (1 : ℝ) else if v = 0 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B3, degree, A_B3, E_B3, W_B3,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 2) (Fin 2) ℝ from G_B3.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 2) => if u = 0 then if v = 0 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B3, A_B3, E_B3, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B7 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (1, 2), (2, 1)}
def A_B7 (u v : Fin 3) : Prop := (u, v) ∈ E_B7
instance : DecidableRel A_B7 := fun _ _ => Finset.decidableMem _ _
def W_B7 : Finset (Sym2 (Fin 3)) := {}
def G_B7 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B7
      symm := by
        intro u v h
        simp [A_B7, E_B7, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B7, E_B7, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B7
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B7.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B7, degree, A_B7, E_B7, W_B7,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B7.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B7, A_B7, E_B7, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B11 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
def A_B11 (u v : Fin 3) : Prop := (u, v) ∈ E_B11
instance : DecidableRel A_B11 := fun _ _ => Finset.decidableMem _ _
def W_B11 : Finset (Sym2 (Fin 3)) := {}
def G_B11 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B11
      symm := by
        intro u v h
        simp [A_B11, E_B11, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B11, E_B11, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B11
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B11.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B11, degree, A_B11, E_B11, W_B11,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B11.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B11, A_B11, E_B11, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B15 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
def A_B15 (u v : Fin 3) : Prop := (u, v) ∈ E_B15
instance : DecidableRel A_B15 := fun _ _ => Finset.decidableMem _ _
def W_B15 : Finset (Sym2 (Fin 3)) := {s(0, 1), s(0, 2)}
def G_B15 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B15
      symm := by
        intro u v h
        simp [A_B15, E_B15, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B15, E_B15, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B15
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B15.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B15, degree, A_B15, E_B15, W_B15,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B15.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B15, A_B15, E_B15, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B19 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)}
def A_B19 (u v : Fin 4) : Prop := (u, v) ∈ E_B19
instance : DecidableRel A_B19 := fun _ _ => Finset.decidableMem _ _
def W_B19 : Finset (Sym2 (Fin 4)) := {}
def G_B19 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B19
      symm := by
        intro u v h
        simp [A_B19, E_B19, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B19, E_B19, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B19
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B19.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B19, degree, A_B19, E_B19, W_B19,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B19.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B19, A_B19, E_B19, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B23 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)}
def A_B23 (u v : Fin 4) : Prop := (u, v) ∈ E_B23
instance : DecidableRel A_B23 := fun _ _ => Finset.decidableMem _ _
def W_B23 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(1, 2)}
def G_B23 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B23
      symm := by
        intro u v h
        simp [A_B23, E_B23, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B23, E_B23, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B23
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B23.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B23, degree, A_B23, E_B23, W_B23,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B23.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B23, A_B23, E_B23, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B27 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0)}
def A_B27 (u v : Fin 4) : Prop := (u, v) ∈ E_B27
instance : DecidableRel A_B27 := fun _ _ => Finset.decidableMem _ _
def W_B27 : Finset (Sym2 (Fin 4)) := {}
def G_B27 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B27
      symm := by
        intro u v h
        simp [A_B27, E_B27, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B27, E_B27, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B27
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B27.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B27, degree, A_B27, E_B27, W_B27,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B27.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B27, A_B27, E_B27, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B31 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0)}
def A_B31 (u v : Fin 4) : Prop := (u, v) ∈ E_B31
instance : DecidableRel A_B31 := fun _ _ => Finset.decidableMem _ _
def W_B31 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(0, 2)}
def G_B31 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B31
      symm := by
        intro u v h
        simp [A_B31, E_B31, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B31, E_B31, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B31
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B31.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B31, degree, A_B31, E_B31, W_B31,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B31.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B31, A_B31, E_B31, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B35 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B35 (u v : Fin 4) : Prop := (u, v) ∈ E_B35
instance : DecidableRel A_B35 := fun _ _ => Finset.decidableMem _ _
def W_B35 : Finset (Sym2 (Fin 4)) := {}
def G_B35 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B35
      symm := by
        intro u v h
        simp [A_B35, E_B35, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B35, E_B35, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B35
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B35.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B35, degree, A_B35, E_B35, W_B35,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B35.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B35, A_B35, E_B35, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B39 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B39 (u v : Fin 4) : Prop := (u, v) ∈ E_B39
instance : DecidableRel A_B39 := fun _ _ => Finset.decidableMem _ _
def W_B39 : Finset (Sym2 (Fin 4)) := {s(1, 2), s(3, 0)}
def G_B39 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B39
      symm := by
        intro u v h
        simp [A_B39, E_B39, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B39, E_B39, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B39
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B39.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B39, degree, A_B39, E_B39, W_B39,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B39.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B39, A_B39, E_B39, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B43 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 2), (2, 0)}
def A_B43 (u v : Fin 4) : Prop := (u, v) ∈ E_B43
instance : DecidableRel A_B43 := fun _ _ => Finset.decidableMem _ _
def W_B43 : Finset (Sym2 (Fin 4)) := {}
def G_B43 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B43
      symm := by
        intro u v h
        simp [A_B43, E_B43, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B43, E_B43, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B43
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B43.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B43, degree, A_B43, E_B43, W_B43,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B43.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B43, A_B43, E_B43, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B47 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 2), (2, 0)}
def A_B47 (u v : Fin 4) : Prop := (u, v) ∈ E_B47
instance : DecidableRel A_B47 := fun _ _ => Finset.decidableMem _ _
def W_B47 : Finset (Sym2 (Fin 4)) := {s(1, 2), s(3, 0)}
def G_B47 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B47
      symm := by
        intro u v h
        simp [A_B47, E_B47, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B47, E_B47, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B47
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B47.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B47, degree, A_B47, E_B47, W_B47,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B47.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B47, A_B47, E_B47, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B51 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)}
def A_B51 (u v : Fin 4) : Prop := (u, v) ∈ E_B51
instance : DecidableRel A_B51 := fun _ _ => Finset.decidableMem _ _
def W_B51 : Finset (Sym2 (Fin 4)) := {}
def G_B51 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B51
      symm := by
        intro u v h
        simp [A_B51, E_B51, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B51, E_B51, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B51
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B51.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B51, degree, A_B51, E_B51, W_B51,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B51.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B51, A_B51, E_B51, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B55 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)}
def A_B55 (u v : Fin 4) : Prop := (u, v) ∈ E_B55
instance : DecidableRel A_B55 := fun _ _ => Finset.decidableMem _ _
def W_B55 : Finset (Sym2 (Fin 4)) := {s(0, 2), s(1, 2), s(1, 3)}
def G_B55 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B55
      symm := by
        intro u v h
        simp [A_B55, E_B55, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B55, E_B55, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B55
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B55.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B55, degree, A_B55, E_B55, W_B55,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B55.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B55, A_B55, E_B55, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B59 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 4), (4, 3)}
def A_B59 (u v : Fin 5) : Prop := (u, v) ∈ E_B59
instance : DecidableRel A_B59 := fun _ _ => Finset.decidableMem _ _
def W_B59 : Finset (Sym2 (Fin 5)) := {}
def G_B59 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B59
      symm := by
        intro u v h
        simp [A_B59, E_B59, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B59, E_B59, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B59
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B59.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B59, degree, A_B59, E_B59, W_B59,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B59.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B59, A_B59, E_B59, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B63 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 4), (4, 3)}
def A_B63 (u v : Fin 5) : Prop := (u, v) ∈ E_B63
instance : DecidableRel A_B63 := fun _ _ => Finset.decidableMem _ _
def W_B63 : Finset (Sym2 (Fin 5)) := {s(0, 2), s(3, 4)}
def G_B63 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B63
      symm := by
        intro u v h
        simp [A_B63, E_B63, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B63, E_B63, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B63
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B63.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B63, degree, A_B63, E_B63, W_B63,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B63.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B63, A_B63, E_B63, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B67 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B67 (u v : Fin 5) : Prop := (u, v) ∈ E_B67
instance : DecidableRel A_B67 := fun _ _ => Finset.decidableMem _ _
def W_B67 : Finset (Sym2 (Fin 5)) := {}
def G_B67 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B67
      symm := by
        intro u v h
        simp [A_B67, E_B67, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B67, E_B67, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B67
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B67.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B67, degree, A_B67, E_B67, W_B67,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B67.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B67, A_B67, E_B67, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B71 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B71 (u v : Fin 5) : Prop := (u, v) ∈ E_B71
instance : DecidableRel A_B71 := fun _ _ => Finset.decidableMem _ _
def W_B71 : Finset (Sym2 (Fin 5)) := {s(1, 2), s(3, 0)}
def G_B71 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B71
      symm := by
        intro u v h
        simp [A_B71, E_B71, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B71, E_B71, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B71
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B71.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B71, degree, A_B71, E_B71, W_B71,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B71.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B71, A_B71, E_B71, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

end Hardening
