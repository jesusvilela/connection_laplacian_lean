/-
Convention battery SHARD D (generated).
See Hardening/ConventionBattery.lean header for provenance.
-/
import Hardening.BatteryPrelude

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators

set_option maxHeartbeats 4000000


def E_B4 : Finset (Fin 3 × Fin 3) := {}
def A_B4 (u v : Fin 3) : Prop := (u, v) ∈ E_B4
instance : DecidableRel A_B4 := fun _ _ => Finset.decidableMem _ _
def W_B4 : Finset (Sym2 (Fin 3)) := {}
def G_B4 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B4
      symm := by
        intro u v h
        simp [A_B4, E_B4, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B4, E_B4, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B4
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B4.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B4, degree, A_B4, E_B4, W_B4,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B4.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B4, A_B4, E_B4, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B8 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (1, 2), (2, 1)}
def A_B8 (u v : Fin 3) : Prop := (u, v) ∈ E_B8
instance : DecidableRel A_B8 := fun _ _ => Finset.decidableMem _ _
def W_B8 : Finset (Sym2 (Fin 3)) := {s(0, 1)}
def G_B8 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B8
      symm := by
        intro u v h
        simp [A_B8, E_B8, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B8, E_B8, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B8
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B8.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B8, degree, A_B8, E_B8, W_B8,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B8.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B8, A_B8, E_B8, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B12 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
def A_B12 (u v : Fin 3) : Prop := (u, v) ∈ E_B12
instance : DecidableRel A_B12 := fun _ _ => Finset.decidableMem _ _
def W_B12 : Finset (Sym2 (Fin 3)) := {s(0, 1)}
def G_B12 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B12
      symm := by
        intro u v h
        simp [A_B12, E_B12, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B12, E_B12, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B12
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B12.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B12, degree, A_B12, E_B12, W_B12,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B12.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B12, A_B12, E_B12, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B16 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
def A_B16 (u v : Fin 3) : Prop := (u, v) ∈ E_B16
instance : DecidableRel A_B16 := fun _ _ => Finset.decidableMem _ _
def W_B16 : Finset (Sym2 (Fin 3)) := {s(0, 1), s(1, 2)}
def G_B16 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B16
      symm := by
        intro u v h
        simp [A_B16, E_B16, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B16, E_B16, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B16
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B16.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B16, degree, A_B16, E_B16, W_B16,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B16.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B16, A_B16, E_B16, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B20 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)}
def A_B20 (u v : Fin 4) : Prop := (u, v) ∈ E_B20
instance : DecidableRel A_B20 := fun _ _ => Finset.decidableMem _ _
def W_B20 : Finset (Sym2 (Fin 4)) := {s(0, 1)}
def G_B20 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B20
      symm := by
        intro u v h
        simp [A_B20, E_B20, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B20, E_B20, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B20
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B20.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B20, degree, A_B20, E_B20, W_B20,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B20.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B20, A_B20, E_B20, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B24 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)}
def A_B24 (u v : Fin 4) : Prop := (u, v) ∈ E_B24
instance : DecidableRel A_B24 := fun _ _ => Finset.decidableMem _ _
def W_B24 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(2, 3)}
def G_B24 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B24
      symm := by
        intro u v h
        simp [A_B24, E_B24, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B24, E_B24, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B24
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B24.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B24, degree, A_B24, E_B24, W_B24,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B24.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B24, A_B24, E_B24, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B28 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0)}
def A_B28 (u v : Fin 4) : Prop := (u, v) ∈ E_B28
instance : DecidableRel A_B28 := fun _ _ => Finset.decidableMem _ _
def W_B28 : Finset (Sym2 (Fin 4)) := {s(0, 1)}
def G_B28 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B28
      symm := by
        intro u v h
        simp [A_B28, E_B28, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B28, E_B28, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B28
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B28.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B28, degree, A_B28, E_B28, W_B28,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B28.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B28, A_B28, E_B28, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B32 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0)}
def A_B32 (u v : Fin 4) : Prop := (u, v) ∈ E_B32
instance : DecidableRel A_B32 := fun _ _ => Finset.decidableMem _ _
def W_B32 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(0, 3)}
def G_B32 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B32
      symm := by
        intro u v h
        simp [A_B32, E_B32, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B32, E_B32, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B32
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B32.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B32, degree, A_B32, E_B32, W_B32,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B32.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B32, A_B32, E_B32, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B36 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B36 (u v : Fin 4) : Prop := (u, v) ∈ E_B36
instance : DecidableRel A_B36 := fun _ _ => Finset.decidableMem _ _
def W_B36 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}
def G_B36 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B36
      symm := by
        intro u v h
        simp [A_B36, E_B36, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B36, E_B36, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B36
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B36.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B36, degree, A_B36, E_B36, W_B36,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B36.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B36, A_B36, E_B36, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B40 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B40 (u v : Fin 4) : Prop := (u, v) ∈ E_B40
instance : DecidableRel A_B40 := fun _ _ => Finset.decidableMem _ _
def W_B40 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(3, 0), s(2, 3)}
def G_B40 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B40
      symm := by
        intro u v h
        simp [A_B40, E_B40, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B40, E_B40, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B40
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B40.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B40, degree, A_B40, E_B40, W_B40,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B40.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B40, A_B40, E_B40, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B44 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 2), (2, 0)}
def A_B44 (u v : Fin 4) : Prop := (u, v) ∈ E_B44
instance : DecidableRel A_B44 := fun _ _ => Finset.decidableMem _ _
def W_B44 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(0, 2)}
def G_B44 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B44
      symm := by
        intro u v h
        simp [A_B44, E_B44, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B44, E_B44, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B44
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B44.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (3 : ℝ) else (1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B44, degree, A_B44, E_B44, W_B44,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B44.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B44, A_B44, E_B44, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B48 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 2), (2, 0)}
def A_B48 (u v : Fin 4) : Prop := (u, v) ∈ E_B48
instance : DecidableRel A_B48 := fun _ _ => Finset.decidableMem _ _
def W_B48 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(0, 2), s(3, 0)}
def G_B48 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B48
      symm := by
        intro u v h
        simp [A_B48, E_B48, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B48, E_B48, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B48
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B48.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B48, degree, A_B48, E_B48, W_B48,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B48.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B48, A_B48, E_B48, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B52 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)}
def A_B52 (u v : Fin 4) : Prop := (u, v) ∈ E_B52
instance : DecidableRel A_B52 := fun _ _ => Finset.decidableMem _ _
def W_B52 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)}
def G_B52 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B52
      symm := by
        intro u v h
        simp [A_B52, E_B52, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B52, E_B52, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B52
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B52.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (3 : ℝ) else (1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B52, degree, A_B52, E_B52, W_B52,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B52.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B52, A_B52, E_B52, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B56 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)}
def A_B56 (u v : Fin 4) : Prop := (u, v) ∈ E_B56
instance : DecidableRel A_B56 := fun _ _ => Finset.decidableMem _ _
def W_B56 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(2, 3)}
def G_B56 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B56
      symm := by
        intro u v h
        simp [A_B56, E_B56, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B56, E_B56, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B56
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B56.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B56, degree, A_B56, E_B56, W_B56,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B56.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B56, A_B56, E_B56, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B60 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 4), (4, 3)}
def A_B60 (u v : Fin 5) : Prop := (u, v) ∈ E_B60
instance : DecidableRel A_B60 := fun _ _ => Finset.decidableMem _ _
def W_B60 : Finset (Sym2 (Fin 5)) := {s(0, 1), s(0, 2), s(1, 2), s(3, 4)}
def G_B60 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B60
      symm := by
        intro u v h
        simp [A_B60, E_B60, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B60, E_B60, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B60
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B60.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B60, degree, A_B60, E_B60, W_B60,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B60.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B60, A_B60, E_B60, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B64 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 4), (4, 3)}
def A_B64 (u v : Fin 5) : Prop := (u, v) ∈ E_B64
instance : DecidableRel A_B64 := fun _ _ => Finset.decidableMem _ _
def W_B64 : Finset (Sym2 (Fin 5)) := {s(0, 1), s(3, 4), s(1, 2)}
def G_B64 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B64
      symm := by
        intro u v h
        simp [A_B64, E_B64, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B64, E_B64, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B64
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B64.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B64, degree, A_B64, E_B64, W_B64,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B64.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B64, A_B64, E_B64, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B68 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B68 (u v : Fin 5) : Prop := (u, v) ∈ E_B68
instance : DecidableRel A_B68 := fun _ _ => Finset.decidableMem _ _
def W_B68 : Finset (Sym2 (Fin 5)) := {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}
def G_B68 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B68
      symm := by
        intro u v h
        simp [A_B68, E_B68, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B68, E_B68, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B68
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B68.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B68, degree, A_B68, E_B68, W_B68,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B68.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B68, A_B68, E_B68, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B72 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B72 (u v : Fin 5) : Prop := (u, v) ∈ E_B72
instance : DecidableRel A_B72 := fun _ _ => Finset.decidableMem _ _
def W_B72 : Finset (Sym2 (Fin 5)) := {s(0, 1), s(3, 0), s(2, 3)}
def G_B72 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B72
      symm := by
        intro u v h
        simp [A_B72, E_B72, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B72, E_B72, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B72
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B72.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B72, degree, A_B72, E_B72, W_B72,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B72.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B72, A_B72, E_B72, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

end Hardening
