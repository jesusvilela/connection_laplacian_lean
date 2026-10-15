/-
Convention battery SHARD A (generated).
See Hardening/ConventionBattery.lean header for provenance.
-/
import Hardening.BatteryPrelude

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators

set_option maxHeartbeats 4000000


def E_B1 : Finset (Fin 2 × Fin 2) := {}
def A_B1 (u v : Fin 2) : Prop := (u, v) ∈ E_B1
instance : DecidableRel A_B1 := fun _ _ => Finset.decidableMem _ _
def W_B1 : Finset (Sym2 (Fin 2)) := {}
def G_B1 : ConnGraph where
  V := Fin 2
  graph :=
    { Adj := A_B1
      symm := by
        intro u v h
        simp [A_B1, E_B1, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B1, E_B1, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B1
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 2) (Fin 2) ℝ from G_B1.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 2) => if u = 0 then if v = 0 then (0 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B1, degree, A_B1, E_B1, W_B1,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 2) (Fin 2) ℝ from G_B1.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 2) => if u = 0 then if v = 0 then (0 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B1, A_B1, E_B1, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B5 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0)}
def A_B5 (u v : Fin 3) : Prop := (u, v) ∈ E_B5
instance : DecidableRel A_B5 := fun _ _ => Finset.decidableMem _ _
def W_B5 : Finset (Sym2 (Fin 3)) := {}
def G_B5 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B5
      symm := by
        intro u v h
        simp [A_B5, E_B5, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B5, E_B5, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B5
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B5.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B5, degree, A_B5, E_B5, W_B5,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B5.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B5, A_B5, E_B5, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B9 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (1, 2), (2, 1)}
def A_B9 (u v : Fin 3) : Prop := (u, v) ∈ E_B9
instance : DecidableRel A_B9 := fun _ _ => Finset.decidableMem _ _
def W_B9 : Finset (Sym2 (Fin 3)) := {s(1, 2)}
def G_B9 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B9
      symm := by
        intro u v h
        simp [A_B9, E_B9, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B9, E_B9, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B9
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B9.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B9, degree, A_B9, E_B9, W_B9,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B9.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B9, A_B9, E_B9, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B13 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
def A_B13 (u v : Fin 3) : Prop := (u, v) ∈ E_B13
instance : DecidableRel A_B13 := fun _ _ => Finset.decidableMem _ _
def W_B13 : Finset (Sym2 (Fin 3)) := {s(0, 2)}
def G_B13 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B13
      symm := by
        intro u v h
        simp [A_B13, E_B13, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B13, E_B13, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B13
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B13.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B13, degree, A_B13, E_B13, W_B13,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B13.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B13, A_B13, E_B13, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B17 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
def A_B17 (u v : Fin 3) : Prop := (u, v) ∈ E_B17
instance : DecidableRel A_B17 := fun _ _ => Finset.decidableMem _ _
def W_B17 : Finset (Sym2 (Fin 3)) := {s(0, 2), s(1, 2)}
def G_B17 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B17
      symm := by
        intro u v h
        simp [A_B17, E_B17, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B17, E_B17, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B17
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B17.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B17, degree, A_B17, E_B17, W_B17,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B17.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B17, A_B17, E_B17, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B21 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)}
def A_B21 (u v : Fin 4) : Prop := (u, v) ∈ E_B21
instance : DecidableRel A_B21 := fun _ _ => Finset.decidableMem _ _
def W_B21 : Finset (Sym2 (Fin 4)) := {s(1, 2)}
def G_B21 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B21
      symm := by
        intro u v h
        simp [A_B21, E_B21, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B21, E_B21, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B21
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B21.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B21, degree, A_B21, E_B21, W_B21,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B21.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B21, A_B21, E_B21, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B25 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)}
def A_B25 (u v : Fin 4) : Prop := (u, v) ∈ E_B25
instance : DecidableRel A_B25 := fun _ _ => Finset.decidableMem _ _
def W_B25 : Finset (Sym2 (Fin 4)) := {s(1, 2), s(2, 3)}
def G_B25 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B25
      symm := by
        intro u v h
        simp [A_B25, E_B25, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B25, E_B25, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B25
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B25.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B25, degree, A_B25, E_B25, W_B25,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B25.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B25, A_B25, E_B25, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B29 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0)}
def A_B29 (u v : Fin 4) : Prop := (u, v) ∈ E_B29
instance : DecidableRel A_B29 := fun _ _ => Finset.decidableMem _ _
def W_B29 : Finset (Sym2 (Fin 4)) := {s(0, 2)}
def G_B29 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B29
      symm := by
        intro u v h
        simp [A_B29, E_B29, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B29, E_B29, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B29
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B29.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B29, degree, A_B29, E_B29, W_B29,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B29.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B29, A_B29, E_B29, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B33 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0)}
def A_B33 (u v : Fin 4) : Prop := (u, v) ∈ E_B33
instance : DecidableRel A_B33 := fun _ _ => Finset.decidableMem _ _
def W_B33 : Finset (Sym2 (Fin 4)) := {s(0, 2), s(0, 3)}
def G_B33 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B33
      symm := by
        intro u v h
        simp [A_B33, E_B33, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B33, E_B33, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B33
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B33.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B33, degree, A_B33, E_B33, W_B33,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B33.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B33, A_B33, E_B33, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B37 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B37 (u v : Fin 4) : Prop := (u, v) ∈ E_B37
instance : DecidableRel A_B37 := fun _ _ => Finset.decidableMem _ _
def W_B37 : Finset (Sym2 (Fin 4)) := {s(0, 1)}
def G_B37 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B37
      symm := by
        intro u v h
        simp [A_B37, E_B37, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B37, E_B37, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B37
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B37.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B37, degree, A_B37, E_B37, W_B37,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B37.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B37, A_B37, E_B37, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B41 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B41 (u v : Fin 4) : Prop := (u, v) ∈ E_B41
instance : DecidableRel A_B41 := fun _ _ => Finset.decidableMem _ _
def W_B41 : Finset (Sym2 (Fin 4)) := {s(3, 0), s(1, 2)}
def G_B41 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B41
      symm := by
        intro u v h
        simp [A_B41, E_B41, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B41, E_B41, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B41
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B41.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B41, degree, A_B41, E_B41, W_B41,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B41.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B41, A_B41, E_B41, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B45 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 2), (2, 0)}
def A_B45 (u v : Fin 4) : Prop := (u, v) ∈ E_B45
instance : DecidableRel A_B45 := fun _ _ => Finset.decidableMem _ _
def W_B45 : Finset (Sym2 (Fin 4)) := {s(0, 1)}
def G_B45 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B45
      symm := by
        intro u v h
        simp [A_B45, E_B45, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B45, E_B45, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B45
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B45.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B45, degree, A_B45, E_B45, W_B45,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B45.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B45, A_B45, E_B45, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B49 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 2), (2, 0)}
def A_B49 (u v : Fin 4) : Prop := (u, v) ∈ E_B49
instance : DecidableRel A_B49 := fun _ _ => Finset.decidableMem _ _
def W_B49 : Finset (Sym2 (Fin 4)) := {s(1, 2), s(3, 0), s(0, 2), s(2, 3)}
def G_B49 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B49
      symm := by
        intro u v h
        simp [A_B49, E_B49, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B49, E_B49, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B49
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B49.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (3 : ℝ) else (1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B49, degree, A_B49, E_B49, W_B49,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B49.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B49, A_B49, E_B49, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B53 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)}
def A_B53 (u v : Fin 4) : Prop := (u, v) ∈ E_B53
instance : DecidableRel A_B53 := fun _ _ => Finset.decidableMem _ _
def W_B53 : Finset (Sym2 (Fin 4)) := {s(0, 1)}
def G_B53 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B53
      symm := by
        intro u v h
        simp [A_B53, E_B53, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B53, E_B53, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B53
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B53.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B53, degree, A_B53, E_B53, W_B53,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B53.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B53, A_B53, E_B53, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B57 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)}
def A_B57 (u v : Fin 4) : Prop := (u, v) ∈ E_B57
instance : DecidableRel A_B57 := fun _ _ => Finset.decidableMem _ _
def W_B57 : Finset (Sym2 (Fin 4)) := {s(1, 3), s(1, 2), s(2, 3)}
def G_B57 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B57
      symm := by
        intro u v h
        simp [A_B57, E_B57, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B57, E_B57, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B57
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B57.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (3 : ℝ) else (1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B57, degree, A_B57, E_B57, W_B57,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B57.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B57, A_B57, E_B57, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B61 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 4), (4, 3)}
def A_B61 (u v : Fin 5) : Prop := (u, v) ∈ E_B61
instance : DecidableRel A_B61 := fun _ _ => Finset.decidableMem _ _
def W_B61 : Finset (Sym2 (Fin 5)) := {s(0, 1)}
def G_B61 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B61
      symm := by
        intro u v h
        simp [A_B61, E_B61, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B61, E_B61, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B61
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B61.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B61, degree, A_B61, E_B61, W_B61,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B61.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B61, A_B61, E_B61, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B65 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 4), (4, 3)}
def A_B65 (u v : Fin 5) : Prop := (u, v) ∈ E_B65
instance : DecidableRel A_B65 := fun _ _ => Finset.decidableMem _ _
def W_B65 : Finset (Sym2 (Fin 5)) := {s(3, 4), s(0, 2)}
def G_B65 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B65
      symm := by
        intro u v h
        simp [A_B65, E_B65, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B65, E_B65, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B65
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B65.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B65, degree, A_B65, E_B65, W_B65,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B65.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B65, A_B65, E_B65, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B69 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B69 (u v : Fin 5) : Prop := (u, v) ∈ E_B69
instance : DecidableRel A_B69 := fun _ _ => Finset.decidableMem _ _
def W_B69 : Finset (Sym2 (Fin 5)) := {s(0, 1)}
def G_B69 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B69
      symm := by
        intro u v h
        simp [A_B69, E_B69, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B69, E_B69, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B69
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B69.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B69, degree, A_B69, E_B69, W_B69,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B69.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B69, A_B69, E_B69, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B73 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B73 (u v : Fin 5) : Prop := (u, v) ∈ E_B73
instance : DecidableRel A_B73 := fun _ _ => Finset.decidableMem _ _
def W_B73 : Finset (Sym2 (Fin 5)) := {s(3, 0), s(1, 2)}
def G_B73 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B73
      symm := by
        intro u v h
        simp [A_B73, E_B73, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B73, E_B73, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B73
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B73.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B73, degree, A_B73, E_B73, W_B73,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B73.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B73, A_B73, E_B73, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

end Hardening
