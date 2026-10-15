/-
Convention battery SHARD B (generated).
See Hardening/ConventionBattery.lean header for provenance.
-/
import Hardening.BatteryPrelude

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators

set_option maxHeartbeats 4000000


def E_B2 : Finset (Fin 2 × Fin 2) := {(0, 1), (1, 0)}
def A_B2 (u v : Fin 2) : Prop := (u, v) ∈ E_B2
instance : DecidableRel A_B2 := fun _ _ => Finset.decidableMem _ _
def W_B2 : Finset (Sym2 (Fin 2)) := {}
def G_B2 : ConnGraph where
  V := Fin 2
  graph :=
    { Adj := A_B2
      symm := by
        intro u v h
        simp [A_B2, E_B2, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B2, E_B2, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B2
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 2) (Fin 2) ℝ from G_B2.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 2) => if u = 0 then if v = 0 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B2, degree, A_B2, E_B2, W_B2,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 2) (Fin 2) ℝ from G_B2.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 2) => if u = 0 then if v = 0 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B2, A_B2, E_B2, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B6 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0)}
def A_B6 (u v : Fin 3) : Prop := (u, v) ∈ E_B6
instance : DecidableRel A_B6 := fun _ _ => Finset.decidableMem _ _
def W_B6 : Finset (Sym2 (Fin 3)) := {s(0, 1)}
def G_B6 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B6
      symm := by
        intro u v h
        simp [A_B6, E_B6, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B6, E_B6, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B6
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B6.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B6, degree, A_B6, E_B6, W_B6,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B6.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B6, A_B6, E_B6, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B10 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (1, 2), (2, 1)}
def A_B10 (u v : Fin 3) : Prop := (u, v) ∈ E_B10
instance : DecidableRel A_B10 := fun _ _ => Finset.decidableMem _ _
def W_B10 : Finset (Sym2 (Fin 3)) := {s(0, 1), s(1, 2)}
def G_B10 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B10
      symm := by
        intro u v h
        simp [A_B10, E_B10, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B10, E_B10, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B10
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B10.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B10, degree, A_B10, E_B10, W_B10,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B10.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B10, A_B10, E_B10, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B14 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
def A_B14 (u v : Fin 3) : Prop := (u, v) ∈ E_B14
instance : DecidableRel A_B14 := fun _ _ => Finset.decidableMem _ _
def W_B14 : Finset (Sym2 (Fin 3)) := {s(1, 2)}
def G_B14 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B14
      symm := by
        intro u v h
        simp [A_B14, E_B14, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B14, E_B14, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B14
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B14.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B14, degree, A_B14, E_B14, W_B14,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B14.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B14, A_B14, E_B14, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B18 : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}
def A_B18 (u v : Fin 3) : Prop := (u, v) ∈ E_B18
instance : DecidableRel A_B18 := fun _ _ => Finset.decidableMem _ _
def W_B18 : Finset (Sym2 (Fin 3)) := {s(0, 1), s(0, 2), s(1, 2)}
def G_B18 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := A_B18
      symm := by
        intro u v h
        simp [A_B18, E_B18, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B18, E_B18, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B18
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B18.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B18, degree, A_B18, E_B18, W_B18,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 3) (Fin 3) ℝ from G_B18.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 3) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B18, A_B18, E_B18, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B22 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)}
def A_B22 (u v : Fin 4) : Prop := (u, v) ∈ E_B22
instance : DecidableRel A_B22 := fun _ _ => Finset.decidableMem _ _
def W_B22 : Finset (Sym2 (Fin 4)) := {s(2, 3)}
def G_B22 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B22
      symm := by
        intro u v h
        simp [A_B22, E_B22, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B22, E_B22, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B22
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B22.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B22, degree, A_B22, E_B22, W_B22,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B22.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B22, A_B22, E_B22, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B26 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)}
def A_B26 (u v : Fin 4) : Prop := (u, v) ∈ E_B26
instance : DecidableRel A_B26 := fun _ _ => Finset.decidableMem _ _
def W_B26 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(1, 2), s(2, 3)}
def G_B26 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B26
      symm := by
        intro u v h
        simp [A_B26, E_B26, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B26, E_B26, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B26
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B26.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B26, degree, A_B26, E_B26, W_B26,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B26.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B26, A_B26, E_B26, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B30 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0)}
def A_B30 (u v : Fin 4) : Prop := (u, v) ∈ E_B30
instance : DecidableRel A_B30 := fun _ _ => Finset.decidableMem _ _
def W_B30 : Finset (Sym2 (Fin 4)) := {s(0, 3)}
def G_B30 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B30
      symm := by
        intro u v h
        simp [A_B30, E_B30, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B30, E_B30, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B30
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B30.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B30, degree, A_B30, E_B30, W_B30,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B30.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B30, A_B30, E_B30, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B34 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0)}
def A_B34 (u v : Fin 4) : Prop := (u, v) ∈ E_B34
instance : DecidableRel A_B34 := fun _ _ => Finset.decidableMem _ _
def W_B34 : Finset (Sym2 (Fin 4)) := {s(0, 1), s(0, 2), s(0, 3)}
def G_B34 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B34
      symm := by
        intro u v h
        simp [A_B34, E_B34, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B34, E_B34, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B34
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B34.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B34, degree, A_B34, E_B34, W_B34,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B34.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B34, A_B34, E_B34, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B38 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B38 (u v : Fin 4) : Prop := (u, v) ∈ E_B38
instance : DecidableRel A_B38 := fun _ _ => Finset.decidableMem _ _
def W_B38 : Finset (Sym2 (Fin 4)) := {s(3, 0)}
def G_B38 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B38
      symm := by
        intro u v h
        simp [A_B38, E_B38, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B38, E_B38, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B38
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B38.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B38, degree, A_B38, E_B38, W_B38,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B38.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B38, A_B38, E_B38, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B42 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B42 (u v : Fin 4) : Prop := (u, v) ∈ E_B42
instance : DecidableRel A_B42 := fun _ _ => Finset.decidableMem _ _
def W_B42 : Finset (Sym2 (Fin 4)) := {s(1, 2), s(3, 0), s(0, 1)}
def G_B42 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B42
      symm := by
        intro u v h
        simp [A_B42, E_B42, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B42, E_B42, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B42
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B42.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B42, degree, A_B42, E_B42, W_B42,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B42.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B42, A_B42, E_B42, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B46 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 2), (2, 0)}
def A_B46 (u v : Fin 4) : Prop := (u, v) ∈ E_B46
instance : DecidableRel A_B46 := fun _ _ => Finset.decidableMem _ _
def W_B46 : Finset (Sym2 (Fin 4)) := {s(0, 2)}
def G_B46 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B46
      symm := by
        intro u v h
        simp [A_B46, E_B46, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B46, E_B46, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B46
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B46.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B46, degree, A_B46, E_B46, W_B46,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B46.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B46, A_B46, E_B46, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B50 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3), (0, 2), (2, 0)}
def A_B50 (u v : Fin 4) : Prop := (u, v) ∈ E_B50
instance : DecidableRel A_B50 := fun _ _ => Finset.decidableMem _ _
def W_B50 : Finset (Sym2 (Fin 4)) := {s(3, 0), s(0, 1)}
def G_B50 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B50
      symm := by
        intro u v h
        simp [A_B50, E_B50, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B50, E_B50, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B50
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B50.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B50, degree, A_B50, E_B50, W_B50,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B50.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else (2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B50, A_B50, E_B50, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B54 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)}
def A_B54 (u v : Fin 4) : Prop := (u, v) ∈ E_B54
instance : DecidableRel A_B54 := fun _ _ => Finset.decidableMem _ _
def W_B54 : Finset (Sym2 (Fin 4)) := {s(2, 3)}
def G_B54 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B54
      symm := by
        intro u v h
        simp [A_B54, E_B54, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B54, E_B54, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B54
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B54.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B54, degree, A_B54, E_B54, W_B54,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B54.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B54, A_B54, E_B54, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B58 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2)}
def A_B58 (u v : Fin 4) : Prop := (u, v) ∈ E_B58
instance : DecidableRel A_B58 := fun _ _ => Finset.decidableMem _ _
def W_B58 : Finset (Sym2 (Fin 4)) := {s(0, 2), s(1, 2), s(0, 1), s(1, 3), s(0, 3)}
def G_B58 : ConnGraph where
  V := Fin 4
  graph :=
    { Adj := A_B58
      symm := by
        intro u v h
        simp [A_B58, E_B58, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B58, E_B58, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B58
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B58.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (1 : ℝ) else (1 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (1 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B58, degree, A_B58, E_B58, W_B58,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 4) (Fin 4) ℝ from G_B58.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 4) => if u = 0 then if v = 0 then (3 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (3 : ℝ) else if v = 2 then (-1 : ℝ) else (-1 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (3 : ℝ) else (-1 : ℝ) else if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else (3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B58, A_B58, E_B58, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B62 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 4), (4, 3)}
def A_B62 (u v : Fin 5) : Prop := (u, v) ∈ E_B62
instance : DecidableRel A_B62 := fun _ _ => Finset.decidableMem _ _
def W_B62 : Finset (Sym2 (Fin 5)) := {s(3, 4)}
def G_B62 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B62
      symm := by
        intro u v h
        simp [A_B62, E_B62, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B62, E_B62, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B62
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B62.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B62, degree, A_B62, E_B62, W_B62,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B62.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B62, A_B62, E_B62, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B66 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1), (3, 4), (4, 3)}
def A_B66 (u v : Fin 5) : Prop := (u, v) ∈ E_B66
instance : DecidableRel A_B66 := fun _ _ => Finset.decidableMem _ _
def W_B66 : Finset (Sym2 (Fin 5)) := {s(0, 2), s(3, 4), s(0, 1)}
def G_B66 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B66
      symm := by
        intro u v h
        simp [A_B66, E_B66, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B66, E_B66, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B66
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B66.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B66, degree, A_B66, E_B66, W_B66,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B66.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (-1 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (-1 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (1 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B66, A_B66, E_B66, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B70 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B70 (u v : Fin 5) : Prop := (u, v) ∈ E_B70
instance : DecidableRel A_B70 := fun _ _ => Finset.decidableMem _ _
def W_B70 : Finset (Sym2 (Fin 5)) := {s(3, 0)}
def G_B70 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B70
      symm := by
        intro u v h
        simp [A_B70, E_B70, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B70, E_B70, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B70
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B70.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B70, degree, A_B70, E_B70, W_B70,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B70.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B70, A_B70, E_B70, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

def E_B74 : Finset (Fin 5 × Fin 5) := {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3)}
def A_B74 (u v : Fin 5) : Prop := (u, v) ∈ E_B74
instance : DecidableRel A_B74 := fun _ _ => Finset.decidableMem _ _
def W_B74 : Finset (Sym2 (Fin 5)) := {s(1, 2), s(3, 0), s(0, 1)}
def G_B74 : ConnGraph where
  V := Fin 5
  graph :=
    { Adj := A_B74
      symm := by
        intro u v h
        simp [A_B74, E_B74, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq] at h ⊢
        <;> omega
      loopless := by
        intro u
        simp [A_B74, E_B74, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
        <;> omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ W_B74
  decwrap := fun _ => Finset.decidableMem _ _

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B74.signedLaplacianMobius) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G_B74, degree, A_B74, E_B74, W_B74,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

example : (show Matrix (Fin 5) (Fin 5) ℝ from G_B74.scalarLaplacian) =
    (Matrix.of fun (u v : Fin 5) => if u = 0 then if v = 0 then (2 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 1 then if v = 0 then (-1 : ℝ) else if v = 1 then (2 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) else if u = 2 then if v = 0 then (0 : ℝ) else if v = 1 then (-1 : ℝ) else if v = 2 then (2 : ℝ) else if v = 3 then (-1 : ℝ) else (0 : ℝ) else if u = 3 then if v = 0 then (-1 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (-1 : ℝ) else if v = 3 then (2 : ℝ) else (0 : ℝ) else if v = 0 then (0 : ℝ) else if v = 1 then (0 : ℝ) else if v = 2 then (0 : ℝ) else if v = 3 then (0 : ℝ) else (0 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G_B74, A_B74, E_B74, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num

end Hardening
