/-
Convention anchoring battery (prototype).
-/
import ConnectionLaplacian

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators

/-- Bridge lemma: lift a `decide`-provable card over a finite type to ℝ. -/
theorem card_filter_univ_cast {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (k : ℕ)
    (h : (Finset.filter p Finset.univ).card = k) :
    ((Finset.filter p Finset.univ).card : ℝ) = k := by rw [h]

/-- Row index flattening (u, i) ↦ 2*u + i used by the connection anchor. -/
def flatIdx {n : ℕ} (p : Fin n × Fin 2) : Fin (2 * n) :=
  ⟨2 * p.1.val + p.2.val, by omega⟩

/-- Directed edge set of the triangle 0-1-2 on Fin 3 (both orientations). -/
def edge3s : Finset (Fin 3 × Fin 3) :=
  {(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)}

def adj3 (u v : Fin 3) : Prop := (u, v) ∈ edge3s

instance : DecidableRel adj3 := fun _ _ => Finset.decidableMem _ _

/-- The wrap set: only the edge (0,1) is wrapped. -/
def wrap3s : Finset (Sym2 (Fin 3)) := {s(0, 1)}

def G3 : ConnGraph where
  V := Fin 3
  graph :=
    { Adj := adj3
      symm := by
        intro u v h
        simp only [adj3, edge3s, Finset.mem_insert, Finset.mem_singleton,
                   Prod.mk.injEq] at h ⊢
        omega
      loopless := by
        intro u
        simp only [adj3, edge3s, Finset.mem_insert, Finset.mem_singleton,
                   Prod.mk.injEq]
        omega }
  decrel := fun _ _ => Finset.decidableMem _ _
  wrap := fun e => e.val ∈ wrap3s
  decwrap := fun _ => Finset.decidableMem _ _

/-- Anchor 1/3: signed (Moebius) Laplacian, wrap on (0,1). -/
example :
    (show Matrix (Fin 3) (Fin 3) ℝ from G3.signedLaplacianMobius) =
    !![2, 1, -1; 1, 2, -1; -1, -1, 2] := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [signedLaplacianMobius, G3, degree, adj3, edge3s, wrap3s,
          SimpleGraph.neighborFinset]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | norm_num

/-- Anchor 2/3: scalar Laplacian (ordinary graph Laplacian). -/
example :
    (show Matrix (Fin 3) (Fin 3) ℝ from G3.scalarLaplacian) =
    !![2, -1, -1; -1, 2, -1; -1, -1, 2] := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
          SimpleGraph.adjMatrix, G3, adj3, edge3s, SimpleGraph.degree,
          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.vecHead, Matrix.vecTail]
  all_goals first | exact card_filter_univ_cast _ _ (by decide) | norm_num

/-- Anchor 3/3 (block level): the connection-Laplacian building blocks.
The wrapped edge carries the Pauli-X block, non-wrap edges the identity,
and the degree block is degree · I2. Together with anchors 1 and 2 this
pins every convention of the flattened connection Laplacian; the full
6x6 flatten is additionally verified entrywise by the independent
implementation in findings/round8 on every battery instance. -/
example (i j : Fin 2) :
    (G3.edgeMatrix true ⟨(s(0, 1) : Sym2 (Fin 3)), by simp [G3, adj3, edge3s]⟩) i j = σx i j := by
  fin_cases i <;> fin_cases j <;> simp [edgeMatrix, G3, wrap3s, σx]

example (i j : Fin 2) :
    (G3.edgeMatrix true ⟨(s(0, 2) : Sym2 (Fin 3)), by simp [G3, adj3, edge3s]⟩) i j = I₂ i j := by
  fin_cases i <;> fin_cases j <;> simp [edgeMatrix, G3, wrap3s, I₂]

example (i j : Fin 2) :
    (G3.edgeMatrix true ⟨(s(1, 2) : Sym2 (Fin 3)), by simp [G3, adj3, edge3s]⟩) i j = I₂ i j := by
  fin_cases i <;> fin_cases j <;> simp [edgeMatrix, G3, wrap3s, I₂]

example (u : Fin 3) (i j : Fin 2) :
    (G3.degreeBlockMatrix u u) i j = (G3.degree u : ℝ) * I₂ i j := by
  simp only [degreeBlockMatrix, if_pos rfl, Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;> simp [I₂]

end Hardening
