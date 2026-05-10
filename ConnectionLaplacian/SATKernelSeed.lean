/-
ConnectionLaplacian/SATKernelSeed.lean

SAT-to-kernel seed theorem.

This file proves the exact finite statement that the Clay/P-vs-NP program can
honestly use as its first closed bridge: any decidable SAT predicate on a
finite assignment type has a canonical diagonal kernel operator whose
nontrivial kernel is equivalent to satisfiability.

This is not a polynomial-time reduction theorem. The assignment type may be
exponentially large in the ordinary bit-size of a formula. The missing P-vs-NP
work is exactly the uniform sparse/polynomial construction plus complexity
bound.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace ConnectionLaplacian

open Classical

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A Boolean assignment over `n` variables. -/
abbrev BoolAssignment (n : Nat) := Fin n → Bool

/-- A literal is a variable together with a polarity. `positive = true`
means the variable itself; `positive = false` means its negation. -/
structure Literal (n : Nat) where
  var : Fin n
  positive : Bool
deriving DecidableEq, Repr

/-- A clause is satisfied when at least one literal is satisfied. -/
def literalEval {n : Nat} (ρ : BoolAssignment n) (lit : Literal n) : Prop :=
  ρ lit.var = lit.positive

/-- A finite disjunctive clause. -/
abbrev Clause (n : Nat) := List (Literal n)

/-- A finite CNF formula. -/
abbrev CNF (n : Nat) := List (Clause n)

def clauseEval {n : Nat} (ρ : BoolAssignment n) (clause : Clause n) : Prop :=
  ∃ lit ∈ clause, literalEval ρ lit

def cnfEval {n : Nat} (ρ : BoolAssignment n) (cnf : CNF n) : Prop :=
  ∀ clause ∈ cnf, clauseEval ρ clause

instance {n : Nat} (ρ : BoolAssignment n) (lit : Literal n) :
    Decidable (literalEval ρ lit) := by
  unfold literalEval
  infer_instance

instance {n : Nat} (ρ : BoolAssignment n) (clause : Clause n) :
    Decidable (clauseEval ρ clause) := by
  unfold clauseEval
  infer_instance

instance {n : Nat} (ρ : BoolAssignment n) (cnf : CNF n) :
    Decidable (cnfEval ρ cnf) := by
  unfold cnfEval
  infer_instance

instance {n : Nat} (cnf : CNF n) :
    DecidablePred (fun ρ : BoolAssignment n => cnfEval ρ cnf) := by
  intro ρ
  infer_instance

/-- Diagonal SAT obstruction operator: satisfying assignments have zero
energy; non-satisfying assignments are multiplied by one. -/
noncomputable def satKernelOp (φ : A → Prop) [DecidablePred φ] (x : A → ℝ) : A → ℝ :=
  fun a => if φ a then 0 else x a

/-- Linear-map form of the diagonal SAT obstruction operator. -/
noncomputable def satKernelLinear (φ : A → Prop) [DecidablePred φ] : (A → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun := satKernelOp φ
  map_add' := by
    intro x y
    funext a
    by_cases hφ : φ a <;> simp [satKernelOp, hφ]
  map_smul' := by
    intro c x
    funext a
    by_cases hφ : φ a <;> simp [satKernelOp, hφ]

/-- A predicate is SAT iff its diagonal obstruction operator has a nonzero
kernel vector. -/
theorem sat_iff_nontrivial_kernel
    (φ : A → Prop) [DecidablePred φ] :
    (∃ x : A → ℝ, x ≠ 0 ∧ satKernelOp φ x = 0) ↔ ∃ a : A, φ a := by
  constructor
  · rintro ⟨x, hx_nonzero, hx_kernel⟩
    by_contra h_unsat
    apply hx_nonzero
    funext a
    have hφ : ¬ φ a := by
      intro ha
      exact h_unsat ⟨a, ha⟩
    have hx_a := congrFun hx_kernel a
    simpa [satKernelOp, hφ] using hx_a
  · rintro ⟨a0, ha0⟩
    let x : A → ℝ := fun a => if a = a0 then 1 else 0
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have h_at := congrFun hx a0
      simp [x] at h_at
    · funext a
      by_cases hφ : φ a
      · simp [satKernelOp, hφ]
      · have hne : a ≠ a0 := by
          intro h
          subst h
          exact hφ ha0
        simp [satKernelOp, hφ, x, hne]

/-- Linear-map kernel witness form of the finite SAT-to-kernel bridge. -/
theorem sat_iff_exists_nonzero_mem_linear_ker
    (φ : A → Prop) [DecidablePred φ] :
    (∃ x : A → ℝ, x ∈ LinearMap.ker (satKernelLinear φ) ∧ x ≠ 0) ↔ ∃ a : A, φ a := by
  rw [← sat_iff_nontrivial_kernel φ]
  constructor
  · rintro ⟨x, hx_mem, hx_nonzero⟩
    refine ⟨x, hx_nonzero, ?_⟩
    rw [LinearMap.mem_ker] at hx_mem
    exact hx_mem
  · rintro ⟨x, hx_nonzero, hx_kernel⟩
    refine ⟨x, ?_, hx_nonzero⟩
    rw [LinearMap.mem_ker]
    ext a
    exact congrFun hx_kernel a

/-- Linear-map kernel witness form for concrete finite CNF formulas. -/
theorem cnf_sat_iff_exists_nonzero_mem_linear_ker {n : Nat} (cnf : CNF n) :
    (∃ x : BoolAssignment n → ℝ,
        x ∈ LinearMap.ker (satKernelLinear (fun ρ : BoolAssignment n => cnfEval ρ cnf)) ∧
          x ≠ 0) ↔
      ∃ ρ : BoolAssignment n, cnfEval ρ cnf := by
  exact sat_iff_exists_nonzero_mem_linear_ker (fun ρ : BoolAssignment n => cnfEval ρ cnf)

/-- Submodule form of the finite SAT-to-kernel bridge. -/
theorem sat_iff_linear_ker_nontrivial
    (φ : A → Prop) [DecidablePred φ] :
    LinearMap.ker (satKernelLinear φ) ≠ ⊥ ↔ ∃ a : A, φ a := by
  rw [← sat_iff_exists_nonzero_mem_linear_ker φ]
  constructor
  · intro hker
    by_contra hno
    apply hker
    ext x
    constructor
    · intro hx
      have hx_zero : x = 0 := by
        by_contra hx_nonzero
        exact hno ⟨x, hx, hx_nonzero⟩
      simp [hx_zero]
    · intro hx
      have hx_zero : x = 0 := by
        simpa using hx
      rw [hx_zero]
      simp
  · rintro ⟨x, hx_mem, hx_nonzero⟩ hbot
    apply hx_nonzero
    have : x ∈ (⊥ : Submodule ℝ (A → ℝ)) := by
      simpa [hbot] using hx_mem
    simpa using this

/-- Submodule form for concrete finite CNF formulas. -/
theorem cnf_sat_iff_linear_ker_nontrivial {n : Nat} (cnf : CNF n) :
    LinearMap.ker (satKernelLinear (fun ρ : BoolAssignment n => cnfEval ρ cnf)) ≠ ⊥ ↔
      ∃ ρ : BoolAssignment n, cnfEval ρ cnf := by
  exact sat_iff_linear_ker_nontrivial (fun ρ : BoolAssignment n => cnfEval ρ cnf)

/-- Concrete CNF version of the SAT-to-kernel seed. -/
theorem cnf_sat_iff_nontrivial_kernel {n : Nat} (cnf : CNF n) :
    (∃ x : BoolAssignment n → ℝ,
        x ≠ 0 ∧ satKernelOp (fun ρ : BoolAssignment n => cnfEval ρ cnf) x = 0) ↔
      ∃ ρ : BoolAssignment n, cnfEval ρ cnf := by
  exact sat_iff_nontrivial_kernel (fun ρ : BoolAssignment n => cnfEval ρ cnf)

end ConnectionLaplacian
