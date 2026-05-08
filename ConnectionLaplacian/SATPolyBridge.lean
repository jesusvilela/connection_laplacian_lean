/-
ConnectionLaplacian/SATPolyBridge.lean

Scaffold for the polynomial-size SAT-to-connection-kernel bridge.
This file records the intended graph/connection interface while leaving the
actual kernel equivalence as an explicit future obligation.
-/

import ConnectionLaplacian.SATKernelSeed
import ConnectionLaplacian.L20_ZModConnection
import Mathlib.Tactic

namespace ConnectionLaplacian

open Classical

/-- Embed an original SAT variable into the enlarged Tseitin vertex set. -/
def varVertex {n : Nat} (cnf : CNF n) (v : Fin n) : Fin (n + 2 * cnf.length) :=
  ⟨v.1, by
    have hv : v.1 < n := v.2
    nlinarith
  ⟩

/-- First helper vertex for clause `j`. -/
def clauseLeftVertex {n : Nat} (cnf : CNF n) (j : Fin cnf.length) : Fin (n + 2 * cnf.length) :=
  ⟨n + 2 * j.1, by
    have hj : j.1 < cnf.length := j.2
    nlinarith
  ⟩

/-- Second helper vertex for clause `j`. -/
def clauseRightVertex {n : Nat} (cnf : CNF n) (j : Fin cnf.length) : Fin (n + 2 * cnf.length) :=
  ⟨n + 2 * j.1 + 1, by
    have hj : j.1 < cnf.length := j.2
    nlinarith
  ⟩

/-- A variable occurs in clause `j`. -/
def varOccursInClause {n : Nat} (cnf : CNF n) (j : Fin cnf.length) (v : Fin n) : Prop :=
  ∃ lit ∈ cnf.get j, lit.var = v

/-- Clause `j` contains a negative occurrence of variable `v`. -/
def negativeOccursInClause {n : Nat} (cnf : CNF n) (j : Fin cnf.length) (v : Fin n) : Prop :=
  ∃ lit ∈ cnf.get j, lit.var = v ∧ lit.positive = false

/-- Clause-internal helper edge. -/
def helperEdge {n : Nat} (cnf : CNF n)
    (u v : Fin (n + 2 * cnf.length)) : Prop :=
  ∃ j : Fin cnf.length,
    (u = clauseLeftVertex cnf j ∧ v = clauseRightVertex cnf j) ∨
      (u = clauseRightVertex cnf j ∧ v = clauseLeftVertex cnf j)

/-- Clause-variable incidence edge. -/
def incidenceEdge {n : Nat} (cnf : CNF n)
    (u v : Fin (n + 2 * cnf.length)) : Prop :=
  ∃ j : Fin cnf.length, ∃ x : Fin n,
    varOccursInClause cnf j x ∧
      ((u = clauseRightVertex cnf j ∧ v = varVertex cnf x) ∨
        (u = varVertex cnf x ∧ v = clauseRightVertex cnf j))

/-- Prototype clause-variable incidence graph with two helper vertices per clause. -/
def tseitinGraph {n : Nat} (cnf : CNF n) : SimpleGraph (Fin (n + 2 * cnf.length)) where
  Adj u v := u ≠ v ∧ (helperEdge cnf u v ∨ incidenceEdge cnf u v)
  symm := by
    intro u v huv
    rcases huv with ⟨hne, hEdge⟩
    refine ⟨Ne.symm hne, ?_⟩
    rcases hEdge with hHelper | hInc
    · left
      rcases hHelper with ⟨j, hdir | hdir⟩
      · exact ⟨j, Or.inr ⟨hdir.2, hdir.1⟩⟩
      · exact ⟨j, Or.inl ⟨hdir.2, hdir.1⟩⟩
    · right
      rcases hInc with ⟨j, x, hocc, hdir⟩
      rcases hdir with hdir | hdir
      · exact ⟨j, x, hocc, Or.inr ⟨hdir.2, hdir.1⟩⟩
      · exact ⟨j, x, hocc, Or.inl ⟨hdir.2, hdir.1⟩⟩
  loopless := by
    intro u hu
    exact hu.1 rfl

/-- Endpoint-based Z/2 polarity tag: negative clause-variable incidences carry holonomy `1`. -/
noncomputable def tseitinConnOn {n : Nat} (cnf : CNF n)
    (u v : Fin (n + 2 * cnf.length)) : ZMod 2 :=
  if ∃ j : Fin cnf.length, ∃ x : Fin n,
      negativeOccursInClause cnf j x ∧
        ((u = clauseRightVertex cnf j ∧ v = varVertex cnf x) ∨
          (u = varVertex cnf x ∧ v = clauseRightVertex cnf j)) then 1 else 0

/-- Z/2 holonomy for the prototype graph. `L20_ZModConnection` packages connections on darts. -/
noncomputable def tseitinConn {n : Nat} (cnf : CNF n) : (tseitinGraph cnf).Dart → ZMod 2
  | ⟨(u, v), _⟩ => tseitinConnOn cnf u v

/-- Boolean global sections of the current Bergman-bundle scaffold. At this
stage, a section is definitionally just a Boolean assignment. -/
abbrev BergmanSection (n : Nat) := BoolAssignment n

/-- NP assignments are definitionally the same as global Boolean sections of the
current Bergman-bundle scaffold. -/
def assignment_section_isomorphism (n : Nat) :
    BoolAssignment n ≃ BergmanSection n :=
  Equiv.refl _

/-- Section space for the current SAT bridge scaffold: complex amplitudes on the
Boolean assignment bundle. -/
abbrev TseitinSection {n : Nat} (_cnf : CNF n) := BoolAssignment n → ℂ

/--
Assignment-indexed diagonal section operator. Satisfying assignments carry zero
energy, while unsatisfying assignments are left unchanged. Replacing this by the
actual sparse graph connection Laplacian is the remaining bridge work.
-/
noncomputable def tseitinSectionLinear {n : Nat} (cnf : CNF n) :
    TseitinSection cnf →ₗ[ℂ] TseitinSection cnf where
  toFun := fun x ρ => if cnfEval ρ cnf then 0 else x ρ
  map_add' := by
    intro x y
    funext ρ
    by_cases hρ : cnfEval ρ cnf <;> simp [hρ]
  map_smul' := by
    intro c x
    funext ρ
    by_cases hρ : cnfEval ρ cnf <;> simp [hρ]

/-- A CNF formula is satisfiable exactly when the current section operator has a
nonzero kernel section. -/
theorem cnf_sat_iff_exists_nonzero_mem_tseitin_linear_ker {n : Nat} (cnf : CNF n) :
    (∃ x : TseitinSection cnf,
        x ∈ LinearMap.ker (tseitinSectionLinear cnf) ∧ x ≠ 0) ↔
      ∃ ρ : BoolAssignment n, cnfEval ρ cnf := by
  constructor
  · rintro ⟨x, hx_mem, hx_nonzero⟩
    rw [LinearMap.mem_ker] at hx_mem
    by_contra h_unsat
    apply hx_nonzero
    funext ρ
    have hρ : ¬ cnfEval ρ cnf := by
      intro hsat
      exact h_unsat ⟨ρ, hsat⟩
    have hxρ := congrFun hx_mem ρ
    simpa [tseitinSectionLinear, hρ] using hxρ
  · rintro ⟨ρ0, hρ0⟩
    let x : TseitinSection cnf := fun ρ => if ρ = ρ0 then 1 else 0
    refine ⟨x, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      funext ρ
      by_cases hρ : cnfEval ρ cnf
      · simp [tseitinSectionLinear, hρ]
      · by_cases hEq : ρ = ρ0
        · subst hEq
          exact (hρ hρ0).elim
        · simp [tseitinSectionLinear, hρ, x, hEq]
    · intro hx
      have h_at := congrFun hx ρ0
      simp [x] at h_at

/-- Submodule form of the current SAT-to-section bridge. -/
theorem cnf_sat_iff_tseitin_linear_ker_nontrivial {n : Nat} (cnf : CNF n) :
    LinearMap.ker (tseitinSectionLinear cnf) ≠ ⊥ ↔ ∃ ρ : BoolAssignment n, cnfEval ρ cnf := by
  rw [← cnf_sat_iff_exists_nonzero_mem_tseitin_linear_ker cnf]
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
    have : x ∈ (⊥ : Submodule ℂ (TseitinSection cnf)) := by
      simpa [hbot] using hx_mem
    simpa using this

/--
Boundary of the current formalization:
* `tseitinGraph` exposes the intended polynomial-size vertex set.
* `tseitinConn` marks the clause-variable incidences where a negative literal
  should contribute the nontrivial `ZMod 2` holonomy.
* `assignment_section_isomorphism` identifies the present Bergman-bundle section
  object with Boolean assignments.
What remains is replacing the assignment-indexed section operator above by the
actual sparse graph connection Laplacian while preserving the same kernel test.
-/
theorem tseitin_kernel_iff_sat {n : Nat} (cnf : CNF n) :
    LinearMap.ker (satKernelLinear (fun ρ : BoolAssignment n => cnfEval ρ cnf)) ≠ ⊥ ↔
      LinearMap.ker (tseitinSectionLinear cnf) ≠ ⊥ := by
  rw [cnf_sat_iff_linear_ker_nontrivial, cnf_sat_iff_tseitin_linear_ker_nontrivial]

end ConnectionLaplacian
