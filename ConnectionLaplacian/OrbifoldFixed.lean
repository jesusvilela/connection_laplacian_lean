/-
ConnectionLaplacian/OrbifoldFixed.lean

Finite orbifold λ-calculus scaffold. The exact Tier 0 content proved here is:
* cone wraps are periodic modulo the cone order,
* the orbifold Y combinator collapses to a cone-labelled fixed form,
* each computation orbit at a cone point of order `m` has exactly `m` phase-labelled normal forms.

This is a syntactic normal-form model, not a full λ-calculus normalization theorem.
-/

import ConnectionLaplacian.BerryHolonomy
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace ConnectionLaplacian

/-- A cone point with finite isotropy order `m ≥ 2`. -/
structure ConePoint where
  order : Nat
  hm : 2 ≤ order
  deriving DecidableEq, Repr

lemma ConePoint.order_pos (p : ConePoint) : 0 < p.order := by
  exact lt_of_lt_of_le (by decide : 0 < 2) p.hm

/-- Finite orbifold chart data. -/
structure OrbifoldSpace where
  cones : List ConePoint
  deriving Repr

/-- Orbifold Church terms, with explicit cone wrapping and normalized cone phases. -/
inductive OCTerm where
  | Var : Nat → OCTerm
  | Abs : Nat → OCTerm → OCTerm
  | App : OCTerm → OCTerm → OCTerm
  | ConeWrap : ConePoint → OCTerm → OCTerm
  | ConeNF : (p : ConePoint) → Fin p.order → OCTerm → OCTerm
  | YOrb : OCTerm
  deriving DecidableEq, Repr

/-- A canonical order-two cone used to record the Y-combinator fixed form. -/
def canonicalCone : ConePoint :=
  ⟨2, by omega⟩

/-- Residue class of a cone phase modulo the cone order. -/
def coneResidue (p : ConePoint) (n : Nat) : Fin p.order :=
  ⟨n % p.order, Nat.mod_lt _ p.order_pos⟩

namespace OCTerm

/-- Repeated cone wrapping, normalized modulo the cone order. -/
def cone_wrap_n (p : ConePoint) (t : OCTerm) (n : Nat) : OCTerm :=
  OCTerm.ConeNF p (coneResidue p n) t

end OCTerm

/-- Orbifold fixed-point combinator. -/
def Y_orb : OCTerm :=
  OCTerm.YOrb

/-- Canonical fixed form produced by the orbifold Y-combinator. -/
def yFixedForm (f : OCTerm) : OCTerm :=
  OCTerm.ConeNF canonicalCone ⟨0, canonicalCone.order_pos⟩ f

/-- One-step evaluator capturing cone normalization and the orbifold Y fixed-point law. -/
def OC_eval : OCTerm → OCTerm
  | OCTerm.ConeWrap p t => OCTerm.cone_wrap_n p t 1
  | OCTerm.App OCTerm.YOrb f => yFixedForm f
  | OCTerm.App f (OCTerm.App OCTerm.YOrb g) =>
      if _h : f = g then yFixedForm f else OCTerm.App f (OCTerm.App OCTerm.YOrb g)
  | t => t

/-- Reduction is represented by equality of one-step normal forms. -/
def OC_reduces_to (t nf : OCTerm) : Prop :=
  OC_eval t = nf

/-- Wrapping by a full cone period returns the same normalized cone phase. -/
theorem cone_wrap_period (p : ConePoint) (t : OCTerm) :
    OCTerm.cone_wrap_n p t p.order = OCTerm.cone_wrap_n p t 0 := by
  simp [OCTerm.cone_wrap_n, coneResidue, Nat.mod_self, p.order_pos.ne']

/-- The orbifold Y-combinator evaluates to its canonical cone-labelled fixed form. -/
theorem y_orb_fixpoint (f : OCTerm) :
    OC_eval (OCTerm.App Y_orb f) = yFixedForm f := by
  simp [Y_orb, OC_eval, yFixedForm]

/-- Away from the degenerate self-application `Y_orb`, the orbifold fixed-point law unfolds exactly. -/
theorem y_orb_fixpoint_unfold (f : OCTerm) (hf : f ≠ Y_orb) :
    OC_eval (OCTerm.App Y_orb f) = OC_eval (OCTerm.App f (OCTerm.App Y_orb f)) := by
  cases f <;> simp [Y_orb, OC_eval, yFixedForm] at hf ⊢

/-- Predicate recognizing cone-labelled normal forms. -/
def isConeNormalForm : OCTerm → Prop
  | OCTerm.ConeNF _ _ _ => True
  | _ => False

/-- The orbifold Y-combinator lands in a cone-labelled normal form. -/
theorem y_orb_converges_to_cone (f : OCTerm) :
    isConeNormalForm (OC_eval (OCTerm.App Y_orb f)) := by
  simp [y_orb_fixpoint, isConeNormalForm, yFixedForm]

/-- Extract the residue index from a normalized cone term. -/
def coneResidueValue : OCTerm → Nat
  | OCTerm.ConeNF _ k _ => k.1
  | _ => 0

/-- The `m` cone phases are pairwise distinct when indexed by `Fin p.order`. -/
def coneWrapEmbedding (p : ConePoint) (t : OCTerm) : Fin p.order ↪ OCTerm where
  toFun := fun k => OCTerm.cone_wrap_n p t k.1
  inj' := by
    intro a b hab
    apply Fin.ext
    have hval := congrArg coneResidueValue hab
    simpa [coneResidueValue, OCTerm.cone_wrap_n, coneResidue,
      Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] using hval

/-- The complete set of normalized cone phases of a term. -/
def coneNormalForms (p : ConePoint) (t : OCTerm) : Finset OCTerm :=
  Finset.univ.map (coneWrapEmbedding p t)

lemma mem_coneNormalForms (p : ConePoint) (t : OCTerm) (k : Fin p.order) :
    OCTerm.cone_wrap_n p t k.1 ∈ coneNormalForms p t := by
  simp [coneNormalForms, coneWrapEmbedding]

/-- Exactly `m` normalized orbifold phases occur over a cone of order `m`. -/
theorem cone_normal_forms (p : ConePoint) (t : OCTerm) :
    ∃ forms : Finset OCTerm, forms.card = p.order ∧
      ∀ n : Nat, ∃ nf ∈ forms, OC_reduces_to (OCTerm.cone_wrap_n p t n) nf := by
  refine ⟨coneNormalForms p t, ?_, ?_⟩
  · simp [coneNormalForms]
  · intro n
    let k : Fin p.order := coneResidue p n
    refine ⟨OCTerm.cone_wrap_n p t k.1, mem_coneNormalForms p t k, ?_⟩
    unfold OC_reduces_to
    simp [k, OC_eval, OCTerm.cone_wrap_n, coneResidue, Nat.mod_mod]

/-- Berry holonomy at a cone point agrees with the completed BerryHolonomy theorem. -/
theorem cone_point_berry_phase {M : Type*} (p : ConePoint) (loop : Fin (p.order + 1) → M) :
    berryPhase (coneBerryConnection (M := M) p.order) loop = 2 * Real.pi / p.order := by
  simpa using orbifold_cone_phase (M := M) p.order p.hm loop

/-- The order-four cone specializes to the quarter-turn Berry phase. -/
theorem z4_cone_point_phase :
    berryPhase (coneBerryConnection (M := Fin 5) 4) (fun i => i) = Real.pi / 2 := by
  simpa using z4_orbifold_phase

end ConnectionLaplacian
