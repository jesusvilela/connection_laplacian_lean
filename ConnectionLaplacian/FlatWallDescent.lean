import ConnectionLaplacian.L20_ZModConnection
import ConnectionLaplacian.SATKernelSeed
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Flat Wall Descent: The L0 Floor Theorem

This file proves the key sorry-free results about the Z/4 flat wall
(trivial connection, all holonomies = 0) that form the floor of the
P vs NP separation program.

These theorems are Tier 0 (Lean-checked). They do NOT prove P≠NP.
They establish the flat-wall floor: the trivial connection Laplacian
is positive semidefinite with a predictable kernel.
-/

namespace ConnectionLaplacian

open Matrix Complex

variable {n : Nat} [NeZero n]

/-- For trivial holonomy, the twisted Laplacian is the ordinary graph Laplacian. -/
theorem trivial_conn_laplacian_is_real
    (Z : ZnConnGraph n) (h_trivial : ∀ d, Z.α d = 0) :
    Z.laplacian = Z.graph.lapMatrix ℂ := by
  ext u v
  by_cases huv : u = v
  · subst huv
    simp [ZnConnGraph.laplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix]
  · by_cases hadj : Z.graph.Adj u v
    · simp [ZnConnGraph.laplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix, huv, hadj, h_trivial ⟨(u, v), hadj⟩]
    · simp [ZnConnGraph.laplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix, huv, hadj]

/-- Entrywise real form of the trivial-connection Laplacian. -/
theorem trivial_conn_laplacian_entry_real
    (Z : ZnConnGraph n) (h_trivial : ∀ d, Z.α d = 0) (u v : Z.V) :
    ∃ r : ℝ, Z.laplacian u v = (r : ℂ) := by
  rw [trivial_conn_laplacian_is_real Z h_trivial]
  by_cases huv : u = v
  · subst huv
    refine ⟨Z.graph.degree u, ?_⟩
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix]
  · by_cases hadj : Z.graph.Adj u v
    · refine ⟨-1, ?_⟩
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, huv, hadj]
    · refine ⟨0, ?_⟩
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, huv, hadj]

/-- The ordinary graph Laplacian is positive semidefinite. -/
theorem trivial_conn_laplacian_posSemidef (Z : ZnConnGraph n) :
    PosSemidef (Z.graph.lapMatrix ℝ) := by
  simpa using Z.graph.posSemidef_lapMatrix ℝ

/-- In `Z/4`, the uniform holonomy `2` contributes the phase `-1`. -/
theorem omega_sq_z4 : (ZnConnGraph.ω 4) ^ 2 = (-1 : ℂ) := by
  unfold ZnConnGraph.ω
  rw [sq]
  calc
    Complex.exp (2 * Real.pi * I / (4 : ℂ)) * Complex.exp (2 * Real.pi * I / (4 : ℂ))
        = Complex.exp (2 * Real.pi * I / (4 : ℂ) + 2 * Real.pi * I / (4 : ℂ)) := by
            rw [← Complex.exp_add]
    _ = Complex.exp (Real.pi * I) := by
            congr 1
            ring_nf
    _ = -1 := Complex.exp_pi_mul_I

/-- Two decoupled zero-energy charge sectors for the `h = 2` model. -/
noncomputable def starWallChargeSectorModel : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![(0 : ℂ), 0, 1, 1]

private noncomputable def twoSectorEmbedding :
    (Fin 2 → ℂ) →ₗ[ℂ] LinearMap.ker (Matrix.toLin' starWallChargeSectorModel) where
  toFun x :=
    ⟨![x 0, x 1, 0, 0], by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply', Matrix.mulVecLin_apply]
      ext i
      fin_cases i <;> simp [starWallChargeSectorModel, Matrix.mulVec_diagonal]⟩
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

private theorem twoSectorEmbedding_injective : Function.Injective twoSectorEmbedding := by
  intro x y hxy
  funext i
  fin_cases i
  · have h0 := congrArg (fun z : LinearMap.ker (Matrix.toLin' starWallChargeSectorModel) =>
        ((z : Fin 4 → ℂ) 0)) hxy
    simpa [twoSectorEmbedding] using h0
  · have h1 := congrArg (fun z : LinearMap.ker (Matrix.toLin' starWallChargeSectorModel) =>
        ((z : Fin 4 → ℂ) 1)) hxy
    simpa [twoSectorEmbedding] using h1

/-- A Tier-0 linear-algebra model for the `Z/4` star wall: there are at least
two independent zero-energy sectors. -/
theorem uniform_holonomy_2_kernel_dim_ge_2 :
    2 ≤ FiniteDimensional.finrank ℂ
      (LinearMap.ker (Matrix.toLin' starWallChargeSectorModel)) := by
  let ι := twoSectorEmbedding
  have hι : Function.Injective ι := twoSectorEmbedding_injective
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := ι) hι
  simpa [ι] using hdim

/-- A finite deterministic automaton over `Bool`. -/
structure DFA (α : Type) where
  State : Type
  instFintypeState : Fintype State
  instDecidableEqState : DecidableEq State
  start : State
  step : State → α → State
  accept : Set State

attribute [instance] DFA.instFintypeState DFA.instDecidableEqState

namespace DFA

/-- Run a DFA on a finite input word. -/
def run {α : Type} (M : DFA α) (w : List α) : M.State :=
  w.foldl M.step M.start

/-- Acceptance predicate for a DFA. -/
def Accepts {α : Type} (M : DFA α) (w : List α) : Prop :=
  M.run w ∈ M.accept

end DFA

/-- Toggle the parity state when reading `true`; keep it when reading `false`. -/
def parityStep : Bool → Bool → Bool := fun s a => xor s a

/-- The flat-wall language: words with even `true`-parity. -/
def flatWallLanguage : Set (List Bool) :=
  { w | w.foldl parityStep false = false }

/-- The two-state DFA recognizing the flat-wall language. -/
def parityDFA : DFA Bool where
  State := Bool
  instFintypeState := inferInstance
  instDecidableEqState := inferInstance
  start := false
  step := parityStep
  accept := {false}

/-- The trivial-holonomy flat wall is regular: a two-state DFA recognizes it. -/
theorem flat_wall_regular :
    ∃ M : DFA Bool, ∀ w : List Bool, w ∈ flatWallLanguage ↔ M.Accepts w := by
  refine ⟨parityDFA, ?_⟩
  intro w
  simp [flatWallLanguage, DFA.Accepts, DFA.run, parityDFA]

/-- The flat wall contributes only a regular-language certificate; the separate
SAT-to-kernel seed remains the finite diagonal bridge. This packages both Tier-0
facts without asserting any NP-hardness consequence. -/
theorem flat_wall_bridge_with_satKernelSeed {m : Nat} (cnf : CNF m) :
    (∃ M : DFA Bool, ∀ w : List Bool, w ∈ flatWallLanguage ↔ M.Accepts w) ∧
    ((∃ x : BoolAssignment m → ℝ, x ≠ 0 ∧
        satKernelOp (fun ρ : BoolAssignment m => cnfEval ρ cnf) x = 0) ↔
      ∃ ρ : BoolAssignment m, cnfEval ρ cnf) := by
  exact ⟨flat_wall_regular, cnf_sat_iff_nontrivial_kernel cnf⟩

end ConnectionLaplacian
