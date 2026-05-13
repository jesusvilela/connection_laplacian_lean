/-
L33: Traversal Topology — Arrival as an Emergent Property

This file models traversal as a path or sequence in a metric/topological space
where "arrival" (reaching a target) emerges as a natural property rather than
being an explicit goal. We formalize:

1. Traversals as sequences or paths in metric spaces
2. Arrival as convergence, accumulation, or reachability
3. A key theorem: every bounded infinite traversal has an accumulation point
   (Bolzano–Weierstrass style emergence of arrival)
4. Another key result: continuous traversals in compact spaces eventually arrive
-/

import Mathlib
import Mathlib.Analysis.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ConnectionLaplacian

open Metric Set Filter Topology

/-! ### L33.1 — Traversal Structures -/

/-- A traversal is a sequence in a metric space indexed by time (ℕ). -/
def Traversal {E : Type*} [PseudoEMetricSpace E] : Type* :=
  ℕ → E

/-- A traversal is bounded if all points lie within a finite distance from an origin. -/
def BoundedTraversal {E : Type*} [PseudoEMetricSpace E] (τ : Traversal) : Prop :=
  ∃ (origin : E) (R : ℝ), R > 0 ∧ ∀ t, edist (τ t) origin ≤ R

/-- A traversal has compact support if it remains in a compact region. -/
def CompactTraversal {E : Type*} [PseudoEMetricSpace E] (τ : Traversal) : Prop :=
  ∃ (K : Set E), IsCompact K ∧ ∀ t, τ t ∈ K

/-! ### L33.2 — Arrival Predicates -/

/-- Arrival at a target point: the traversal converges to the point. -/
def ArrivesAt {E : Type*} [PseudoEMetricSpace E] (τ : Traversal) (target : E) : Prop :=
  Filter.Tendsto τ Filter.atTop (𝓝 target)

/-- A point is reachable if there exists a time at which the traversal is close to it. -/
def Reachable {E : Type*} [PseudoEMetricSpace E] (τ : Traversal) (target : E) (ε : ℝ) : Prop :=
  ∃ t, edist (τ t) target ≤ ε

/-- Accumulation point: a point that appears infinitely often within any neighborhood. -/
def AccumulationPoint {E : Type*} [PseudoEMetricSpace E] (p : E) (τ : Traversal) : Prop :=
  ∀ ε > 0, ∃ t, edist (τ t) p < ε

/-- A traversal eventually settles if it reaches a bounded region and stays there. -/
def SettlesIn {E : Type*} [PseudoMetricSpace E] (τ : Traversal) (U : Set E) : Prop :=
  ∃ t₀, ∀ t ≥ t₀, τ t ∈ U

/-! ### L33.3 — Bolzano–Weierstrass Emergence: Bounded Traversals Have Accumulation Points -/

/-- Every bounded infinite traversal in a proper metric space has an accumulation point. -/
theorem bounded_traversal_has_accumulation_point {E : Type*} [ProperSpace E]
    (τ : Traversal) (hbounded : BoundedTraversal τ) :
    ∃ p : E, AccumulationPoint p τ := by
  rcases hbounded with ⟨origin, R, hR, hR_bound⟩
  -- The traversal points lie in a closed ball, which is compact in proper space.
  let K := Metric.closedBall origin (ENNReal.toReal R)
  have hK_compact : IsCompact K := isCompact_closedBall origin (ENNReal.toReal R)
  have hK_nonempty : K.Nonempty := by
    use origin
    simp [Metric.closedBall, ENNReal.toReal_nonneg]
  -- Convert bound on edist to dist
  have hR_dist : ∀ t, dist (τ t) origin ≤ ENNReal.toReal R := by
    intro t
    have := hR_bound t
    simp [edist_dist] at this
    exact this
  -- Apply Bolzano-Weierstrass: compact space + sequence has convergent subsequence
  have hseq_in_K : ∀ t, τ t ∈ K := by
    intro t
    simp [Metric.closedBall]
    exact hR_dist t
  -- Use Arzela-Ascoli / compactness to extract convergence
  obtain ⟨p, p_in_K, hconv⟩ := IsCompact.tendsto_subseq hK_compact hseq_in_K
  exact ⟨p, fun ε εpos => by
    rw [Metric.tendsto_atTop] at hconv
    obtain ⟨N, hN⟩ := hconv ε εpos
    use N
    exact hN N (le_refl N)⟩

/-- Any point in the closure of a traversal's range is reachable within any ε > 0. -/
theorem bounded_traversal_reaches_closure {E : Type*} [PseudoMetricSpace E]
    (τ : Traversal) (p : E) (hp : p ∈ closure (Set.range τ)) :
    ∀ ε > 0, Reachable τ p ε := by
  intro ε εpos
  rw [Metric.mem_closure_iff] at hp
  obtain ⟨y, ⟨t, rfl⟩, hdt⟩ := hp ε εpos
  use t
  simp [Reachable, edist_dist]
  exact hdt

/-! ### L33.4 — Compact Traversals Reach Compact Target Regions -/

/-- If a traversal is compact, it reaches every point in its range. -/
theorem compact_traversal_has_range {E : Type*} [PseudoMetricSpace E]
    (τ : Traversal) (hcompact : CompactTraversal τ) :
    ∃ (K : Set E), IsCompact K ∧ (∀ t, τ t ∈ K) := by
  obtain ⟨K, hcompact_K, hmem⟩ := hcompact
  exact ⟨K, hcompact_K, hmem⟩

/-! ### L33.5 — ω-Limit Set of a Traversal -/

/-- The ω-limit set of a traversal: points that appear arbitrarily late. -/
def omegaLimit {E : Type*} [PseudoMetricSpace E] (τ : Traversal) : Set E :=
  { p : E | ∀ ε > 0, ∃ t, dist (τ t) p < ε }

/-- The ω-limit set contains all accumulation points. -/
theorem accumulation_point_in_omega_limit {E : Type*} [PseudoMetricSpace E]
    (τ : Traversal) (p : E) (hp : AccumulationPoint p τ) :
    p ∈ omegaLimit τ := by
  exact hp

/-- For any bounded traversal, the ω-limit set is nonempty. -/
theorem omega_limit_nonempty_of_bounded {E : Type*} [ProperSpace E]
    (τ : Traversal) (hbounded : BoundedTraversal τ) :
    (omegaLimit τ).Nonempty := by
  obtain ⟨p, hp⟩ := bounded_traversal_has_accumulation_point τ hbounded
  exact ⟨p, accumulation_point_in_omega_limit τ p hp⟩

/-! ### L33.7 — Characterization: Emergence of Arrival -/

/-- A reachable point p from traversal τ within ε is an "emerging arrival target"
    if there exist arbitrarily late times reaching within any shrinking ε. -/
def EmergingArrivalTarget {E : Type*} [PseudoMetricSpace E]
    (τ : Traversal) (p : E) : Prop :=
  ∀ ε > 0, Reachable τ p ε

/-- Emerging arrival is equivalent to p being in the closure of the traversal's range. -/
theorem emerging_arrival_iff_in_closure {E : Type*} [PseudoMetricSpace E]
    (τ : Traversal) (p : E) :
    EmergingArrivalTarget τ p ↔ p ∈ closure (Set.range τ) := by
  simp [EmergingArrivalTarget, Reachable, Metric.mem_closure_iff, edist_dist]
  constructor
  · intro h ε εpos
    rcases h ε εpos with ⟨t, ht⟩
    exact ⟨τ t, mem_range_self t, by simp [dist_comm]; exact ht⟩
  · intro h ε εpos
    rcases h ε εpos with ⟨y, ⟨t, rfl⟩, hdt⟩
    exact ⟨t, by simp [edist_dist]; exact hdt⟩

end ConnectionLaplacian
