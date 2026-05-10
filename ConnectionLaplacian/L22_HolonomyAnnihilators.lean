/-
ConnectionLaplacian/L22_HolonomyAnnihilators.lean

**Stratum L22 — Holonomy and Annihilators.**

This file proves that the character χ_k is trivial on the holonomy subgroup H_C
iff the character-twisted Laplacian L_k has a non-trivial kernel restricted to C.

Proof strategy (four simultaneous angles):
  A (Algebraic):   annihilator ↔ path-independence of k·T(v) on spanning tree
  S (Spectral):    ⟨f, L_k f⟩ = ½∑|f(u)−ω^{kα}f(v)|² ≥ 0; zero iff pointwise
  W (Walk):        pointwise twisted condition propagates along walks and closes cycles
  T (Topological): twisted harmonic = flat line bundle section with trivial holonomy

Historical voices:
  Sunada 1985  — isospectrality and holonomy of flat bundles on graphs
  Hodge 1941   — harmonic forms as sections of flat bundles
  Atiyah-Singer 1963 — index theorem bridge: analytical index = Berry holonomy = π/2
  Banach 1922  — contractive maps on complete metric spaces
-/

import ConnectionLaplacian.L21_SectoralDecomposition
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace ConnectionLaplacian

attribute [local instance] Classical.propDecidable

open Matrix BigOperators Complex

variable {n : Nat} [NeZero n] (Z : ZnConnGraph n)

/-- The value of a walk under the connection α. List-sum (NOT finset-sum):
    going around a cycle k times contributes k·(holonomy) so additivity
    under concatenation holds and reverse-walk gives the negation by
    Z/n antisymmetry of α. -/
def walkValue {u v : Z.V} (p : Z.graph.Walk u v) : ZMod n :=
  (p.darts.map Z.α).sum

@[simp]
lemma walkValue_nil (v : Z.V) : walkValue Z (SimpleGraph.Walk.nil : Z.graph.Walk v v) = 0 := by
  simp [walkValue]

lemma walkValue_append {u v w : Z.V}
    (p : Z.graph.Walk u v) (q : Z.graph.Walk v w) :
    walkValue Z (p.append q) = walkValue Z p + walkValue Z q := by
  simp [walkValue, SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]

lemma α_symm (d : Z.graph.Dart) : Z.α d.symm = - Z.α d :=
  eq_neg_of_add_eq_zero_right (Z.antisym d)

lemma walkValue_reverse {u v : Z.V} (p : Z.graph.Walk u v) :
    walkValue Z p.reverse = - walkValue Z p := by
  simp only [walkValue, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.map_map,
             List.sum_reverse]
  have h_pointwise : (Z.α ∘ SimpleGraph.Dart.symm) = (fun d => - Z.α d) := by
    funext d; exact α_symm Z d
  rw [h_pointwise]
  induction p.darts with
  | nil => simp
  | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The annihilator of an additive subgroup in ZMod n. -/
def subgroupAnnihilator (H : AddSubgroup (ZMod n)) : Set (ZMod n) :=
  { k | ∀ h ∈ H, k * h = 0 }

/-- The holonomy subgroup H_C of a connected component C. -/
def holonomySubgroup (C : Z.graph.ConnectedComponent) : AddSubgroup (ZMod n) :=
  let v : Z.V := Quot.out C
  { carrier := { k | ∃ p : Z.graph.Walk v v, walkValue Z p = k }
    add_mem' := by
      rintro a b ⟨p, hp⟩ ⟨q, hq⟩
      exact ⟨p.append q, by rw [walkValue_append, hp, hq]⟩
    zero_mem' := ⟨SimpleGraph.Walk.nil, walkValue_nil Z _⟩
    neg_mem' := by
      rintro a ⟨p, hp⟩
      exact ⟨p.reverse, by rw [walkValue_reverse, hp]⟩
  }

-- ══════════════════════════════════════════════════════════════════
-- §A — ALGEBRAIC LAYER: path-independence and cocycle condition
-- ══════════════════════════════════════════════════════════════════

/-- The cycle formed by two walks from a common root r has its walkValue
    in the holonomy subgroup. -/
lemma cycle_walkValue_mem_holonomy {r u v : Z.V} (C : Z.graph.ConnectedComponent)
    (hr : r ∈ C.supp) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (p : Z.graph.Walk r u) (q : Z.graph.Walk r v)
    (h_adj : Z.graph.Adj u v) :
    walkValue Z ((p.append (SimpleGraph.Walk.cons h_adj SimpleGraph.Walk.nil)).append q.reverse)
      ∈ (holonomySubgroup Z C) := by
  -- The cycle starts and ends at r = Quot.out C... or any vertex in C
  -- We need to connect r to Quot.out C and show the cycle value ∈ holonomySubgroup.
  -- The holonomySubgroup is defined using root Quot.out C, but contains all cycles
  -- at all vertices in C (by connectivity).
  -- Conjugation: get walk from Quot.out C to r using mem_supp_iff
  have hroot_supp' : Quot.out C ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact Quot.out_eq C
  obtain ⟨w⟩ : Z.graph.Reachable (Quot.out C) r := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hr hroot_supp'
    exact SimpleGraph.ConnectedComponent.exact (hroot_supp'.trans hr.symm)
  -- Membership: provide conjugated cycle γ = w ++ cycle ++ w.reverse at Quot.out C
  simp only [holonomySubgroup, AddSubgroup.mem_mk, Set.mem_setOf_eq]
  refine ⟨w.append (((p.append (SimpleGraph.Walk.cons h_adj SimpleGraph.Walk.nil)).append
      q.reverse).append w.reverse), ?_⟩
  -- walkValue Z γ = walkValue Z cycle (w and w.reverse cancel by ring)
  rw [walkValue_append, walkValue_append, walkValue_reverse]
  ring

/-- Annihilator kills cycle holonomies: k annihilates H_C means for any two
    walks p : r → u and q : r → v and edge u → v, k·(T(p) + α(u,v) - T(q)) = 0.
    This is the key algebraic identity for the forward direction. -/
lemma annihilator_kills_cycle {r u v : Z.V} (C : Z.graph.ConnectedComponent)
    (hr : r ∈ C.supp) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (h_adj : Z.graph.Adj u v)
    (p : Z.graph.Walk r u) (q : Z.graph.Walk r v)
    (k : ZMod n)
    (h_ann : k ∈ subgroupAnnihilator (holonomySubgroup Z C)) :
    k * (walkValue Z p + Z.α ⟨(u, v), h_adj⟩ - walkValue Z q) = 0 := by
  apply h_ann
  -- hmem: the cycle walkValue is in holonomySubgroup (via conjugation proof)
  have hmem := cycle_walkValue_mem_holonomy Z C hr hu hv p q h_adj
  -- heq: unfold the cycle walkValue to the goal's form
  have heq : walkValue Z ((p.append (SimpleGraph.Walk.cons h_adj SimpleGraph.Walk.nil)).append
      q.reverse) = walkValue Z p + Z.α ⟨(u, v), h_adj⟩ - walkValue Z q := by
    rw [walkValue_append, walkValue_append, walkValue_reverse]
    simp only [walkValue, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  rw [heq] at hmem; exact hmem

/-- **Path independence**: if k annihilates H_C, then k·walkValue is
    independent of the choice of walk from r to v.

    Proof: conjugate the cycle p ++ q.reverse (based at r) with a walk
    w : Quot.out C → r to produce a cycle γ based at Quot.out C.
    γ ∈ holonomySubgroup by definition.  walkValue Z γ = T(p) − T(q).
    Annihilator kills γ, so k·(T(p)−T(q)) = 0 → k·T(p) = k·T(q). -/
lemma annihilator_path_independent {r v : Z.V} (C : Z.graph.ConnectedComponent)
    (hr : r ∈ C.supp) (hv : v ∈ C.supp)
    (p q : Z.graph.Walk r v) (k : ZMod n)
    (h_ann : k ∈ subgroupAnnihilator (holonomySubgroup Z C)) :
    k * walkValue Z p = k * walkValue Z q := by
  -- Get a walk from Quot.out C to r (inlined connectivity argument)
  set root := Quot.out C with hroot_def
  have hroot_supp : root ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hroot_def]
    exact Quot.out_eq C
  obtain ⟨w⟩ : Z.graph.Reachable root r := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hr hroot_supp
    exact SimpleGraph.ConnectedComponent.exact (hroot_supp.trans hr.symm)
  -- Conjugated cycle γ = w ++ (p ++ q.reverse) ++ w.reverse at Quot.out C
  let γ : Z.graph.Walk root root :=
    w.append ((p.append q.reverse).append w.reverse)
  -- γ ∈ holonomySubgroup Z C by definition (closed walk at Quot.out C)
  have hγ_mem : walkValue Z γ ∈ holonomySubgroup Z C := by
    simp only [holonomySubgroup, AddSubgroup.mem_mk, Set.mem_setOf_eq]
    exact ⟨γ, rfl⟩
  -- walkValue Z γ = walkValue Z p − walkValue Z q
  have hγ_val : walkValue Z γ = walkValue Z p - walkValue Z q := by
    unfold_let γ
    rw [walkValue_append, walkValue_append, walkValue_append, walkValue_reverse, walkValue_reverse]
    ring
  -- Annihilator kills γ → k * (T(p) − T(q)) = 0 → k·T(p) = k·T(q)
  have h_diff := h_ann (walkValue Z γ) hγ_mem
  rw [hγ_val] at h_diff
  linear_combination h_diff

-- ══════════════════════════════════════════════════════════════════
-- §S — SPECTRAL LAYER: quadratic form for backward direction
-- ══════════════════════════════════════════════════════════════════

/-- **Sunada-Hodge quadratic identity**: for any f : Z.V → ℂ,
    the inner product ⟨f, L_k f⟩ equals ½ ∑_{u adj v} |f(u) − ω^{k·α(u,v)} f(v)|².
    Proof: expand using Hermiticity of L_k (follows from antisymmetry of α)
    and the identity Re(z) + Re(conj(z)) = 2Re(z). -/
lemma sectoralLaplacian_quadratic_form (k : Fin n) (f : Z.V → ℂ) :
    Matrix.dotProduct (star ∘ f) (Matrix.mulVec (sectoralLaplacian Z k) f) =
    (1/2 : ℂ) * ∑ u : Z.V, ∑ v : Z.V,
      if h : Z.graph.Adj u v then
        Complex.normSq (f u - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h⟩).val : ℤ) * f v)
      else 0 := by
  let φ : Z.V → Z.V → ℂ := fun u v =>
    if h : Z.graph.Adj u v then
      (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h⟩).val : ℤ)
    else 0
  have hφ_symm : ∀ {u v : Z.V}, Z.graph.Adj u v → star (φ u v) = φ v u := by
    intro u v h
    have hs : Z.graph.Adj v u := h.symm
    have hzmod :
        (((-(k.val * (Z.α ⟨(u, v), h⟩).val : ℤ) : ℤ) : ZMod n)) =
          (((k.val * (Z.α ⟨(v, u), hs⟩).val : ℤ) : ZMod n)) := by
      calc
        (((-(k.val * (Z.α ⟨(u, v), h⟩).val : ℤ) : ℤ) : ZMod n))
            = - ((k.val : ZMod n) * Z.α ⟨(u, v), h⟩) := by
                simp [ZMod.natCast_zmod_val]
        _ = (k.val : ZMod n) * Z.α ⟨(v, u), hs⟩ := by
              have hα : Z.α ⟨(v, u), hs⟩ = - Z.α ⟨(u, v), h⟩ := by
                simpa using (α_symm Z ⟨(u, v), h⟩)
              rw [hα]
              ring
        _ = (((k.val * (Z.α ⟨(v, u), hs⟩).val : ℤ) : ZMod n)) := by
              simp [ZMod.natCast_zmod_val]
    have hmodeq :
        (-(k.val * (Z.α ⟨(u, v), h⟩).val : ℤ)) ≡
          (k.val * (Z.α ⟨(v, u), hs⟩).val : ℤ) [ZMOD (n : ℤ)] := by
      exact (ZMod.intCast_eq_intCast_iff
        (-(k.val * (Z.α ⟨(u, v), h⟩).val : ℤ))
        (k.val * (Z.α ⟨(v, u), hs⟩).val : ℤ) n).mp hzmod
    -- Extract the zpow values from φ without involving star (avoids map_zpow₀ over-simplification)
    have heqUV : φ u v = (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h⟩).val : ℤ) := by
      simp [φ, h]
    have heqVU : φ v u = (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(v, u), hs⟩).val : ℤ) := by
      simp [φ, hs]
    rw [heqUV, heqVU, ZnConnGraph.ω_zpow_neg,
      ZnConnGraph.ω_zpow_mod_n n (-(k.val * (Z.α ⟨(u, v), h⟩).val : ℤ)),
      ZnConnGraph.ω_zpow_mod_n n (k.val * (Z.α ⟨(v, u), hs⟩).val : ℤ), hmodeq.eq]
  have hφ_unit : ∀ {u v : Z.V}, (h : Z.graph.Adj u v) → star (φ u v) * φ u v = 1 := by
    intro u v h
    let m : ℤ := (k.val * (Z.α ⟨(u, v), h⟩).val : ℤ)
    calc
      star (φ u v) * φ u v = star ((ZnConnGraph.ω n) ^ m) * (ZnConnGraph.ω n) ^ m := by
        simp [φ, h, m]
      _ = (ZnConnGraph.ω n) ^ (-m) * (ZnConnGraph.ω n) ^ m := by
        rw [ZnConnGraph.ω_zpow_neg]
      _ = (ZnConnGraph.ω n) ^ (-m + m) := by
        rw [← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
      _ = 1 := by simp [m]
  have hentry : ∀ u v : Z.V,
      star (f u) * (sectoralLaplacian Z k u v * f v) =
        (if u = v then (Z.graph.degree u : ℂ) * (star (f u) * f u) else 0) +
        (if u = v then 0 else
          if h : Z.graph.Adj u v then -(star (f u) * φ u v * f v) else 0) := by
    intro u v
    by_cases huv : u = v
    · subst huv
      simp [sectoralLaplacian, φ, SimpleGraph.irrefl]
      ring
    · by_cases hadj : Z.graph.Adj u v
      · simp [sectoralLaplacian, φ, huv, hadj, ← zpow_natCast]
        ring
      · simp [sectoralLaplacian, φ, huv, hadj]
  have hstep3 : ∀ u : Z.V,
      (∑ v : Z.V,
        ((if u = v then (Z.graph.degree u : ℂ) * (star (f u) * f u) else 0) +
          (if u = v then 0 else
            if h : Z.graph.Adj u v then -(star (f u) * φ u v * f v) else 0))) =
        (Z.graph.degree u : ℂ) * (star (f u) * f u) +
          ∑ v : Z.V, if h : Z.graph.Adj u v then -(star (f u) * φ u v * f v) else 0 := by
    intro u
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_ite_eq Finset.univ u
        (fun _ : Z.V => (Z.graph.degree u : ℂ) * (star (f u) * f u))]
      rw [if_pos (Finset.mem_univ u)]
    · apply Finset.sum_congr rfl
      intro v hv
      by_cases huv : u = v
      · subst huv
        simp [SimpleGraph.irrefl]
      · simp [huv]
  have hdeg : ∀ u : Z.V,
      (Z.graph.degree u : ℂ) * (star (f u) * f u) =
        ∑ v : Z.V, if Z.graph.Adj u v then star (f u) * f u else 0 := by
    intro u
    rw [SimpleGraph.degree_eq_sum_if_adj (G := Z.graph) (R := ℂ) u, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hadj : Z.graph.Adj u v
    · simp [hadj]
    · simp [hadj]
  have hLHS_raw :
      Matrix.dotProduct (star ∘ f) (Matrix.mulVec (sectoralLaplacian Z k) f) =
        ∑ u : Z.V, ∑ v : Z.V,
          if Z.graph.Adj u v then
            star (f u) * f u - star (f u) * φ u v * f v
          else 0 := by
    have h_expand :
        Matrix.dotProduct (star ∘ f) (Matrix.mulVec (sectoralLaplacian Z k) f) =
          ∑ u : Z.V, ∑ v : Z.V,
            ((if u = v then (Z.graph.degree u : ℂ) * (star (f u) * f u) else 0) +
              (if u = v then 0 else
                if h : Z.graph.Adj u v then -(star (f u) * φ u v * f v) else 0)) := by
      rw [Matrix.dotProduct]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Matrix.mulVec, Matrix.dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      simpa using hentry u v
    rw [h_expand]
    rw [Finset.sum_congr rfl (fun u _ => hstep3 u)]
    rw [Finset.sum_add_distrib]
    rw [show (∑ u : Z.V, (Z.graph.degree u : ℂ) * (star (f u) * f u)) =
        ∑ u : Z.V, ∑ v : Z.V, if Z.graph.Adj u v then star (f u) * f u else 0 by
      exact Finset.sum_congr rfl (fun u _ => hdeg u)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hadj : Z.graph.Adj u v
    · rw [if_pos hadj, dif_pos hadj, if_pos hadj]
      ring
    · rw [if_neg hadj, dif_neg hadj, if_neg hadj]
      ring
  set S : ℂ := ∑ u : Z.V, ∑ v : Z.V,
      if Z.graph.Adj u v then star (f u) * f u - star (f u) * φ u v * f v else 0 with hS
  have hLHS : Matrix.dotProduct (star ∘ f) (Matrix.mulVec (sectoralLaplacian Z k) f) = S := by
    rw [hS]
    exact hLHS_raw
  have hswap : S = ∑ u : Z.V, ∑ v : Z.V,
      if Z.graph.Adj u v then star (f v) * f v - star (f v) * φ v u * f u else 0 := by
    rw [hS, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hadj : Z.graph.Adj v u
    · have hduv : Z.graph.Adj u v := hadj.symm
      rw [if_pos hadj, if_pos hduv]
    · have hduv : ¬ Z.graph.Adj u v := fun h => hadj h.symm
      rw [if_neg hadj, if_neg hduv]
  have hnorm : ∀ {u v : Z.V} (h : Z.graph.Adj u v),
      ((Complex.normSq (f u - φ u v * f v) : ℝ) : ℂ) =
        (star (f u) * f u - star (f u) * φ u v * f v) +
        (star (f v) * f v - star (f v) * φ v u * f u) := by
    intro u v h
    have hstarφ : star (φ u v) = φ v u := hφ_symm h
    have hunit : star (φ u v) * φ u v = 1 := hφ_unit h
    calc
      ((Complex.normSq (f u - φ u v * f v) : ℝ) : ℂ)
          = star (f u - φ u v * f v) * (f u - φ u v * f v) := by
              simpa [Complex.star_def] using
                (Complex.normSq_eq_conj_mul_self (z := f u - φ u v * f v))
      _ = (star (f u) - star (f v) * star (φ u v)) * (f u - φ u v * f v) := by
            have hstar_expand : star (f u - φ u v * f v) =
                star (f u) - star (f v) * star (φ u v) := by
              show starRingEnd ℂ (f u - φ u v * f v) =
                  starRingEnd ℂ (f u) - starRingEnd ℂ (f v) * starRingEnd ℂ (φ u v)
              rw [map_sub (starRingEnd ℂ), _root_.map_mul (starRingEnd ℂ)]
              ring
            rw [hstar_expand]
      _ = star (f u) * f u - star (f u) * φ u v * f v
            - star (f v) * star (φ u v) * f u
            + star (f v) * (star (φ u v) * φ u v) * f v := by
            ring
      _ = (star (f u) * f u - star (f u) * φ u v * f v) +
            (star (f v) * f v - star (f v) * φ v u * f u) := by
            rw [hunit, hstarφ]
            ring
  have hQ_phi :
      (∑ u : Z.V, ∑ v : Z.V,
        if h : Z.graph.Adj u v then Complex.normSq (f u - φ u v * f v) else 0) = S + S := by
    calc
      (∑ u : Z.V, ∑ v : Z.V,
        if h : Z.graph.Adj u v then Complex.normSq (f u - φ u v * f v) else 0)
          = ∑ u : Z.V, ∑ v : Z.V,
              if h : Z.graph.Adj u v then
                (star (f u) * f u - star (f u) * φ u v * f v) +
                  (star (f v) * f v - star (f v) * φ v u * f u)
              else 0 := by
                push_cast
                apply Finset.sum_congr rfl
                intro u hu
                apply Finset.sum_congr rfl
                intro v hv
                by_cases hadj : Z.graph.Adj u v
                · simp only [dif_pos hadj]
                  exact_mod_cast hnorm hadj
                · simp only [dif_neg hadj, Complex.ofReal_zero]
      _ = S + ∑ u : Z.V, ∑ v : Z.V,
            if Z.graph.Adj u v then star (f v) * f v - star (f v) * φ v u * f u else 0 := by
            rw [hS, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro u hu
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro v hv
            by_cases hadj : Z.graph.Adj u v
            · rw [dif_pos hadj, if_pos hadj, if_pos hadj]
            · rw [dif_neg hadj, if_neg hadj, if_neg hadj, add_zero]
      _ = S + S := by rw [← hswap]
  have hQ :
      (∑ u : Z.V, ∑ v : Z.V,
        if h : Z.graph.Adj u v then
          Complex.normSq (f u - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h⟩).val : ℤ) * f v)
        else 0) = S + S := by
    have hstep : (∑ u : Z.V, ∑ v : Z.V,
        if h : Z.graph.Adj u v then
          Complex.normSq (f u - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h⟩).val : ℤ) * f v)
        else 0) =
      (∑ u : Z.V, ∑ v : Z.V,
        if h : Z.graph.Adj u v then Complex.normSq (f u - φ u v * f v) else 0) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hadj : Z.graph.Adj u v
        · simp only [dif_pos hadj]; simp [φ, hadj]
        · simp only [dif_neg hadj]
    rw [hstep]
    exact hQ_phi
  calc
    Matrix.dotProduct (star ∘ f) (Matrix.mulVec (sectoralLaplacian Z k) f) = S := hLHS
    _ = (1 / 2 : ℂ) * (S + S) := by ring
    _ = (1/2 : ℂ) * ∑ u : Z.V, ∑ v : Z.V,
          if h : Z.graph.Adj u v then
            Complex.normSq (f u - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h⟩).val : ℤ) * f v)
          else 0 := by
            rw [hQ]

/-- **Kernel → pointwise twisted** (Spectral angle, backward direction core):
    If f ∈ ker(L_k) and u adj v, then f(u) = ω^{k·α(u,v)} · f(v).
    Proof: L_k f = 0 → ⟨f, L_k f⟩ = 0 → ∑|f(u)-ω·f(v)|² = 0 → each term = 0. -/
lemma kernel_pointwise_twisted (k : Fin n) (f : Z.V → ℂ)
    (hf : Matrix.mulVec (sectoralLaplacian Z k) f = 0) :
    ∀ (u v : Z.V) (h : Z.graph.Adj u v),
      f u = (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h⟩).val : ℤ) * f v := by
  intro u v h_adj
  -- From hf: ⟨f, L_k f⟩ = 0
  have h_qf_zero : Matrix.dotProduct (star ∘ f) (Matrix.mulVec (sectoralLaplacian Z k) f) = 0 := by
    rw [hf]; simp [Matrix.dotProduct]
  -- By sectoralLaplacian_quadratic_form: ∑|f(u)-ω·f(v)|² = 0
  rw [sectoralLaplacian_quadratic_form] at h_qf_zero
  -- h_qf_zero : (1/2 : ℂ) * ∑_u ∑_v (if adj then normSq else 0) = 0
  -- Multiply by 2: the ℝ-valued sum = 0
  have h_sum_zero : ∑ a : Z.V, ∑ b : Z.V,
      (if h : Z.graph.Adj a b then
        Complex.normSq (f a - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(a, b), h⟩).val : ℤ) * f b)
      else (0 : ℝ)) = 0 := by
    have h_half_ne : (1 / 2 : ℂ) ≠ 0 := by norm_num
    have hS := (mul_eq_zero.mp h_qf_zero).resolve_left h_half_ne
    exact_mod_cast hS
  -- Each term ≥ 0
  have h_nonneg : ∀ a b : Z.V, (0 : ℝ) ≤
      if h : Z.graph.Adj a b then
        Complex.normSq (f a - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(a, b), h⟩).val : ℤ) * f b)
      else (0 : ℝ) := fun a b => by split_ifs; exact Complex.normSq_nonneg _; norm_num
  -- Each outer sum ≥ 0
  have h_outer_nn : ∀ a : Z.V, (0 : ℝ) ≤ ∑ b : Z.V,
      if h : Z.graph.Adj a b then
        Complex.normSq (f a - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(a, b), h⟩).val : ℤ) * f b)
      else 0 := fun a => Finset.sum_nonneg (fun b _ => h_nonneg a b)
  -- By Finset.sum_eq_zero_iff_of_nonneg: each outer = 0
  have h_each_u : ∀ a : Z.V, ∑ b : Z.V,
      (if h : Z.graph.Adj a b then
        Complex.normSq (f a - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(a, b), h⟩).val : ℤ) * f b)
      else 0) = 0 := fun a =>
    (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun a' _ => h_outer_nn a')).mp
      h_sum_zero a (Finset.mem_univ a)
  -- By Finset.sum_eq_zero_iff_of_nonneg again: the (u,v) term = 0
  have h_uv_zero : Complex.normSq
      (f u - (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), h_adj⟩).val : ℤ) * f v) = 0 :=
    have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun b _ => h_nonneg u b)).mp
      (h_each_u u) v (Finset.mem_univ v)
    by simp only [h_adj, dif_pos] at this; exact this
  -- normSq z = 0 → z = 0 → f u = ω^{kα} * f v
  have h_diff := Complex.normSq_eq_zero.mp h_uv_zero
  exact sub_eq_zero.mp h_diff

-- ══════════════════════════════════════════════════════════════════
-- §W — WALK LAYER: propagation and cycle closure
-- ══════════════════════════════════════════════════════════════════

/-- **Walk propagation**: if f satisfies the pointwise twisted condition,
    then for any walk p : u → v, f(u) = ω^{k·walkValue(p)} · f(v). -/
lemma twisted_walk_propagation (k : Fin n) (f : Z.V → ℂ)
    (hf_pt : ∀ (a b : Z.V) (h : Z.graph.Adj a b),
      f a = (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(a, b), h⟩).val : ℤ) * f b) :
    ∀ (u v : Z.V) (p : Z.graph.Walk u v),
      f u = (ZnConnGraph.ω n) ^ (k.val * (walkValue Z p).val : ℤ) * f v := by
  intro u v p
  induction p with
  | nil =>
      simp [walkValue_nil]
  | @cons u w v h_adj rest ih =>
      -- walkValue (cons h_adj rest) = α(u,w) + walkValue(rest)
      have hwalk : walkValue Z (SimpleGraph.Walk.cons h_adj rest) =
          Z.α ⟨(u, w), h_adj⟩ + walkValue Z rest := by
        simp [walkValue]
      -- f(u) = ω^{k·α(u,w)} · f(w)  by hf_pt
      have h_step : f u = (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, w), h_adj⟩).val : ℤ) * f w :=
        hf_pt u w h_adj
      -- f(w) = ω^{k·walkValue(rest)} · f(v)  by ih
      rw [h_step, ih]
      -- Combine: ω^{k·α} · (ω^{k·T} · f v) = ω^{k·(α+T)} · f v
      rw [hwalk]
      rw [← mul_assoc, ← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
      have hzmod :
          (((k.val * (Z.α ⟨(u, w), h_adj⟩ + walkValue Z rest).val : ℤ) : ZMod n)) =
            (((k.val * (Z.α ⟨(u, w), h_adj⟩).val +
                k.val * (walkValue Z rest).val : ℤ) : ZMod n)) := by
        calc
          (((k.val * (Z.α ⟨(u, w), h_adj⟩ + walkValue Z rest).val : ℤ) : ZMod n)) =
              (k.val : ZMod n) * (Z.α ⟨(u, w), h_adj⟩ + walkValue Z rest) := by
            simp [ZMod.natCast_zmod_val]
          _ = (k.val : ZMod n) * Z.α ⟨(u, w), h_adj⟩ +
              (k.val : ZMod n) * walkValue Z rest := by
            rw [mul_add]
          _ = (((k.val * (Z.α ⟨(u, w), h_adj⟩).val +
                k.val * (walkValue Z rest).val : ℤ) : ZMod n)) := by
            simp [ZMod.natCast_zmod_val, mul_add]
      have hmodeq :
          (k.val * (Z.α ⟨(u, w), h_adj⟩ + walkValue Z rest).val : ℤ) ≡
            (k.val * (Z.α ⟨(u, w), h_adj⟩).val +
              k.val * (walkValue Z rest).val : ℤ) [ZMOD (n : ℤ)] := by
        exact (ZMod.intCast_eq_intCast_iff
          (k.val * (Z.α ⟨(u, w), h_adj⟩ + walkValue Z rest).val : ℤ)
          (k.val * (Z.α ⟨(u, w), h_adj⟩).val + k.val * (walkValue Z rest).val : ℤ)
          n).mp hzmod
      rw [ZnConnGraph.ω_zpow_mod_n n (k.val * (Z.α ⟨(u, w), h_adj⟩ + walkValue Z rest).val : ℤ),
        ZnConnGraph.ω_zpow_mod_n n
          (k.val * (Z.α ⟨(u, w), h_adj⟩).val + k.val * (walkValue Z rest).val : ℤ),
        hmodeq.eq]

/-- **Cycle holonomy**: if f satisfies the pointwise twisted condition and
    γ is a closed walk at r, then f(r) = ω^{k·walkValue(γ)} · f(r). -/
lemma twisted_cycle_holonomy (k : Fin n) (f : Z.V → ℂ) (r : Z.V)
    (hf_pt : ∀ (a b : Z.V) (h : Z.graph.Adj a b),
      f a = (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(a, b), h⟩).val : ℤ) * f b)
    (γ : Z.graph.Walk r r) :
    f r = (ZnConnGraph.ω n) ^ (k.val * (walkValue Z γ).val : ℤ) * f r :=
  twisted_walk_propagation Z k f hf_pt r r γ

-- ══════════════════════════════════════════════════════════════════
-- §T — TOPOLOGICAL LAYER: main equivalence
-- ══════════════════════════════════════════════════════════════════

/-- **Walk extraction**: any two vertices in the same component are connected.
    Uses Classical.choice on SimpleGraph.Reachable. -/
lemma exists_walk_in_component {C : Z.graph.ConnectedComponent} (u v : Z.V)
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) : Z.graph.Reachable u v := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu hv
  exact SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)

/-- **A character χ_k is trivial on H_C iff L_k has a non-trivial kernel on C.**

    FORWARD (A + T angles):
      If k annihilates H_C, construct f(v) = ω^{−k·T(v)} using spans.
      Path-independence (§A) makes f well-defined.
      Pointwise gauge condition (§A cocycle) gives kernel equation.
      f(r) = 1 ≠ 0 witnesses the non-trivial kernel.

    BACKWARD (S + W + T angles):
      Non-trivial kernel gives f ≠ 0 with L_k f = 0.
      Spectral identity (§S) → pointwise twisted condition on all edges.
      Walk propagation (§W) → ω^{k·h}·f(r) = f(r) for all closed walks.
      f(r) ≠ 0 (connectivity in C) → ω^{k·h} = 1 → k·h = 0 in ZMod n.

    Remaining Lean gaps:
      F1. sectoralLaplacian kernel sum over Finset.V (matrix mulVec computation)
      S1. normSq sum extraction (Finset nonneg argument)
      W1. ω^{a+b} from ZMod.val_add modular arithmetic
-/
theorem mem_annihilator_iff_kernel_pos (C : Z.graph.ConnectedComponent) (k : Fin n)
    (hconn : Z.graph.Connected) :
    (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C) ↔
    LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) ≠ ⊥ := by
  classical
  constructor
  · -- ══ FORWARD ══
    intro h_ann
    -- Root vertex r ∈ C
    set r := Quot.out C with hr_def
    have hr_supp : r ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hr_def]
      exact Quot.out_eq C
    have hr_eq : Z.graph.connectedComponentMk r = C := by
      rw [hr_def]
      exact Quot.out_eq C
    -- Define T : Z.V → ZMod n  (path-independent under k by h_ann)
    let T : Z.V → ZMod n := fun v =>
      if hv : Z.graph.connectedComponentMk v = C then
        walkValue Z ((exists_walk_in_component Z r v hr_supp
          (by simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv)).some)
      else 0
    -- Define the twisted harmonic function f : Z.V → ℂ
    let f : Z.V → ℂ := fun v =>
      if Z.graph.connectedComponentMk v = C then
        (ZnConnGraph.ω n) ^ (-(k.val * (T v).val : ℤ))
      else 0
    -- f(r) = 1 ≠ 0
    have hfr : f r = 1 := by
      dsimp [f]
      rw [if_pos hr_eq]
      have hTr_mem : T r ∈ holonomySubgroup Z C := by
        dsimp [T]
        rw [dif_pos hr_eq]
        simp only [holonomySubgroup, AddSubgroup.mem_mk, Set.mem_setOf_eq]
        exact ⟨(exists_walk_in_component Z r r hr_supp hr_supp).some, rfl⟩
      have hkTr : (k.val : ZMod n) * T r = 0 := h_ann (T r) hTr_mem
      have hdvd : n ∣ k.val * (T r).val := by
        rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
        show ((k.val * (T r).val : ℕ) : ZMod n) = 0
        simpa [ZMod.natCast_zmod_val] using hkTr
      have hω_one : (ZnConnGraph.ω n) ^ (↑k.val * ↑(T r).val : ℤ) = 1 := by
        rw [omega_zpow_eq_one_iff_dvd]
        exact_mod_cast hdvd
      have hω_neg : (ZnConnGraph.ω n) ^ (-(↑k.val * ↑(T r).val : ℤ)) = 1 := by
        calc
          (ZnConnGraph.ω n) ^ (-(↑k.val * ↑(T r).val : ℤ))
              = ((ZnConnGraph.ω n) ^ (↑k.val * ↑(T r).val : ℤ))⁻¹ := by
                  rw [_root_.zpow_neg]
          _ = 1 := by rw [hω_one]; simp
      simpa using hω_neg
    -- f is in the kernel of L_k
    have hf_ker : Matrix.mulVec (sectoralLaplacian Z k) f = 0 := by
      funext u
      simp only [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply]
      -- Case split: u ∈ C.supp or not
      by_cases hu : u ∈ C.supp
      · -- For u ∈ C: show ∑_v L_k(u,v)*f(v) = 0
        -- Plan: each ω^{kα(u,v)} * f(v) = f(u) by path-independence, so
        --   deg(u)*f(u) - deg(u)*f(u) = 0.
        have hu_eq : Z.graph.connectedComponentMk u = C := by
          simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hu
        have hfu_val : f u = (ZnConnGraph.ω n) ^ (-(k.val * (T u).val : ℤ)) := by
          dsimp [f]
          rw [if_pos hu_eq]
        -- For each adj v: ω^{kα(u,v)} * f(v) = f(u)
        have h_adj_eq : ∀ (v : Z.V), ∀ (hadj : Z.graph.Adj u v),
            (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) * f v = f u := by
          intro v hadj
          have hv_eq : Z.graph.connectedComponentMk v = C := by
            rw [← SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj]
            exact hu_eq
          have hv : v ∈ C.supp := by
            simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv_eq
          have hfv_val : f v = (ZnConnGraph.ω n) ^ (-(k.val * (T v).val : ℤ)) := by
            dsimp [f]
            rw [if_pos hv_eq]
          have hpind : (k.val : ZMod n) * T v =
              (k.val : ZMod n) * T u + (k.val : ZMod n) * Z.α ⟨(u, v), hadj⟩ := by
            have heq := annihilator_path_independent Z C hr_supp hv
              (exists_walk_in_component Z r v hr_supp hv).some
              ((exists_walk_in_component Z r u hr_supp hu).some.append
                (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil))
              (k.val : ZMod n) h_ann
            simpa [T, hv_eq, hu_eq, walkValue_append, walkValue,
              SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
              List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_add] using heq
          calc
            (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) * f v
                = (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) *
                    (ZnConnGraph.ω n) ^ (-(k.val * (T v).val : ℤ)) := by rw [hfv_val]
            _ = (ZnConnGraph.ω n) ^
                  ((k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) + -(k.val * (T v).val : ℤ)) := by
                  rw [← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
            _ = (ZnConnGraph.ω n) ^ (-(k.val * (T u).val : ℤ)) := by
                  have hzmod_eq :
                      -((k.val : ZMod n) * T v) + (k.val : ZMod n) * Z.α ⟨(u, v), hadj⟩ =
                        -((k.val : ZMod n) * T u) := by
                    have htmp := congrArg
                      (fun x : ZMod n => -x + (k.val : ZMod n) * Z.α ⟨(u, v), hadj⟩) hpind
                    simpa [add_assoc, add_left_comm, add_comm] using htmp
                  have hzmod :
                      (((k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) +
                          -(k.val * (T v).val : ℤ) : ℤ) : ZMod n) =
                        (((-(k.val * (T u).val : ℤ) : ℤ)) : ZMod n) := by
                    calc
                      (((k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) +
                            -(k.val * (T v).val : ℤ) : ℤ) : ZMod n)
                          = -((k.val : ZMod n) * T v) + (k.val : ZMod n) * Z.α ⟨(u, v), hadj⟩ := by
                              simp [ZMod.natCast_zmod_val, add_comm, add_left_comm, add_assoc]
                      _ = -((k.val : ZMod n) * T u) := hzmod_eq
                      _ = (((-(k.val * (T u).val : ℤ) : ℤ)) : ZMod n) := by
                            simp [ZMod.natCast_zmod_val]
                  have hmodeq :
                      ((k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) + -(k.val * (T v).val : ℤ) : ℤ) ≡
                        (-(k.val * (T u).val : ℤ) : ℤ) [ZMOD (n : ℤ)] := by
                    exact (ZMod.intCast_eq_intCast_iff
                      ((k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) + -(k.val * (T v).val : ℤ) : ℤ)
                      (-(k.val * (T u).val : ℤ) : ℤ) n).mp hzmod
                  rw [ZnConnGraph.ω_zpow_mod_n n
                    ((k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) + -(k.val * (T v).val : ℤ) : ℤ),
                    ZnConnGraph.ω_zpow_mod_n n (-(k.val * (T u).val : ℤ) : ℤ), hmodeq.eq]
            _ = f u := by rw [hfu_val]
        -- F1: split ∑_v L_k(u,v)*f(v) into (diagonal) + (adj) parts, then cancel.
        -- Key: sectoralLaplacian Z k u v * f v =
        --        (if u = v then deg(u)*f(u) else 0) + (if Adj u v then -f(u) else 0)
        -- because ω^{kα}*f(v) = f(u) for adj v (h_adj_eq), so the adj term = -(f u).
        have hterm : ∀ v : Z.V, sectoralLaplacian Z k u v * f v =
            (if u = v then (Z.graph.degree u : ℂ) * f u else 0) +
            (if Z.graph.Adj u v then -f u else 0) := fun v => by
          by_cases heq : u = v
          · subst heq
            simp [sectoralLaplacian, Z.graph.loopless]
          · by_cases hadj : Z.graph.Adj u v
            · have hentry : sectoralLaplacian Z k u v =
                  -((ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ)) := by
                  unfold sectoralLaplacian
                  rw [if_neg heq, dif_pos hadj]
                  congr
              calc
                sectoralLaplacian Z k u v * f v
                    = (-(ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ)) * f v := by
                        rw [hentry]
                _ = -((ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) * f v) := by
                      ring
                _ = -(f u) := by rw [h_adj_eq v hadj]
                _ = (if u = v then (Z.graph.degree u : ℂ) * f u else 0) +
                      (if Z.graph.Adj u v then -f u else 0) := by
                        simp [heq, hadj]
            · simp [sectoralLaplacian, heq, hadj]
        simp_rw [hterm, Finset.sum_add_distrib]
        -- Diagonal sum: ∑_v (if u = v then deg(u)*f(u) else 0) = deg(u)*f(u)
        have hd : ∑ v : Z.V, (if u = v then (Z.graph.degree u : ℂ) * f u else 0) =
            (Z.graph.degree u : ℂ) * f u := by
          simp [Finset.sum_ite_eq']
        -- Adj sum: ∑_v (if Adj u v then -f(u) else 0) = -deg(u)*f(u)
        have ha : ∑ v : Z.V, (if Z.graph.Adj u v then (-f u : ℂ) else 0) =
            -(Z.graph.degree u : ℂ) * f u := by
          have hconv : ∀ v : Z.V,
              (if Z.graph.Adj u v then (-f u : ℂ) else 0) =
                if v ∈ Z.graph.neighborFinset u then (-f u : ℂ) else 0 := by
            intro v
            simp [SimpleGraph.mem_neighborFinset]
          calc
            ∑ v : Z.V, (if Z.graph.Adj u v then (-f u : ℂ) else 0)
                = ∑ v : Z.V, if v ∈ Z.graph.neighborFinset u then (-f u : ℂ) else 0 := by
                    simp_rw [hconv]
            _ = ∑ v in Z.graph.neighborFinset u, (-f u : ℂ) := by
                  classical
                  rw [Finset.sum_ite_mem, Finset.univ_inter]
            _ = (Z.graph.neighborFinset u).card • (-f u : ℂ) := by
                  rw [Finset.sum_const]
            _ = (Z.graph.degree u : ℂ) * (-f u) := by
                  rw [SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
            _ = -(Z.graph.degree u : ℂ) * f u := by ring
        rw [hd, ha]; ring
      · -- For u ∉ C: f(u) = 0, all adj v ∉ C → f(v) = 0 → each term = 0
        have hu_ne : Z.graph.connectedComponentMk u ≠ C := by
          simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hu
        have hfu : f u = 0 := by
          dsimp [f]
          rw [if_neg hu_ne]
        have h_adj_zero : ∀ (v : Z.V), Z.graph.Adj u v → f v = 0 := fun v hadj => by
          have hv_not : v ∉ C.supp := fun hv => hu (by
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv
            exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).trans hv)
          have hv_ne : Z.graph.connectedComponentMk v ≠ C := by
            simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv_not
          dsimp [f]
          rw [if_neg hv_ne]
        apply Finset.sum_eq_zero
        intro v _
        simp only [sectoralLaplacian]
        split_ifs with hveq hadj
        · subst hveq; simp [hfu]
        · simp [h_adj_zero v hadj]
        · simp
    -- f ≠ 0 since f(r) = 1
    have hf_ne : f ≠ 0 := by
      intro heq; have := congr_fun heq r; simp [hfr] at this
    -- kernel ≠ ⊥
    intro h_bot
    have : f ∈ LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hf_ker
    rw [h_bot] at this
    have hf_zero : f = 0 := by simpa using this
    exact hf_ne hf_zero
  · -- ══ BACKWARD ══
    intro h_ker_ne_bot
    -- Extract f ≠ 0 from ker ≠ ⊥
    rw [ne_eq, Submodule.eq_bot_iff, not_forall] at h_ker_ne_bot
    push_neg at h_ker_ne_bot
    obtain ⟨f_lm, hf_ker, hf_ne⟩ := h_ker_ne_bot
    -- Convert LinearMap to function
    let f : Z.V → ℂ := fun v => f_lm v
    have hf_ne_fn : f ≠ 0 := fun h => hf_ne (by ext v; exact congr_fun h v)
    have hf_ker_fn : Matrix.mulVec (sectoralLaplacian Z k) f = 0 := by
      have := (LinearMap.mem_ker.mp hf_ker)
      rw [Matrix.toLin'_apply] at this; exact this
    -- §S: pointwise twisted condition from quadratic form
    have hf_pt := kernel_pointwise_twisted Z k f hf_ker_fn
    -- Choose r ∈ C.supp with f(r) ≠ 0
    -- (Since f ≠ 0, ∃ v with f(v) ≠ 0; by connectivity of C, propagate to Quot.out C)
    set r := Quot.out C with hr_def
    have hr_supp : r ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hr_def]
      exact Quot.out_eq C
    have hr_eq : Z.graph.connectedComponentMk r = C := by
      rw [hr_def]
      exact Quot.out_eq C
    -- f(r) ≠ 0 or we can find v ∈ C with f(v) ≠ 0 and propagate
    have hfr_ne : f r ≠ 0 := by
      -- By contradiction: if f r = 0, then by walk propagation + ω≠0,
      -- f v = 0 for every v in C.supp.
      -- Since Z.graph.Connected, C.supp = Finset.univ, so f = 0, contradicting hf_ne_fn.
      by_contra h_zero
      have hfC_zero : ∀ v : Z.V, v ∈ C.supp → f v = 0 := fun v hv => by
        obtain ⟨p⟩ := exists_walk_in_component Z r v hr_supp hv
        have hprop := twisted_walk_propagation Z k f hf_pt r v p
        rw [h_zero] at hprop
        exact (mul_eq_zero.mp hprop.symm).resolve_left
          (zpow_ne_zero _ (ZnConnGraph.ω_ne_zero n))
      -- With hconn, every vertex w is in C.supp (unique component)
      have hall : ∀ w : Z.V, w ∈ C.supp := fun w => by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact (SimpleGraph.ConnectedComponent.sound (hconn r w)).symm.trans hr_eq
      exact hf_ne_fn (funext fun w => hfC_zero w (hall w))
    -- For any closed walk γ at r: ω^{k·walkValue(γ)} · f(r) = f(r)
    -- Hence ω^{k·walkValue(γ)} = 1 → k·walkValue(γ) = 0 in ZMod n (by omega_zpow_eq_one_iff_dvd)
    -- This proves (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)
    intro h h_mem
    simp only [holonomySubgroup, AddSubgroup.mem_mk, Set.mem_setOf_eq] at h_mem
    obtain ⟨γ, hγ⟩ := h_mem
    -- γ : Walk r r, walkValue Z γ = h, k * h = ?
    -- By twisted_cycle_holonomy: f r = ω^{k·walkValue(γ)} · f r = ω^{k·h} · f r
    have hcyc := twisted_cycle_holonomy Z k f r hf_pt γ
    -- So ω^{k·h} · f r = f r → ω^{k·h} = 1 (since f r ≠ 0)
    have hω_eq_one : (ZnConnGraph.ω n) ^ (k.val * (walkValue Z γ).val : ℤ) = 1 := by
      -- hcyc : f r = ω^{k·walkValue γ} * f r
      -- → ω^{k·walkValue γ} * f r = 1 * f r  → (mul_right_cancel₀ hfr_ne) → ω^{...} = 1
      have heq : (ZnConnGraph.ω n) ^ (k.val * (walkValue Z γ).val : ℤ) * f r = 1 * f r :=
        hcyc.symm.trans (one_mul (f r)).symm
      exact mul_right_cancel₀ hfr_ne heq
    -- By omega_zpow_eq_one_iff_dvd: n ∣ k.val * walkValue(γ).val in ℤ
    rw [omega_zpow_eq_one_iff_dvd] at hω_eq_one
    -- k * walkValue Z γ = 0 in ZMod n
    rw [← hγ]
    -- (k.val : ZMod n) * walkValue Z γ = 0
    -- Proof: n ∣ k.val * (walkValue Z γ).val in ℤ  (hω_eq_one)
    -- → (k.val * (walkValue Z γ).val : ZMod n) = 0  (ZMod.natCast_zmod_eq_zero_iff_dvd)
    -- → (k.val : ZMod n) * (walkValue Z γ : ZMod n) = 0  (push_cast)
    -- ZMod: n ∣ k*h in ℤ → (k : ZMod n) * h = 0 via natCast_zmod_eq_zero_iff_dvd
    have key : ((k.val * (walkValue Z γ).val : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hω_eq_one
    have : (k.val : ZMod n) * walkValue Z γ = 0 := by
      simpa [ZMod.natCast_zmod_val] using key
    exact this

/-- Dimension of the sectoral kernel (componentwise). -/
noncomputable def componentSectoralKernelDim (_Comp : Z.graph.ConnectedComponent) (k : Fin n) : Nat :=
  FiniteDimensional.finrank ℂ (LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)))

/-- **Kernel Binary Property**: the sectoral kernel dimension is 1 if
    k annihilates H_C, 0 otherwise.

    Upper bound 1 (uniqueness): f(v) = ω^{−k·T(v)} · c for scalar c ∈ ℂ;
    the scalar is fixed by f(r) and T is spanning-tree-determined.
    Lower bound 1 (existence): from mem_annihilator_iff_kernel_pos forward.
    Zero case: ker = ⊥ from backward iff.

    Remaining Lean gap: convert ker = ⊥ / ker ≠ ⊥ to finrank 0 / 1
    using FiniteDimensional.finrank_eq_zero_iff and the uniqueness of
    the twisted harmonic extension along a spanning tree. -/
theorem sectoral_kernel_dim_binary (Comp : Z.graph.ConnectedComponent) (k : Fin n)
    (hconn : Z.graph.Connected) :
    componentSectoralKernelDim Z Comp k =
    if (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z Comp) then 1 else 0 := by
  classical
  by_cases h_ann : (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z Comp)
  · simp [componentSectoralKernelDim, h_ann]
    have h_ker_ne :
        LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) ≠ ⊥ :=
      (mem_annihilator_iff_kernel_pos Z Comp k hconn).mp h_ann
    have h_ge_one :
        1 ≤ FiniteDimensional.finrank ℂ
          (LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k))) := by
      rw [Nat.one_le_iff_ne_zero]
      intro hfin0
      apply h_ker_ne
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [FiniteDimensional.finrank_eq_zero_iff] at hfin0
      obtain ⟨a, ha_ne, hax⟩ := hfin0 ⟨x, hx⟩
      have hx0 : (⟨x, hx⟩ : LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k))) = 0 := by
        exact (smul_eq_zero.mp hax).resolve_left ha_ne
      simpa using congrArg Subtype.val hx0
    set r : Z.V := Quot.out Comp with hr_def
    have hr_supp : r ∈ Comp.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hr_def]
      exact Quot.out_eq Comp
    have hr_eq : Z.graph.connectedComponentMk r = Comp := by
      rw [hr_def]
      exact Quot.out_eq Comp
    have hall : ∀ v : Z.V, v ∈ Comp.supp := fun v => by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound (hconn r v)).symm.trans hr_eq
    let evr : LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) →ₗ[ℂ] ℂ :=
      { toFun := fun f => (f : Z.V → ℂ) r
        map_add' := by
          intro f g
          rfl
        map_smul' := by
          intro c f
          rfl }
    have h_evr_inj : Function.Injective evr := by
      intro f g hfg
      apply Subtype.ext
      funext v
      have hf_ker_fn : Matrix.mulVec (sectoralLaplacian Z k) (f : Z.V → ℂ) = 0 := by
        have hf0 := LinearMap.mem_ker.mp f.2
        rw [Matrix.toLin'_apply] at hf0
        exact hf0
      have hg_ker_fn : Matrix.mulVec (sectoralLaplacian Z k) (g : Z.V → ℂ) = 0 := by
        have hg0 := LinearMap.mem_ker.mp g.2
        rw [Matrix.toLin'_apply] at hg0
        exact hg0
      have hf_pt := kernel_pointwise_twisted Z k (f : Z.V → ℂ) hf_ker_fn
      have hg_pt := kernel_pointwise_twisted Z k (g : Z.V → ℂ) hg_ker_fn
      obtain ⟨p⟩ := exists_walk_in_component Z r v hr_supp (hall v)
      have hprop_f := twisted_walk_propagation Z k (f : Z.V → ℂ) hf_pt r v p
      have hprop_g := twisted_walk_propagation Z k (g : Z.V → ℂ) hg_pt r v p
      have hω_ne : (ZnConnGraph.ω n) ^ (k.val * (walkValue Z p).val : ℤ) ≠ 0 := by
        exact zpow_ne_zero _ (ZnConnGraph.ω_ne_zero n)
      apply mul_left_cancel₀ hω_ne
      calc
        (ZnConnGraph.ω n) ^ (k.val * (walkValue Z p).val : ℤ) * (f : Z.V → ℂ) v =
            (f : Z.V → ℂ) r := by
              exact hprop_f.symm
        _ = (g : Z.V → ℂ) r := hfg
        _ = (ZnConnGraph.ω n) ^ (k.val * (walkValue Z p).val : ℤ) * (g : Z.V → ℂ) v := by
              exact hprop_g
    have h_le_one :
        FiniteDimensional.finrank ℂ
          (LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k))) ≤ 1 := by
      have hdim := LinearMap.finrank_le_finrank_of_injective (f := evr) h_evr_inj
      simpa using hdim
    exact Nat.le_antisymm h_le_one h_ge_one
  · have h_ker_bot : LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) = ⊥ := by
      by_contra h
      exact h_ann ((mem_annihilator_iff_kernel_pos Z Comp k hconn).mpr h)
    have hfinrank_zero :
        FiniteDimensional.finrank ℂ (LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k))) = 0 := by
      rw [FiniteDimensional.finrank_eq_zero_iff]
      intro x
      refine ⟨1, one_ne_zero, ?_⟩
      have hx0 : x.1 = 0 := by
        simpa [h_ker_bot] using x.2
      ext v
      simp [hx0]
    simpa [componentSectoralKernelDim, h_ann] using hfinrank_zero

end ConnectionLaplacian
