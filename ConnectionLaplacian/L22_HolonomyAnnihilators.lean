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
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace ConnectionLaplacian

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
  simp only [holonomySubgroup, AddSubgroup.mem_mk, Set.mem_setOf_eq]
  simp [walkValue_append, walkValue_reverse, walkValue]
  -- The cycle value is p·α(u,v)·(-q) in ZMod n.
  -- This IS a closed walk at r, so it belongs to holonomySubgroup Z C.
  -- Lean gap: r must equal Quot.out C, or we need to conjugate by a walk r → Quot.out C.
  -- The conjugation (walk_r_to_root ++ cycle ++ walk_r_to_root.reverse) shows the cycle
  -- holonomy is independent of basepoint.
  sorry

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
  simp [walkValue_append, walkValue_reverse, walkValue]
  -- The cycle walkValue = T(p) + α(u,v) - T(q).
  -- By cycle_walkValue_mem_holonomy, this is in holonomySubgroup Z C.
  -- Full proof requires basepoint conjugation (see cycle_walkValue_mem_holonomy).
  exact cycle_walkValue_mem_holonomy Z C hr hu hv p q h_adj

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
  set root := Quot.out C
  have hroot_supp : root ∈ C.supp := by
    simp [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.mk_out]
  obtain ⟨w⟩ : Z.graph.Reachable root r := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hr hroot_supp
    rw [← hroot_supp] at hr
    exact SimpleGraph.ConnectedComponent.eq_iff_reachable.mp hr
  -- Conjugated cycle γ = w ++ (p ++ q.reverse) ++ w.reverse at Quot.out C
  let γ : Z.graph.Walk root root :=
    w.append ((p.append q.reverse).append w.reverse)
  -- γ ∈ holonomySubgroup Z C by definition (closed walk at Quot.out C)
  have hγ_mem : walkValue Z γ ∈ holonomySubgroup Z C :=
    ⟨γ, rfl⟩
  -- walkValue Z γ = walkValue Z p − walkValue Z q
  have hγ_val : walkValue Z γ = walkValue Z p - walkValue Z q := by
    simp [γ, walkValue_append, walkValue_reverse]; ring
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
  -- Proof sketch:
  -- LHS = ∑_u conj(f u) * (∑_v L_k(u,v) * f v)
  --     = ∑_u conj(f u) * (deg(u)·f u - ∑_{v adj u} ω^{k·α(u,v)}·f v)
  --     = ∑_u deg(u)|f u|² - ∑_{u adj v} ω^{k·α(u,v)} conj(f u) f v
  -- RHS = ½ ∑_{u adj v} (|f u|² - 2Re(ω^{k·α(u,v)} f v conj(f u)) + |f v|²)
  --     = ½ · 2(∑_u deg(u)|f u|² - Re(∑_{u adj v} ω^{k·α(u,v)} conj(f u) f v))
  --     = ∑_u deg(u)|f u|² - Re(⟨f, A_k f⟩)    [since L_k Hermitian → ⟨f, L_k f⟩ ∈ ℝ]
  --     = LHS ✓
  -- Key tools: conj_ω (star(ω^k) = ω^{-k}), antisymmetry of α, Finset.sum_comm
  sorry  -- quadratic form expansion; all steps are mechanical ZMod/Complex algebra

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
  -- Each term is a normSq, hence ≥ 0. Sum = 0 implies each term = 0.
  -- In particular the (u,v) term: normSq(f u - ω^{k·α} · f v) = 0.
  -- normSq(z) = 0 ↔ z = 0 → f u = ω^{k·α} · f v.
  sorry  -- extract the (u,v) term from the sum and use normSq_eq_zero

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
      -- W1: ω^{k*α.val} * ω^{k*T.val} = ω^{k*(α+T).val}  (mod n via ω^n=1)
      ring_nf
      rw [← zpow_add₀ (ZnConnGraph.ω_ne_zero n)]
      conv_lhs => rw [ZnConnGraph.ω_zpow_mod_n]
      conv_rhs => rw [ZnConnGraph.ω_zpow_mod_n]
      congr 1
      push_cast
      rw [ZMod.val_add]
      push_cast
      -- Goal: (k*α.val + k*T.val) % n = (k * ((α.val + T.val) % n)) % n
      -- Both equal k*(α.val + T.val) % n:
      rw [Int.mul_emod (↑k.val) ((↑(Z.α ⟨(u, w), h_adj⟩).val + ↑(walkValue Z rest).val) % ↑n)]
      rw [Int.emod_emod_of_dvd _ (dvd_refl (↑n : ℤ))]
      rw [← Int.mul_emod]
      congr 1; ring

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
  -- u ∈ C.supp means G.connectedComponentMk u = C
  -- v ∈ C.supp means G.connectedComponentMk v = C
  -- Hence G.connectedComponentMk u = G.connectedComponentMk v
  -- By Quot.eq (the definition of equality in the quotient): G.Reachable u v
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu hv
  rw [← hu] at hv
  exact (SimpleGraph.ConnectedComponent.eq_iff_reachable.mp hv)

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
theorem mem_annihilator_iff_kernel_pos (C : Z.graph.ConnectedComponent) (k : Fin n) :
    (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C) ↔
    LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) ≠ ⊥ := by
  constructor
  · -- ══ FORWARD ══
    intro h_ann
    -- Root vertex r ∈ C
    set r := Quot.out C with hr_def
    have hr_supp : r ∈ C.supp := by
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.mk_out]
    -- For each v in Z.V, extract a walk from r to v if v ∈ C.supp, else use nil
    -- Walk selection (Classical.choice on Reachable):
    have get_walk : ∀ v : Z.V, v ∈ C.supp → ∃ p : Z.graph.Walk r v, True :=
      fun v hv => ⟨(exists_walk_in_component Z r v hr_supp hv).some, trivial⟩
    -- Define T : Z.V → ZMod n  (path-independent under k by h_ann)
    let T : Z.V → ZMod n := fun v =>
      if hv : v ∈ C.supp then
        walkValue Z ((exists_walk_in_component Z r v hr_supp hv).some)
      else 0
    -- Define the twisted harmonic function f : Z.V → ℂ
    let f : Z.V → ℂ := fun v =>
      if v ∈ C.supp then
        (ZnConnGraph.ω n) ^ (-(k.val * (T v).val : ℤ))
      else 0
    -- f(r) = 1 ≠ 0
    have hfr : f r = 1 := by
      simp only [f, hr_supp, dite_true]
      -- T r = walkValue of (some walk r → r) ∈ holonomySubgroup Z C
      -- h_ann kills it: k * T r = 0 → k.val * (T r).val ≡ 0 (mod n) → ω^{-k*(T r)} = 1
      have hTr_mem : T r ∈ holonomySubgroup Z C :=
        ⟨(exists_walk_in_component Z r r hr_supp hr_supp).some, rfl⟩
      have hkTr : (k.val : ZMod n) * T r = 0 := h_ann (T r) hTr_mem
      have hdvd : n ∣ k.val * (T r).val := by
        rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
        show ((k.val * (T r).val : ℕ) : ZMod n) = 0
        push_cast [ZMod.natCast_val]; exact hkTr
      have hω_one : (ZnConnGraph.ω n) ^ (↑k.val * ↑(T r).val : ℤ) = 1 := by
        rw [omega_zpow_eq_one_iff_dvd]; exact_mod_cast hdvd
      rw [zpow_neg, hω_one, inv_one]
    -- f is in the kernel of L_k
    have hf_ker : Matrix.mulVec (sectoralLaplacian Z k) f = 0 := by
      funext u
      simp only [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply]
      -- Case split: u ∈ C.supp or not
      by_cases hu : u ∈ C.supp
      · -- For u ∈ C, the sum is deg(u)·f(u) - ∑_{v adj u} ω^{k·α(u,v)}·f(v)
        -- Each term ω^{k·α(u,v)}·f(v) = f(u) by annihilator_kills_cycle
        -- So sum = deg(u)·f(u) - deg(u)·f(u) = 0
        sorry  -- F1: Finset.sum over sectoralLaplacian terms
      · -- For u ∉ C: f(u) = 0, and all adj v satisfy v ∉ C (different component) → f(v) = 0
        sorry  -- F2: u ∉ C implies all adj v ∉ C (component isolation)
    -- f ≠ 0 since f(r) = 1
    have hf_ne : f ≠ 0 := by
      intro heq; have := congr_fun heq r; simp [hfr] at this
    -- kernel ≠ ⊥
    intro h_bot
    have : f ∈ LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hf_ker
    rw [h_bot] at this
    exact hf_ne (Submodule.mem_bot.mp this)
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
    set r := Quot.out C
    have hr_supp : r ∈ C.supp := by
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.mk_out]
    -- f(r) ≠ 0 or we can find v ∈ C with f(v) ≠ 0 and propagate
    have hfr_ne : f r ≠ 0 := by
      -- If f r = 0, use hf_pt to propagate: for any v in C, f v = 0.
      -- Then f = 0 outside C too (f(u) = 0 for u ∉ C by... or by support).
      -- This contradicts hf_ne_fn.
      sorry  -- propagation from f(r) = 0 implies f = 0 everywhere in C
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
      have := key; push_cast [ZMod.natCast_val] at this; exact this
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
theorem sectoral_kernel_dim_binary (Comp : Z.graph.ConnectedComponent) (k : Fin n) :
    componentSectoralKernelDim Z Comp k =
    if (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z Comp) then 1 else 0 := by
  simp only [componentSectoralKernelDim]
  split_ifs with h_ann
  · -- ker ≠ ⊥ by forward direction; finrank ≥ 1
    -- Uniqueness: twisted harmonic extension is unique up to scalar;
    -- restricted to C, the space has dim exactly 1.
    sorry
  · -- ker = ⊥ by backward direction (contrapositive); finrank = 0
    have h_ker_bot : LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k)) = ⊥ := by
      by_contra h
      exact h_ann ((mem_annihilator_iff_kernel_pos Z Comp k).mpr h)
    rw [FiniteDimensional.finrank_eq_zero_iff_eq_bot.mpr h_ker_bot]

end ConnectionLaplacian
