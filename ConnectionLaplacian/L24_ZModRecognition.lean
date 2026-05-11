/-
ConnectionLaplacian/L24_ZModRecognition.lean

**Stratum L24 — Recognition Theorem for Z/n Covers.**

The main kernel counting theorem for Z/n connection Laplacians:
the kernel dimension of the connection Laplacian on the n-fold cover 
equals the sum over connected components of n divided by the order of
the holonomy subgroup.
-/

import ConnectionLaplacian.KernelDimension
import ConnectionLaplacian.L22_HolonomyAnnihilators
import ConnectionLaplacian.L18_A5n

namespace ConnectionLaplacian

open Matrix BigOperators Complex FiniteDimensional

variable {n : Nat} [NeZero n] (Z : ZnConnGraph n)

/-- The annihilator of the holonomy subgroup of a connected component C,
    as a Finset of indices Fin n. These are the sector indices k where 
    (k : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C). -/
noncomputable def annihilator (C : Z.graph.ConnectedComponent) : Finset (Fin n) :=
  Finset.univ.filter fun k => (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)

private lemma finrank_ker_toLin'_blockDiagonal
    {K : Type*} [Field K]
    {o m : Type*} [Fintype o] [DecidableEq o] [Fintype m] [DecidableEq m]
    (M : o → Matrix m m K) :
    finrank K (LinearMap.ker (Matrix.toLin' (Matrix.blockDiagonal M))) =
      ∑ k : o, finrank K (LinearMap.ker (Matrix.toLin' (M k))) := by
  classical
  let e : (m × o) ≃ (o × m) := Equiv.prodComm _ _
  let N : Matrix (o × m) (o × m) K := fun ki lj =>
    if ki.1 = lj.1 then M ki.1 ki.2 lj.2 else 0
  have hN : N = Matrix.reindex e e (Matrix.blockDiagonal M) := by
    ext ki lj
    rcases ki with ⟨k, i⟩
    rcases lj with ⟨l, j⟩
    simp [N, e, Matrix.reindex_apply, Matrix.blockDiagonal_apply]
  have hreindex :
      finrank K (LinearMap.ker (Matrix.toLin' (Matrix.blockDiagonal M))) =
        finrank K (LinearMap.ker (Matrix.toLin' N)) := by
    rw [hN]
    simpa using (finrank_ker_toLin'_reindex (K := K) e (Matrix.blockDiagonal M)).symm
  have hker_iff :
      ∀ x : o × m → K, x ∈ LinearMap.ker (Matrix.toLin' N) ↔
        ∀ k : o, (fun i => x (k, i)) ∈ LinearMap.ker (Matrix.toLin' (M k)) := by
    intro x
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · intro hx k
      ext i
      have hxi := congrFun hx (k, i)
      simpa [N, Matrix.mulVec, Matrix.dotProduct, Matrix.reindex_apply,
        Matrix.blockDiagonal_apply, ← Finset.univ_product_univ, Finset.sum_product] using hxi
    · intro hx
      ext km
      rcases km with ⟨k, i⟩
      have hxi := congrFun (hx k) i
      simpa [N, Matrix.mulVec, Matrix.dotProduct, Matrix.reindex_apply,
        Matrix.blockDiagonal_apply, ← Finset.univ_product_univ, Finset.sum_product] using hxi
  let kerEq :
      LinearMap.ker (Matrix.toLin' N) ≃ₗ[K] ∀ k : o, LinearMap.ker (Matrix.toLin' (M k)) :=
    { toFun := fun v k => ⟨fun i => v.1 (k, i), (hker_iff v.1).mp v.2 k⟩
      invFun := fun f =>
        ⟨fun km => (f km.1 : m → K) km.2, (hker_iff _).mpr fun k => (f k).2⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext km
        rcases km with ⟨k, i⟩
        rfl
      right_inv := by
        intro f
        funext k
        apply Subtype.ext
        funext i
        rfl
      map_add' := by
        intro v w
        funext k
        apply Subtype.ext
        funext i
        rfl
      map_smul' := by
        intro c v
        funext k
        apply Subtype.ext
        funext i
        rfl }
  rw [hreindex, kerEq.finrank_eq, FiniteDimensional.finrank_pi_fintype]

private lemma finrank_ker_coverLaplacian_eq_sum :
    finrank ℂ (LinearMap.ker (Matrix.toLin' (coverLaplacian Z))) =
    ∑ k : Fin n, finrank ℂ (LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k))) := by
  classical
  obtain ⟨P, hPdet, hdiag⟩ := laplacian_sectoral_decomposition (Z := Z)
  have hPunit : IsUnit P.det := Ne.isUnit hPdet
  have hPinvdet : (P⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det (A := P) hPunit).ne_zero
  have hPP : (P⁻¹)⁻¹ = P := Matrix.nonsing_inv_nonsing_inv (A := P) hPunit
  have hdiag' :
      P⁻¹ * coverLaplacian Z * (P⁻¹)⁻¹ = Matrix.blockDiagonal (fun k : Fin n => sectoralLaplacian Z k) := by
    simpa [hPP] using hdiag
  calc
    finrank ℂ (LinearMap.ker (Matrix.toLin' (coverLaplacian Z))) =
        finrank ℂ (LinearMap.ker (Matrix.toLin'
          (P⁻¹ * coverLaplacian Z * (P⁻¹)⁻¹))) := by
            exact (finrank_ker_toLin'_conj (K := ℂ) (P := P⁻¹) (L := coverLaplacian Z) hPinvdet).symm
    _ = finrank ℂ (LinearMap.ker (Matrix.toLin'
          (Matrix.blockDiagonal (fun k : Fin n => sectoralLaplacian Z k)))) := by
            rw [hdiag']
    _ = ∑ k : Fin n, finrank ℂ (LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k))) := by
            simpa using finrank_ker_toLin'_blockDiagonal (K := ℂ)
              (M := fun k : Fin n => sectoralLaplacian Z k)

private lemma subgroupAnnihilator_card_eq_div (H : AddSubgroup (ZMod n)) :
    Nat.card { k : ZMod n // k ∈ subgroupAnnihilator H } = n / Nat.card H := by
  classical
  let ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H)
  let φ : ℤ →+ H := zmultiplesHom H g
  have hφn : φ n = 0 := by
    apply Subtype.ext
    change ((n : ℤ) • (g : ZMod n)) = 0
    simp [zsmul_eq_mul]
  let μ : ZMod n →+ H := ZMod.lift n ⟨φ, hφn⟩
  have hμ_apply (k : ZMod n) : ((μ k : H) : ZMod n) = k * (g : ZMod n) := by
    have hkval : (((k.val : ℤ) : ZMod n)) = k := by
      exact_mod_cast ZMod.natCast_zmod_val k
    rw [← hkval, ZMod.lift_coe]
    simp [φ, zsmul_eq_mul, mul_assoc]
  have hμ_surj : Function.Surjective μ := by
    intro x
    rcases hg x with ⟨m, hm⟩
    refine ⟨(m : ZMod n), ?_⟩
    apply Subtype.ext
    rw [hμ_apply]
    simpa [zsmul_eq_mul] using congrArg Subtype.val hm
  have hker_iff : ∀ k : ZMod n, k ∈ μ.ker ↔ k ∈ subgroupAnnihilator H := by
    intro k
    constructor
    · intro hk
      have hk0 : k * (g : ZMod n) = 0 := by
        have hk' : μ k = 0 := by simpa using hk
        exact by
          have := congrArg Subtype.val hk'
          simpa [hμ_apply] using this
      intro h hh
      rcases hg ⟨h, hh⟩ with ⟨m, hm⟩
      have hm0 : h = (m : ZMod n) * (g : ZMod n) := by
        symm
        simpa [zsmul_eq_mul] using congrArg Subtype.val hm
      rw [hm0]
      calc
        k * ((m : ZMod n) * (g : ZMod n)) = (m : ZMod n) * (k * (g : ZMod n)) := by ring
        _ = 0 := by simp [hk0]
    · intro hk
      change μ k = 0
      apply Subtype.ext
      simpa [hμ_apply] using hk (g : ZMod n) g.property
  have hker_card : Nat.card μ.ker = Nat.card { k : ZMod n // k ∈ subgroupAnnihilator H } := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun k => ⟨k.1, (hker_iff k.1).mp k.2⟩
        invFun := fun k => ⟨k.1, (hker_iff k.1).mpr k.2⟩
        left_inv := by intro k; cases k; rfl
        right_inv := by intro k; cases k; rfl }
  have hquot_card : Nat.card (ZMod n ⧸ μ.ker) = Nat.card H := by
    calc
      Nat.card (ZMod n ⧸ μ.ker) = Nat.card μ.range := by
        exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange μ).toEquiv
      _ = Nat.card H := by
        let eRange : μ.range ≃ H :=
          Equiv.ofBijective (fun y : μ.range => (y : H))
            ⟨Subtype.val_injective, by
              intro x
              rcases hμ_surj x with ⟨k, rfl⟩
              exact ⟨⟨μ k, ⟨k, rfl⟩⟩, rfl⟩⟩
        exact Nat.card_congr eRange
  have hcard : n = Nat.card H * Nat.card μ.ker := by
    calc
      n = Nat.card (ZMod n) := by simp
      _ = Nat.card (ZMod n ⧸ μ.ker) * Nat.card μ.ker := by
            simpa using (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (μ.ker))
      _ = Nat.card H * Nat.card μ.ker := by rw [hquot_card]
  have hdvd : Nat.card H ∣ n := ⟨Nat.card μ.ker, hcard⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H))
  calc
    Nat.card H * Nat.card { k : ZMod n // k ∈ subgroupAnnihilator H }
        = Nat.card H * Nat.card μ.ker := by rw [hker_card]
    _ = n := by exact hcard.symm
    _ = Nat.card H * (n / Nat.card H) := by rw [Nat.mul_div_cancel' hdvd]

lemma annihilator_card_eq_div (C : Z.graph.ConnectedComponent) :
    (annihilator Z C).card =
    n / Nat.card (holonomySubgroup Z C) := by
  classical
  let H := holonomySubgroup Z C
  have hcard :
      Nat.card { k : ZMod n // k ∈ subgroupAnnihilator H } = n / Nat.card H :=
    subgroupAnnihilator_card_eq_div (n := n) H
  let e : { k : Fin n // (k.val : ZMod n) ∈ subgroupAnnihilator H } ≃
      { k : ZMod n // k ∈ subgroupAnnihilator H } :=
    { toFun := fun k => ⟨k.1, k.2⟩
      invFun := fun k => ⟨⟨k.1.val, k.1.val_lt⟩, by simpa [ZMod.natCast_zmod_val] using k.2⟩
      left_inv := by
        intro k
        apply Subtype.ext
        apply Fin.ext
        simp [Nat.mod_eq_of_lt k.1.is_lt]
      right_inv := by
        intro k
        apply Subtype.ext
        simp [ZMod.natCast_zmod_val] }
  calc
    (annihilator Z C).card
        = Nat.card { k : Fin n // (k.val : ZMod n) ∈ subgroupAnnihilator H } := by
            rw [annihilator]
            rw [← Finset.card_subtype (p := fun k : Fin n => (k : ZMod n) ∈ subgroupAnnihilator H) Finset.univ]
            simp [Nat.card_eq_fintype_card, H]
    _ = Nat.card { k : ZMod n // k ∈ subgroupAnnihilator H } := Nat.card_congr e
    _ = n / Nat.card H := hcard
    _ = n / Nat.card (holonomySubgroup Z C) := by simp [H]

private lemma sectoralLaplacian_off_comp (k : Fin n) {u v : Z.V}
    (h : Z.graph.connectedComponentMk u ≠ Z.graph.connectedComponentMk v) :
    sectoralLaplacian Z k u v = 0 := by
  have huv : u ≠ v := by
    intro huv
    apply h
    simpa [huv]
  have hadj : ¬ Z.graph.Adj u v := by
    intro hadj
    apply h
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  simp [sectoralLaplacian, huv, hadj]

private lemma projComp_ker (k : Fin n) (C : Z.graph.ConnectedComponent) (f : Z.V → ℂ)
    (hf : Matrix.mulVec (sectoralLaplacian Z k) f = 0) :
    Matrix.mulVec (sectoralLaplacian Z k)
      (fun v => @ite ℂ (Z.graph.connectedComponentMk v = C)
        (Classical.propDecidable (Z.graph.connectedComponentMk v = C)) (f v) 0) = 0 := by
  classical
  funext u
  by_cases hu : Z.graph.connectedComponentMk u = C
  · calc
      ∑ v : Z.V, sectoralLaplacian Z k u v *
          (if Z.graph.connectedComponentMk v = C then f v else 0)
          = ∑ v : Z.V, sectoralLaplacian Z k u v * f v := by
              refine Finset.sum_congr rfl ?_
              intro v _
              by_cases hv : Z.graph.connectedComponentMk v = C
              · simp [hv]
              · have hentry : sectoralLaplacian Z k u v = 0 :=
                    sectoralLaplacian_off_comp (Z := Z) k (u := u) (v := v) (by
                      intro huv
                      apply hv
                      exact huv.symm.trans hu)
                simp [hv, hentry]
    _ = 0 := by
      simpa [Matrix.mulVec, Matrix.dotProduct] using congrFun hf u
  · have : ∑ v : Z.V, sectoralLaplacian Z k u v *
        (if Z.graph.connectedComponentMk v = C then f v else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        by_cases hv : Z.graph.connectedComponentMk v = C
        · have hentry : sectoralLaplacian Z k u v = 0 :=
              sectoralLaplacian_off_comp (Z := Z) k (u := u) (v := v) (by
                intro huv
                apply hu
                exact huv.trans hv)
          simp [hv, hentry]
        · simp [hv]
    simpa [Matrix.mulVec, Matrix.dotProduct] using this

private lemma forward_basisVec (k : Fin n) (C : Z.graph.ConnectedComponent)
    (h_ann : (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)) :
    ∃ bC : Z.V → ℂ,
      Matrix.mulVec (sectoralLaplacian Z k) bC = 0 ∧
      (∀ v : Z.V, Z.graph.connectedComponentMk v ≠ C → bC v = 0) ∧
      bC (Quot.out C) = 1 := by
  classical
  set r := Quot.out C with hr_def
  have hr_supp : r ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hr_def]
    exact Quot.out_eq C
  have hr_eq : Z.graph.connectedComponentMk r = C := by
    rw [hr_def]
    exact Quot.out_eq C
  let T : Z.V → ZMod n := fun v =>
    if hv : Z.graph.connectedComponentMk v = C then
      walkValue Z ((exists_walk_in_component Z r v hr_supp
        (by simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv)).some)
    else 0
  let bC : Z.V → ℂ := fun v =>
    if Z.graph.connectedComponentMk v = C then
      (ZnConnGraph.ω n) ^ (-(k.val * (T v).val : ℤ))
    else 0
  have hroot : bC r = 1 := by
    dsimp [bC]
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
  have hbC_ker : Matrix.mulVec (sectoralLaplacian Z k) bC = 0 := by
    funext u
    simp only [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply]
    by_cases hu : u ∈ C.supp
    · have hu_eq : Z.graph.connectedComponentMk u = C := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hu
      have hbu_val : bC u = (ZnConnGraph.ω n) ^ (-(k.val * (T u).val : ℤ)) := by
        dsimp [bC]
        rw [if_pos hu_eq]
      have h_adj_eq : ∀ (v : Z.V), ∀ (hadj : Z.graph.Adj u v),
          (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) * bC v = bC u := by
        intro v hadj
        have hv_eq : Z.graph.connectedComponentMk v = C := by
          rw [← SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj]
          exact hu_eq
        have hv : v ∈ C.supp := by
          simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv_eq
        have hbv_val : bC v = (ZnConnGraph.ω n) ^ (-(k.val * (T v).val : ℤ)) := by
          dsimp [bC]
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
          (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) * bC v
              = (ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) *
                  (ZnConnGraph.ω n) ^ (-(k.val * (T v).val : ℤ)) := by rw [hbv_val]
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
          _ = bC u := by rw [hbu_val]
      have hterm : ∀ v : Z.V, sectoralLaplacian Z k u v * bC v =
          (if u = v then (Z.graph.degree u : ℂ) * bC u else 0) +
          (if Z.graph.Adj u v then -bC u else 0) := fun v => by
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
              sectoralLaplacian Z k u v * bC v
                  = (-(ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ)) * bC v := by
                      rw [hentry]
              _ = -((ZnConnGraph.ω n) ^ (k.val * (Z.α ⟨(u, v), hadj⟩).val : ℤ) * bC v) := by
                    ring
              _ = -(bC u) := by rw [h_adj_eq v hadj]
              _ = (if u = v then (Z.graph.degree u : ℂ) * bC u else 0) +
                    (if Z.graph.Adj u v then -bC u else 0) := by
                      simp [heq, hadj]
          · simp [sectoralLaplacian, heq, hadj]
      simp_rw [hterm, Finset.sum_add_distrib]
      have hd : ∑ v : Z.V, (if u = v then (Z.graph.degree u : ℂ) * bC u else 0) =
          (Z.graph.degree u : ℂ) * bC u := by
        simp [Finset.sum_ite_eq']
      have ha : ∑ v : Z.V, (if Z.graph.Adj u v then (-bC u : ℂ) else 0) =
          -(Z.graph.degree u : ℂ) * bC u := by
        have hconv : ∀ v : Z.V,
            (if Z.graph.Adj u v then (-bC u : ℂ) else 0) =
              if v ∈ Z.graph.neighborFinset u then (-bC u : ℂ) else 0 := by
          intro v
          simp [SimpleGraph.mem_neighborFinset]
        calc
          ∑ v : Z.V, (if Z.graph.Adj u v then (-bC u : ℂ) else 0)
              = ∑ v : Z.V, if v ∈ Z.graph.neighborFinset u then (-bC u : ℂ) else 0 := by
                  simp_rw [hconv]
          _ = ∑ v in Z.graph.neighborFinset u, (-bC u : ℂ) := by
                classical
                rw [Finset.sum_ite_mem, Finset.univ_inter]
          _ = (Z.graph.neighborFinset u).card • (-bC u : ℂ) := by
                rw [Finset.sum_const]
          _ = (Z.graph.degree u : ℂ) * (-bC u) := by
                rw [SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
          _ = -(Z.graph.degree u : ℂ) * bC u := by ring
      rw [hd, ha]
      ring
    · have hu_ne : Z.graph.connectedComponentMk u ≠ C := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hu
      have h_adj_zero : ∀ (v : Z.V), Z.graph.Adj u v → bC v = 0 := fun v hadj => by
        have hv_not : v ∉ C.supp := fun hv => hu (by
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv
          exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).trans hv)
        have hv_ne : Z.graph.connectedComponentMk v ≠ C := by
          simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv_not
        dsimp [bC]
        rw [if_neg hv_ne]
      apply Finset.sum_eq_zero
      intro v _
      simp only [sectoralLaplacian]
      split_ifs with hveq hadj
      · subst hveq
        dsimp [bC]
        rw [if_neg hu_ne]
        simp
      · simp [h_adj_zero v hadj]
      · simp
  refine ⟨bC, hbC_ker, ?_, hroot⟩
  intro v hv
  dsimp [bC]
  rw [if_neg hv]

private lemma supported_ker_mem_ann (k : Fin n) (C : Z.graph.ConnectedComponent)
    (f : Z.V → ℂ) (hf : Matrix.mulVec (sectoralLaplacian Z k) f = 0)
    (hsupp : ∀ v : Z.V, Z.graph.connectedComponentMk v ≠ C → f v = 0)
    (hf_ne : f ≠ 0) :
    (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C) := by
  classical
  have hf_pt := kernel_pointwise_twisted Z k f hf
  set r := Quot.out C with hr_def
  have hr_supp : r ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hr_def]
    exact Quot.out_eq C
  have hfr_ne : f r ≠ 0 := by
    by_contra h_zero
    have hfC_zero : ∀ v : Z.V, v ∈ C.supp → f v = 0 := by
      intro v hv
      obtain ⟨p⟩ := exists_walk_in_component Z r v hr_supp hv
      have hprop := twisted_walk_propagation Z k f hf_pt r v p
      rw [h_zero] at hprop
      exact (mul_eq_zero.mp hprop.symm).resolve_left
        (zpow_ne_zero _ (ZnConnGraph.ω_ne_zero n))
    apply hf_ne
    funext v
    by_cases hv : v ∈ C.supp
    · exact hfC_zero v hv
    · have hv_ne : Z.graph.connectedComponentMk v ≠ C := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hv
      exact hsupp v hv_ne
  intro h h_mem
  simp only [holonomySubgroup, AddSubgroup.mem_mk, Set.mem_setOf_eq] at h_mem
  obtain ⟨γ, hγ⟩ := h_mem
  have hcyc := twisted_cycle_holonomy Z k f r hf_pt γ
  have hω_eq_one : (ZnConnGraph.ω n) ^ (k.val * (walkValue Z γ).val : ℤ) = 1 := by
    have heq : (ZnConnGraph.ω n) ^ (k.val * (walkValue Z γ).val : ℤ) * f r = 1 * f r :=
      hcyc.symm.trans (one_mul (f r)).symm
    exact mul_right_cancel₀ hfr_ne heq
  rw [omega_zpow_eq_one_iff_dvd] at hω_eq_one
  rw [← hγ]
  have key : ((k.val * (walkValue Z γ).val : ℕ) : ZMod n) = 0 := by
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hω_eq_one
  simpa [ZMod.natCast_zmod_val] using key

private noncomputable def annComponentCount (k : Fin n) : Nat := by
  classical
  exact (Finset.univ.filter fun C : Z.graph.ConnectedComponent =>
    (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)).card

private noncomputable def sectoralKer (k : Fin n) : Submodule ℂ (Z.V → ℂ) :=
  LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k))

private lemma annComponentCount_eq (k : Fin n) :
    annComponentCount Z k =
      (by
        classical
        exact (Finset.univ.filter fun C : Z.graph.ConnectedComponent =>
          (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)).card) := by
  rfl

set_option maxHeartbeats 800000 in
private lemma finrank_ker_sectoralLaplacian_eq_ann (k : Fin n) :
    finrank ℂ (LinearMap.ker (Matrix.toLin' (sectoralLaplacian Z k))) =
      annComponentCount Z k := by
  classical
  let p : Z.graph.ConnectedComponent → Prop := fun C =>
    (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)
  let I := { C : Z.graph.ConnectedComponent // p C }
  let Ker := sectoralKer Z k
  have hcardI : Fintype.card I = annComponentCount Z k := by
    rw [annComponentCount_eq]
    simp [I, p, Fintype.card_subtype]
  have hforward :
      ∀ i : I, ∃ bC : Z.V → ℂ,
        Matrix.mulVec (sectoralLaplacian Z k) bC = 0 ∧
        (∀ v : Z.V, Z.graph.connectedComponentMk v ≠ i.1 → bC v = 0) ∧
        bC (Quot.out i.1) = 1 := by
    intro i
    simpa [p] using forward_basisVec (Z := Z) k i.1 i.2
  choose b hbker hbsupp hbroot using hforward
  let basisVec : I → Ker := fun i =>
    ⟨b i, by
      change b i ∈ sectoralKer Z k
      rw [sectoralKer, LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hbker i⟩
  let φ : Ker →ₗ[ℂ] I → ℂ :=
    { toFun := fun f i => (f : Z.V → ℂ) (Quot.out i.1)
      map_add' := by intro f g; funext i; rfl
      map_smul' := by intro c f; funext i; rfl }
  have hφ_inj : Function.Injective φ := by
    intro f g hfg
    apply Subtype.ext
    funext v
    have hf_ker : Matrix.mulVec (sectoralLaplacian Z k) (f : Z.V → ℂ) = 0 := by
      have hf0 := LinearMap.mem_ker.mp f.2
      rw [Matrix.toLin'_apply] at hf0
      exact hf0
    have hg_ker : Matrix.mulVec (sectoralLaplacian Z k) (g : Z.V → ℂ) = 0 := by
      have hg0 := LinearMap.mem_ker.mp g.2
      rw [Matrix.toLin'_apply] at hg0
      exact hg0
    have hf_pt := kernel_pointwise_twisted Z k (f : Z.V → ℂ) hf_ker
    have hg_pt := kernel_pointwise_twisted Z k (g : Z.V → ℂ) hg_ker
    let C : Z.graph.ConnectedComponent := Z.graph.connectedComponentMk v
    by_cases hC : p C
    · have hroot_supp : Quot.out C ∈ C.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact Quot.out_eq C
      have hv_supp : v ∈ C.supp := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff, C]
      obtain ⟨q⟩ := exists_walk_in_component Z (Quot.out C) v hroot_supp hv_supp
      have hroot_eq : (f : Z.V → ℂ) (Quot.out C) = (g : Z.V → ℂ) (Quot.out C) := by
        simpa [φ] using congrFun hfg ⟨C, hC⟩
      have hprop_f := twisted_walk_propagation Z k (f : Z.V → ℂ) hf_pt (Quot.out C) v q
      have hprop_g := twisted_walk_propagation Z k (g : Z.V → ℂ) hg_pt (Quot.out C) v q
      have hω_ne : (ZnConnGraph.ω n) ^ (k.val * (walkValue Z q).val : ℤ) ≠ 0 := by
        exact zpow_ne_zero _ (ZnConnGraph.ω_ne_zero n)
      apply mul_left_cancel₀ hω_ne
      calc
        (ZnConnGraph.ω n) ^ (k.val * (walkValue Z q).val : ℤ) * (f : Z.V → ℂ) v
            = (f : Z.V → ℂ) (Quot.out C) := by exact hprop_f.symm
        _ = (g : Z.V → ℂ) (Quot.out C) := hroot_eq
        _ = (ZnConnGraph.ω n) ^ (k.val * (walkValue Z q).val : ℤ) * (g : Z.V → ℂ) v := by
              exact hprop_g
    · let fC : Z.V → ℂ := fun w => if Z.graph.connectedComponentMk w = C then (f : Z.V → ℂ) w else 0
      let gC : Z.V → ℂ := fun w => if Z.graph.connectedComponentMk w = C then (g : Z.V → ℂ) w else 0
      have hfC_ker : Matrix.mulVec (sectoralLaplacian Z k) fC = 0 := by
        simpa [fC] using projComp_ker (Z := Z) k C (f : Z.V → ℂ) hf_ker
      have hgC_ker : Matrix.mulVec (sectoralLaplacian Z k) gC = 0 := by
        simpa [gC] using projComp_ker (Z := Z) k C (g : Z.V → ℂ) hg_ker
      have hfC_zero : fC = 0 := by
        by_contra hfC_ne
        exact hC (supported_ker_mem_ann (Z := Z) k C fC hfC_ker
          (by intro w hw; simp [fC, hw]) hfC_ne)
      have hgC_zero : gC = 0 := by
        by_contra hgC_ne
        exact hC (supported_ker_mem_ann (Z := Z) k C gC hgC_ker
          (by intro w hw; simp [gC, hw]) hgC_ne)
      have hvC : Z.graph.connectedComponentMk v = C := by
        simp [C]
      have hfv_zero : (f : Z.V → ℂ) v = 0 := by
        have hfv := congrFun hfC_zero v
        simpa [fC, hvC] using hfv
      have hgv_zero : (g : Z.V → ℂ) v = 0 := by
        have hgv := congrFun hgC_zero v
        simpa [gC, hvC] using hgv
      simp [hfv_zero, hgv_zero]
  let ψ : (I → ℂ) →ₗ[ℂ] Ker :=
    { toFun := fun c => ∑ i : I, c i • basisVec i
      map_add' := by
        intro c d
        apply Subtype.ext
        funext v
        simp [basisVec, Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro a c
        apply Subtype.ext
        funext v
        simp [basisVec, Finset.mul_sum, smul_eq_mul, mul_assoc] }
  have hbasis_eval : ∀ i j : I, (basisVec j : Z.V → ℂ) (Quot.out i.1) = if j = i then 1 else 0 := by
    intro i j
    by_cases hji : j = i
    · subst hji
      simp [basisVec, hbroot]
    · have hneq : Z.graph.connectedComponentMk (Quot.out i.1) ≠ j.1 := by
        intro hcomp
        apply hji
        apply Subtype.ext
        exact hcomp.symm.trans (Quot.out_eq i.1)
      have hz : b j (Quot.out i.1) = 0 := hbsupp j (Quot.out i.1) hneq
      simpa [basisVec, hji] using hz
  have hψ_apply (c : I → ℂ) (i : I) : (ψ c : Z.V → ℂ) (Quot.out i.1) = c i := by
    calc
      (ψ c : Z.V → ℂ) (Quot.out i.1)
          = ∑ j : I, c j * (basisVec j : Z.V → ℂ) (Quot.out i.1) := by
              simp [ψ]
      _ = ∑ j : I, if j = i then c i else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases hji : j = i
            · subst hji
              simp [hbasis_eval, basisVec, hbroot]
            · have hb0 : (basisVec j : Z.V → ℂ) (Quot.out i.1) = 0 := by
                simpa [hji] using hbasis_eval i j
              calc
                c j * (basisVec j : Z.V → ℂ) (Quot.out i.1)
                    = c j * 0 := by rw [hb0]
                _ = 0 := by simp
                _ = (if j = i then c i else 0) := by simp [hji]
      _ = c i := by
            simp
  have hψ_inj : Function.Injective ψ := by
    intro c d hcd
    funext i
    have heval := congrArg (fun x : Ker => (x : Z.V → ℂ) (Quot.out i.1)) hcd
    simpa [hψ_apply] using heval
  have hle := LinearMap.finrank_le_finrank_of_injective (f := φ) hφ_inj
  have hge := LinearMap.finrank_le_finrank_of_injective (f := ψ) hψ_inj
  apply Nat.le_antisymm
  · calc
      finrank ℂ Ker ≤ Fintype.card I := by
        simpa [FiniteDimensional.finrank_pi_fintype] using hle
      _ = annComponentCount Z k := hcardI
  · calc
      annComponentCount Z k = Fintype.card I := hcardI.symm
      _ ≤ finrank ℂ Ker := by
        simpa [FiniteDimensional.finrank_pi_fintype] using hge

/-- THEOREM: The total kernel dimension of the Z/n connection Laplacian on the n-fold cover
    equals the sum over connected components of n divided by the order of
    the holonomy subgroup. -/
theorem connectionLaplacian_kernel_dim_general :
    finrank ℂ (LinearMap.ker (Matrix.toLin' (coverLaplacian Z))) =
    ∑ C : Z.graph.ConnectedComponent, n / Nat.card (holonomySubgroup Z C) := by
  classical
  rw [finrank_ker_coverLaplacian_eq_sum]
  simp_rw [finrank_ker_sectoralLaplacian_eq_ann, annComponentCount_eq]
  have hcard_filter (k : Fin n) :
      (Finset.filter (fun C : Z.graph.ConnectedComponent =>
          (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)) Finset.univ).card =
        ∑ C : Z.graph.ConnectedComponent,
          if (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C) then 1 else 0 := by
    rw [Finset.card_filter]
  simp_rw [hcard_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  have hsum_filter :
      (∑ k : Fin n,
        if (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C) then 1 else 0) =
      (Finset.filter (fun k : Fin n =>
          (k.val : ZMod n) ∈ subgroupAnnihilator (holonomySubgroup Z C)) Finset.univ).card := by
    rw [Finset.card_filter]
  rw [hsum_filter, ← annihilator_card_eq_div Z C, annihilator]

/-- COROLLARY: For a connected graph, the cover kernel dimension is exactly n/|H|.
    This is the core witness for the P vs NP spectral reduction. -/
theorem connectionLaplacian_kernel_dim_connected (h_conn : Z.graph.Connected) (v : Z.V) :
    finrank ℂ (LinearMap.ker (Matrix.toLin' (coverLaplacian Z))) =
    n / Nat.card (holonomySubgroup Z (Quot.mk _ v)) := by
  rw [finrank_ker_coverLaplacian_eq_sum]
  change annihilatorKernelCount Z (Quot.mk _ v) = _
  rw [annihilatorKernelCount_eq Z _ h_conn]
  exact annihilator_card_eq_div Z _

end ConnectionLaplacian
