/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.Surface.Circle
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Classification

/-!
# The two cuff incidences at a seam vertex

The local count in VII (4.6), page 225, includes two incidences from the cuff.
The cuff through a seam vertex either has no other seam vertex, giving a loop,
or has two distinct neighbouring edges. We construct these edges from the
cyclic order on the cuff.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

private theorem mem_closure_nextSegment {V : Set Circle} (hV : V.Finite) {v : Circle}
    (hv : v ∈ V) : v ∈ closure (nextSegment V v) := by
  obtain ⟨L, hL0, hL2pi, hseg⟩ : ∃ L : ℝ, 0 < L ∧ L ≤ 2 * Real.pi ∧
      nextSegment V v = arcOfLength v L := by
    rcases (V \ {v}).eq_empty_or_nonempty with hemp | hne
    · have hV_eq : V = {v} := Subset.antisymm (sdiff_eq_empty.mp hemp) (singleton_subset_iff.mpr hv)
      refine ⟨2 * Real.pi, Real.two_pi_pos, le_rfl, ?_⟩
      rw [hV_eq, nextSegment_singleton]
      ext z
      simp only [mem_compl_iff, mem_singleton_iff, arcOfLength, mem_ofPred_eq]
      exact ⟨fun h => ⟨Circle.angleDiff_pos (Ne.symm h), Circle.angleDiff_lt_two_pi v z⟩,
        fun ⟨hpos, _⟩ h => by subst h; simp [Circle.angleDiff] at hpos⟩
    · obtain ⟨v_next, hv_next, hmin⟩ := exists_min_on_finite hV.sdiff hne (Circle.angleDiff v)
      have hne_v : v ≠ v_next := Ne.symm hv_next.2
      refine ⟨v.angleDiff v_next, Circle.angleDiff_pos hne_v,
        (Circle.angleDiff_lt_two_pi v v_next).le, ?_⟩
      rw [nextSegment_eq_circleOpenArc_of_min hv_next hmin]
      ext z
      rw [mem_circleOpenArc_iff_angleDiff hne_v]
      rfl
  rw [hseg, _root_.mem_closure_iff]
  intro U hU hvU
  let γ : ℝ → Circle := fun t => Circle.exp (L * t) * v
  have hγ_cont : Continuous γ :=
    (Circle.exp.continuous.comp (continuous_const.mul continuous_id)).mul continuous_const
  have hγ0 : γ 0 = v := by simp [γ]
  have hpre : IsOpen (γ ⁻¹' U) := hU.preimage hγ_cont
  have h0_mem : (0 : ℝ) ∈ γ ⁻¹' U := by simp [hγ0, hvU]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre 0 h0_mem
  let t₀ : ℝ := min (ε / 2) (1 / 2)
  have ht₀_pos : 0 < t₀ := lt_min (half_pos hε) (by norm_num)
  have ht₀_lt1 : t₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have ht₀_ball : t₀ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  refine ⟨γ t₀, hball ht₀_ball, ?_⟩
  have ht0 : 0 < L * t₀ := mul_pos hL0 ht₀_pos
  have htL : L * t₀ < L := by nlinarith
  have ht2pi : L * t₀ < 2 * Real.pi := htL.trans_le hL2pi
  simp only [arcOfLength, mem_ofPred_eq, γ, angleDiff_exp_mul ht0 ht2pi]
  exact ⟨ht0, htL⟩

/-- On `Circle`, for any finite subset `V` and `v ∈ V`, `v ∈ closure (prevSegment V v)`. -/
private theorem mem_closure_prevSegment {V : Set Circle} (hV : V.Finite) {v : Circle}
    (hv : v ∈ V) : v ∈ closure (prevSegment V v) := by
  obtain ⟨L, hL0, hL2pi, hseg⟩ : ∃ L : ℝ, 0 < L ∧ L ≤ 2 * Real.pi ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, Circle.exp (-(L * t)) * v ∈ prevSegment V v := by
    rcases (V \ {v}).eq_empty_or_nonempty with hemp | hne
    · have hV_eq : V = {v} := Subset.antisymm (sdiff_eq_empty.mp hemp) (singleton_subset_iff.mpr hv)
      refine ⟨Real.pi, Real.pi_pos, by linarith [Real.pi_pos], fun t ht => ?_⟩
      rw [hV_eq, prevSegment_singleton, mem_compl_iff, mem_singleton_iff]
      intro h
      have h1 : Circle.exp (-(Real.pi * t)) = Circle.exp 0 := by
        rw [Circle.exp_zero, ← mul_left_inj v, one_mul]
        exact h
      have hinj := Circle.exp_injOn_Ioc (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])
      have ht_mem : -(Real.pi * t) ∈ Ioc (-Real.pi) Real.pi :=
        ⟨by nlinarith [ht.2, Real.pi_pos], by nlinarith [ht.1, Real.pi_pos]⟩
      have h0_mem : (0 : ℝ) ∈ Ioc (-Real.pi) Real.pi := ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
      have heq := hinj ht_mem h0_mem h1
      nlinarith [ht.1, Real.pi_pos]
    · obtain ⟨v_prev, hv_prev, hmax⟩ := exists_max_on_finite hV.sdiff hne (Circle.angleDiff v)
      have hvv' : v_prev ≠ v := hv_prev.2
      let L := v_prev.angleDiff v
      have hL0 : 0 < L := Circle.angleDiff_pos hvv'
      have hL2pi : L < 2 * Real.pi := Circle.angleDiff_lt_two_pi v_prev v
      refine ⟨L, hL0, hL2pi.le, fun t ht => ?_⟩
      rw [prevSegment_eq_nextSegment_of_max hv hv_prev hmax]
      let z := Circle.exp (-(L * t)) * v
      have hz_eq : z = Circle.exp (L * (1 - t)) * v_prev := by
        dsimp [z, L]
        have hexp := Circle.exp_angleDiff_mul (x := v_prev) (y := v)
        calc
          Circle.exp (-(v_prev.angleDiff v * t)) * v
            = Circle.exp (-(v_prev.angleDiff v * t)) *
                (Circle.exp (v_prev.angleDiff v) * v_prev) := by rw [hexp]
          _ = (Circle.exp (-(v_prev.angleDiff v * t)) *
                Circle.exp (v_prev.angleDiff v)) * v_prev := by rw [mul_assoc]
          _ = Circle.exp (v_prev.angleDiff v * (1 - t)) * v_prev := by
              rw [← Circle.exp_add]
              congr 2
              ring
      change z ∈ nextSegment V v_prev
      rw [hz_eq]
      have ht1_pos : 0 < L * (1 - t) := mul_pos hL0 (sub_pos.mpr ht.2)
      have ht1_lt : L * (1 - t) < L := by nlinarith [ht.1]
      have ht1_2pi : L * (1 - t) < 2 * Real.pi := ht1_lt.trans hL2pi
      have hang := angleDiff_exp_mul (v := v_prev) ht1_pos ht1_2pi
      refine ⟨?_, fun w hw => ?_⟩
      · intro h
        have hpos := ht1_pos
        rw [← hang, h] at hpos
        simp [Circle.angleDiff] at hpos
      · rcases eq_or_ne w v with rfl | hwv
        · rw [hang]
          exact ht1_lt
        · have hw_mem : w ∈ V \ {v} := ⟨hw.1, hwv⟩
          have hle_w := hmax w hw_mem
          have hlt_w : v.angleDiff w < v.angleDiff v_prev :=
            lt_of_le_of_ne hle_w ((circleCoordFrom v).injective.ne hw.2)
          have hsum_vv' := Circle.angleDiff_add_angleDiff hvv'
          have hsum_wv := Circle.angleDiff_add_angleDiff hwv
          have hw_pos := Circle.angleDiff_pos hwv.symm
          have hvp_pos := Circle.angleDiff_pos hvv'.symm
          have hzp_pos : 0 < v_prev.angleDiff (Circle.exp (L * (1 - t)) * v_prev) := by
            rw [hang]; exact ht1_pos
          have heq_w := angleDiff_eq_of_angleDiff (x := v) (a := v_prev) (b := w)
          have hL_lt : L < v_prev.angleDiff w := by
            dsimp [L] at *
            grind [-Circle.angleDiff]
          rw [hang]
          exact ht1_lt.trans hL_lt
  rw [_root_.mem_closure_iff]
  intro U hU hvU
  let γ : ℝ → Circle := fun t => Circle.exp (-(L * t)) * v
  have hγ_cont : Continuous γ :=
    (Circle.exp.continuous.comp (continuous_neg.comp (continuous_const.mul continuous_id))).mul
      continuous_const
  have hγ0 : γ 0 = v := by simp [γ]
  have hpre : IsOpen (γ ⁻¹' U) := hU.preimage hγ_cont
  have h0_mem : (0 : ℝ) ∈ γ ⁻¹' U := by simp [hγ0, hvU]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre 0 h0_mem
  let t₀ : ℝ := min (ε / 2) (1 / 2)
  have ht₀_pos : 0 < t₀ := lt_min (half_pos hε) (by norm_num)
  have ht₀_lt1 : t₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have ht₀_ball : t₀ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht₀_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  exact ⟨γ t₀, hball ht₀_ball, hseg t₀ ⟨ht₀_pos, ht₀_lt1⟩⟩

/-- The two cuff incidences used in VII (4.6), page 225: either one
boundary loop or two distinct incident boundary edges. -/
theorem Net.exists_cuff_incident_edges (hS : IsSurface S) (N : Net S)
    {J : Drawing S} (hJ : N.IsSeamGraphFor J) {v : S}
    (hvV : v ∈ J.V) (hv_bd : v ∈ bd S) :
    (∃ e ∈ J.E, e ⊆ bd S ∧ J.VertexIncident v e ∧ (tilde e).ncard = 1) ∨
    (∃ e₁ ∈ J.E, ∃ e₂ ∈ J.E, e₁ ≠ e₂ ∧
      e₁ ⊆ bd S ∧ e₂ ⊆ bd S ∧ J.VertexIncident v e₁ ∧ J.VertexIncident v e₂) := by
  have : T2Space S := hS.2.1
  let C : Set S := connectedComponentIn (bd S) v
  have hC_cuff : C ∈ cuffs S := ⟨v, hv_bd, rfl⟩
  have hvC : v ∈ C := mem_connectedComponentIn hv_bd
  obtain ⟨φ_C⟩ := (cuff_statement S hS).2.2 C hC_cuff
  let ι : Circle → S := Subtype.val ∘ φ_C
  have hι_cont : Continuous ι := continuous_subtype_val.comp φ_C.continuous
  have hι_inj : Function.Injective ι := Subtype.val_injective.comp φ_C.injective
  let V_C : Set Circle := ι ⁻¹' J.V
  have hVC_fin : V_C.Finite := J.finite_V.preimage hι_inj.injOn
  let w₀ : Circle := φ_C.symm ⟨v, hvC⟩
  have hw₀_ι : ι w₀ = v := by simp [ι, w₀]
  have hw₀_VC : w₀ ∈ V_C := by
    rw [mem_preimage, hw₀_ι]
    exact hvV
  have hι_compl : ι '' (V_Cᶜ) = C \ J.V := by
    ext x
    simp only [V_C, ι, Function.comp_apply, mem_image, mem_compl_iff, mem_preimage, Set.mem_sdiff]
    exact ⟨by rintro ⟨z, hz, rfl⟩; exact ⟨(φ_C z).2, hz⟩,
      fun ⟨hxC, hxV⟩ => ⟨φ_C.symm ⟨x, hxC⟩, by simpa using hxV, by simp⟩⟩
  obtain ⟨g, hg_cont, hgi⟩ :=
    exists_inv_of_compactOn (isCompact_univ (X := Circle)) hι_cont.continuousOn hι_inj.injOn
  have harc_C : arcComponentsIn (C \ J.V) = image ι '' arcComponentsIn (V_Cᶜ) := by
    rw [← hι_compl]
    exact GM11.arcComponentsIn_image hι_cont.continuousOn
      (hg_cont.mono (image_mono (subset_univ _))) (fun z _ => hgi (mem_univ z))
  obtain ⟨harc_VC, _⟩ := arcComponentsIn_compl_circle hVC_fin ⟨w₀, hw₀_VC⟩
  have harc_C_sub_bd : arcComponentsIn (C \ J.V) ⊆ arcComponentsIn (bd S \ J.V) := by
    let 𝓐 : Set (Set S) := cuffs S \ {C}
    have h𝓐_fin : 𝓐.Finite := (cuff_statement S hS).2.1.subset sdiff_subset
    have hC_closed : IsClosed C := isClosed_of_mem_cuffs hS hC_cuff
    have h𝓐_closed : IsClosed (⋃₀ 𝓐) :=
      h𝓐_fin.isClosed_sUnion fun C' hC' => isClosed_of_mem_cuffs hS hC'.1
    have hdisj : Disjoint C (⋃₀ 𝓐) := by
      rw [Set.disjoint_left]
      rintro x hxC ⟨C', ⟨hC'cuff, hC'ne⟩, hxC'⟩
      exact Set.disjoint_left.mp (cuffs_disjoint hC_cuff hC'cuff (Ne.symm hC'ne)) hxC hxC'
    have hbd_eq : bd S \ J.V = (C \ J.V) ∪ ((⋃₀ 𝓐) \ J.V) := by
      have hunion : C ∪ ⋃₀ 𝓐 = bd S := by
        rw [← sUnion_insert, insert_sdiff_singleton, insert_eq_of_mem hC_cuff, sUnion_cuffs]
      rw [← union_sdiff_distrib, hunion]
    rw [hbd_eq, GM11.arcComponentsIn_union hC_closed h𝓐_closed sdiff_subset sdiff_subset
      (fun x _ hxC hx𝓐 => Set.disjoint_left.mp hdisj hxC hx𝓐)]
    exact subset_union_left
  have hseg_mem_E : ∀ w ∈ V_C, ι '' nextSegment V_C w ∈ J.E := by
    intro w hw
    rw [(N.seamGraph_edges_eq hS hJ).1]
    refine Or.inr (harc_C_sub_bd ?_)
    rw [harc_C, harc_VC]
    exact ⟨nextSegment V_C w, ⟨w, hw, rfl⟩, rfl⟩
  have hseg_sub_bd : ∀ w ∈ V_C, ι '' nextSegment V_C w ⊆ bd S := by
    rintro w _ _ ⟨z, _, rfl⟩
    exact sUnion_cuffs (S := S) ▸ ⟨C, hC_cuff, (φ_C z).2⟩
  let e₁ := ι '' nextSegment V_C w₀
  have he₁_E : e₁ ∈ J.E := hseg_mem_E w₀ hw₀_VC
  have hv_cl_e₁ : v ∈ closure e₁ := by
    rw [← hw₀_ι]
    exact image_closure_subset_closure_image hι_cont
      ⟨w₀, mem_closure_nextSegment hVC_fin hw₀_VC, rfl⟩
  have hv_inc_e₁ : J.VertexIncident v e₁ := ⟨hvV, Or.inl he₁_E, hv_cl_e₁⟩
  have hv_tilde_e₁ : v ∈ tilde e₁ := (vertexIncident_iff_mem_tilde J hvV he₁_E).mp hv_inc_e₁
  -- Split on whether `V_C \ {w₀}` is empty (`|C ∩ J.V| = 1`) or nonempty (`|C ∩ J.V| ≥ 2`).
  rcases (V_C \ {w₀}).eq_empty_or_nonempty with hemp | hne
  · -- `V_C = {w₀}`, so `e₁` is a loop edge (`(tilde e₁).ncard = 1`).
    have htilde_e₁_sub : tilde e₁ ⊆ {v} := by
      rw [tilde_eq_closure_inter_V J he₁_E]
      rintro x ⟨hxcl, hxV⟩
      have hxC : x ∈ C :=
        isClosed_of_mem_cuffs hS hC_cuff |>.closure_subset_iff.mpr
          (by rintro _ ⟨z, _, rfl⟩; exact (φ_C z).2) hxcl
      let z : Circle := φ_C.symm ⟨x, hxC⟩
      have hz_VC : z ∈ V_C := by
        rw [mem_preimage]
        simpa [ι, z] using hxV
      have hzw₀ : z = w₀ := by
        by_contra hne
        exact hemp.subset ⟨hz_VC, hne⟩
      have hx_eq : x = ι z := by simp [ι, z]
      rw [hx_eq, hzw₀, hw₀_ι]
      rfl
    have htilde_e₁_eq : tilde e₁ = {v} :=
      Subset.antisymm htilde_e₁_sub (singleton_subset_iff.mpr hv_tilde_e₁)
    have hncard_e₁ : (tilde e₁).ncard = 1 := by rw [htilde_e₁_eq, ncard_singleton]
    exact .inl ⟨e₁, he₁_E, hseg_sub_bd w₀ hw₀_VC, hv_inc_e₁, hncard_e₁⟩
  · obtain ⟨w₁, hw₁_prev, hmax⟩ := exists_max_on_finite hVC_fin.sdiff hne (Circle.angleDiff w₀)
    have hprev_eq := prevSegment_eq_nextSegment_of_max hw₀_VC hw₁_prev hmax
    have hw₁_VC : w₁ ∈ V_C := hw₁_prev.1
    have hw₁_ne : w₁ ≠ w₀ := hw₁_prev.2
    let e₂ := ι '' nextSegment V_C w₁
    have he₂_E : e₂ ∈ J.E := hseg_mem_E w₁ hw₁_VC
    have hv_cl_e₂ : v ∈ closure e₂ := by
      dsimp only [e₂]
      rw [← hw₀_ι, ← hprev_eq]
      exact image_closure_subset_closure_image hι_cont
        ⟨w₀, mem_closure_prevSegment hVC_fin hw₀_VC, rfl⟩
    have hv_inc_e₂ : J.VertexIncident v e₂ := ⟨hvV, Or.inl he₂_E, hv_cl_e₂⟩
    have he₁_ne_e₂ : e₁ ≠ e₂ := by
      intro h_eq
      obtain ⟨z, hz₁⟩ := nextSegment_nonempty hVC_fin hw₀_VC
      have hz₂_img : ι z ∈ e₂ := h_eq ▸ ⟨z, hz₁, rfl⟩
      rcases hz₂_img with ⟨z', hz', hι_eq⟩
      have hzz' : z = z' := hι_inj hι_eq.symm
      subst hzz'
      have hz_compl : z ∈ V_Cᶜ := nextSegment_subset_compl hz₁
      obtain ⟨_, _, huniq⟩ := exists_unique_nextSegment_of_mem_compl hVC_fin ⟨w₀, hw₀_VC⟩ hz_compl
      exact hw₁_ne (huniq w₁ ⟨hw₁_VC, hz'⟩ |>.trans (huniq w₀ ⟨hw₀_VC, hz₁⟩).symm)
    exact .inr ⟨e₁, he₁_E, e₂, he₂_E, he₁_ne_e₂,
      hseg_sub_bd w₀ hw₀_VC, hseg_sub_bd w₁ hw₁_VC, hv_inc_e₁, hv_inc_e₂⟩

end GraphMinor.GM07
