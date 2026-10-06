/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointCore
public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointPairingSlice
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSlab
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinMollifiedMeasurable

/-!
# Endpoint cutoff pairings on the space-time slab

The two endpoint pairings needed for the convection term of the cross density:
an `L²_t L∞_x` velocity against an `L²_t L¹_x` convection, and an `L∞_t L²_x`
velocity against an `L¹_t L²_x` convection (`lem:lps-comparison`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Almost every time slice of a slab-measurable function is measurable. -/
theorem lps_slice_aesm {T : ℝ} {f : ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      AEStronglyMeasurable (fun x : Vec3 => f (x,t)) volume :=
  (serrin_aesm_prod hf).prodMk_right

/-- Tonelli on the slab for the extended norm of a measurable function. -/
theorem lps_slab_lintegral_eq {T : ℝ} {h : ParabolicPoint → ℝ}
    (hh : AEStronglyMeasurable h
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    (∫⁻ z : ParabolicPoint, ‖h z‖ₑ ∂(volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) =
      ∫⁻ t : ℝ, (∫⁻ x : Vec3, ‖h (x,t)‖ₑ) ∂(volume.restrict (Ioo 0 T)) := by
  rw [serrin_slab_measure_eq T]
  exact lintegral_prod_symm _ (serrin_aesm_prod hh).enorm

/-- The slice `L¹` norm of a slab-measurable function is measurable in time. -/
theorem lps_slice_lintegral_aemeasurable {T : ℝ} {h : ParabolicPoint → ℝ}
    (hh : AEStronglyMeasurable h
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    AEMeasurable (fun t : ℝ => ∫⁻ x : Vec3, ‖h (x,t)‖ₑ)
      (volume.restrict (Ioo 0 T)) :=
  (serrin_aesm_prod hh).enorm.lintegral_prod_left'

/-- Cauchy–Schwarz in time for two profiles with finite square moments. -/
theorem lps_lintegral_mul_ne_top_of_sq {μ : Measure ℝ} {a b : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (ha2 : (∫⁻ t, a t ^ (2 : ℝ) ∂μ) < ⊤) (hb2 : (∫⁻ t, b t ^ (2 : ℝ) ∂μ) < ⊤) :
    (∫⁻ t, a t * b t ∂μ) ≠ ⊤ := by
  have hHolder : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hHolder ha hb
  refine ne_top_of_le_ne_top ?_ h
  exact (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ha2.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hb2.ne)).ne

private theorem lps_cutoff_aesm (n : ℕ) {T : ℝ} :
    AEStronglyMeasurable (fun z : ParabolicPoint => serrinCutoff n z.1)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
  ((serrinCutoff_contDiff n).continuous.measurable.comp measurable_fst).aestronglyMeasurable

/-- Endpoint pairing of a velocity component with an essentially bounded
`L²_t` spatial profile against an `L²_t L¹_x` convection component: the
cutoff-weighted product of the spatial mollifications is integrable and its
integral converges to that of the product. -/
theorem lps_endpoint_cutoff_pairing_limit_linf_l1
    {T t : ℝ} (ht : t ≤ T) {f g : ParabolicPoint → ℝ} {β : ℝ → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hβmeas : AEMeasurable (fun τ => ENNReal.ofReal (β τ))
      (volume.restrict (Ioo 0 T)))
    (hβ : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      ∀ᵐ x ∂(volume : Measure Vec3), |f (x,τ)| ≤ β τ)
    (hβint : (∫⁻ τ in Ioo 0 T, ENNReal.ofReal (β τ) ^ (2 : ℝ)) < ⊤)
    (hgSlice : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      Integrable (fun x : Vec3 => g (x,τ)) volume)
    (hgMoment : (∫⁻ τ in Ioo 0 T,
      (∫⁻ x : Vec3, ‖g (x,τ)‖ₑ) ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z : ParabolicPoint => f z * g z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) ∧
    (∀ n, Integrable (fun z : ParabolicPoint =>
      serrinCutoff n z.1 * serrinSM f n z * serrinSM g n z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) ∧
    Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      serrinCutoff n z.1 * serrinSM f n z * serrinSM g n z) atTop
      (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), f z * g z)) := by
  have hQ : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    intro z hz
    exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 ht⟩
  have hIoo : Ioo 0 t ⊆ Ioo 0 T := Ioo_subset_Ioo_right ht
  have hle : (volume.restrict (Ioo 0 t) : Measure ℝ) ≤ volume.restrict (Ioo 0 T) :=
    Measure.restrict_mono hIoo le_rfl
  -- shrink every hypothesis to the slab of length `t`
  have hf' : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
    hf.mono_measure (Measure.restrict_mono hQ le_rfl)
  have hg' : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
    hg.mono_measure (Measure.restrict_mono hQ le_rfl)
  have hβmeas' := hβmeas.mono_measure hle
  have hβ' := ae_restrict_of_ae_restrict_of_subset hIoo hβ
  have hβint' : (∫⁻ τ in Ioo 0 t, ENNReal.ofReal (β τ) ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hIoo) hβint
  have hgSlice' := ae_restrict_of_ae_restrict_of_subset hIoo hgSlice
  have hgMoment' : (∫⁻ τ in Ioo 0 t, (∫⁻ x : Vec3, ‖g (x,τ)‖ₑ) ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hIoo) hgMoment
  clear hf hg hβmeas hβ hβint hgSlice hgMoment hQ hle
  let μt : Measure ℝ := volume.restrict (Ioo 0 t)
  let h : ℝ → ℝ≥0∞ := fun τ => ∫⁻ x : Vec3, ‖g (x,τ)‖ₑ
  have hhmeas : AEMeasurable h μt := lps_slice_lintegral_aemeasurable hg'
  have hprod := lps_lintegral_mul_ne_top_of_sq hβmeas' hhmeas hβint' hgMoment'
  have hfSlice := lps_slice_aesm hf'
  have hgSliceAesm := lps_slice_aesm hg'
  -- integrability of the product
  have hGint : Integrable (fun z : ParabolicPoint => f z * g z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := by
    refine ⟨hf'.mul hg', ?_⟩
    have hfg : AEStronglyMeasurable (fun z : ParabolicPoint => f z * g z)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := hf'.mul hg'
    change (∫⁻ z : ParabolicPoint, ‖f z * g z‖ₑ ∂(volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) < ⊤
    rw [lps_slab_lintegral_eq hfg]
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) (lt_top_iff_ne_top.mpr hprod)
    filter_upwards [hβ'] with τ hτ
    calc (∫⁻ x : Vec3, ‖f (x,τ) * g (x,τ)‖ₑ) ≤
        ∫⁻ x : Vec3, ENNReal.ofReal (β τ) * ‖g (x,τ)‖ₑ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hτ] with x hx
          rw [enorm_mul]
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal hx
      _ = ENNReal.ofReal (β τ) * h τ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hDint : (∫⁻ τ in Ioo 0 t, 4 * (ENNReal.ofReal (β τ) * h τ)) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ (by simp)]
    exact ENNReal.mul_ne_top (by simp) hprod
  refine ⟨hGint, lps_slab_integral_tendsto_of_slice_domination
    (F := fun n z => serrinCutoff n z.1 * serrinSM f n z * serrinSM g n z)
    (D := fun τ => 4 * (ENNReal.ofReal (β τ) * h τ))
    (fun n => ((lps_cutoff_aesm n).mul (serrinSM_aestronglyMeasurable hf' n)).mul
      (serrinSM_aestronglyMeasurable hg' n))
    hGint hDint ?_ ?_⟩
  · intro n
    filter_upwards [hβ', hfSlice, hgSliceAesm, hgSlice'] with τ hτ hfτ hgτ hgi
    have := (lps_endpoint_slice_pairing_linf_l1 (f := fun x => f (x,τ))
      (g := fun x => g (x,τ)) hfτ hτ hgi).1 n
    calc _ ≤ _ := this
      _ = _ := by simp only [h]; ring
  · filter_upwards [hβ', hfSlice, hgSliceAesm, hgSlice'] with τ hτ hfτ hgτ hgi
    exact (lps_endpoint_slice_pairing_linf_l1 (f := fun x => f (x,τ))
      (g := fun x => g (x,τ)) hfτ hτ hgi).2

/-- Endpoint pairing of an `L∞_t L²_x` velocity component against an
`L¹_t L²_x` convection component. -/
theorem lps_endpoint_cutoff_pairing_limit_l2_l2
    {T t : ℝ} (ht : t ≤ T) {f g : ParabolicPoint → ℝ} {K : ℝ≥0∞}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hfSlice : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f (x,τ)) 2 volume)
    (hK : K ≠ ⊤)
    (hfBound : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (fun x : Vec3 => f (x,τ)) 2 volume ≤ K)
    (hgSlice : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => g (x,τ)) 2 volume)
    (hgMoment : (∫⁻ τ in Ioo 0 T,
      eLpNorm (fun x : Vec3 => g (x,τ)) 2 volume) < ⊤) :
    Integrable (fun z : ParabolicPoint => f z * g z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) ∧
    (∀ n, Integrable (fun z : ParabolicPoint =>
      serrinCutoff n z.1 * serrinSM f n z * serrinSM g n z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) ∧
    Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      serrinCutoff n z.1 * serrinSM f n z * serrinSM g n z) atTop
      (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), f z * g z)) := by
  have hQ : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    intro z hz
    exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 ht⟩
  have hIoo : Ioo 0 t ⊆ Ioo 0 T := Ioo_subset_Ioo_right ht
  have hf' : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
    hf.mono_measure (Measure.restrict_mono hQ le_rfl)
  have hg' : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
    hg.mono_measure (Measure.restrict_mono hQ le_rfl)
  have hfSlice' := ae_restrict_of_ae_restrict_of_subset hIoo hfSlice
  have hfBound' := ae_restrict_of_ae_restrict_of_subset hIoo hfBound
  have hgSlice' := ae_restrict_of_ae_restrict_of_subset hIoo hgSlice
  have hgMoment' : (∫⁻ τ in Ioo 0 t, eLpNorm (fun x : Vec3 => g (x,τ)) 2 volume) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hIoo) hgMoment
  clear hf hg hfSlice hfBound hgSlice hgMoment hQ
  let μt : Measure ℝ := volume.restrict (Ioo 0 t)
  have hfmeasSlice := lps_slice_aesm hf'
  have hgmeasSlice := lps_slice_aesm hg'
  have hDbound : (∫⁻ τ in Ioo 0 t, 6 * (K * eLpNorm (fun x : Vec3 => g (x,τ)) 2 volume)) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ hK]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hK hgMoment'.ne)
  have hGint : Integrable (fun z : ParabolicPoint => f z * g z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := by
    refine ⟨hf'.mul hg', ?_⟩
    have hfg : AEStronglyMeasurable (fun z : ParabolicPoint => f z * g z)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := hf'.mul hg'
    change (∫⁻ z : ParabolicPoint, ‖f z * g z‖ₑ ∂(volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) < ⊤
    rw [lps_slab_lintegral_eq hfg]
    have hle : (∫⁻ τ, (∫⁻ x : Vec3, ‖f (x,τ) * g (x,τ)‖ₑ) ∂μt) ≤
        ∫⁻ τ, K * eLpNorm (fun x : Vec3 => g (x,τ)) 2 volume ∂μt := by
      refine lintegral_mono_ae ?_
      filter_upwards [hfmeasSlice, hgmeasSlice, hfBound'] with τ hfτ hgτ hKτ
      calc (∫⁻ x : Vec3, ‖f (x,τ) * g (x,τ)‖ₑ) ≤
          eLpNorm (fun x : Vec3 => f (x,τ)) 2 volume *
            eLpNorm (fun x : Vec3 => g (x,τ)) 2 volume := by
            simpa only [enorm_mul] using lps_lintegral_mul_le_two hfτ hgτ
        _ ≤ _ := by gcongr
    refine lt_of_le_of_lt hle ?_
    rw [lintegral_const_mul' _ _ hK]
    exact ENNReal.mul_lt_top hK.lt_top hgMoment'
  refine ⟨hGint, lps_slab_integral_tendsto_of_slice_domination
    (F := fun n z => serrinCutoff n z.1 * serrinSM f n z * serrinSM g n z)
    (D := fun τ => 6 * (K * eLpNorm (fun x : Vec3 => g (x,τ)) 2 volume))
    (fun n => ((lps_cutoff_aesm n).mul (serrinSM_aestronglyMeasurable hf' n)).mul
      (serrinSM_aestronglyMeasurable hg' n))
    hGint hDbound ?_ ?_⟩
  · intro n
    filter_upwards [hfSlice', hgSlice', hfBound'] with τ hfτ hgτ hKτ
    have := (lps_endpoint_slice_pairing_l2_l2 (f := fun x => f (x,τ))
      (g := fun x => g (x,τ)) hfτ hgτ).1 n
    refine this.trans ?_
    gcongr
  · filter_upwards [hfSlice', hgSlice'] with τ hfτ hgτ
    exact (lps_endpoint_slice_pairing_l2_l2 (f := fun x => f (x,τ))
      (g := fun x => g (x,τ)) hfτ hgτ).2

end ESS

end
