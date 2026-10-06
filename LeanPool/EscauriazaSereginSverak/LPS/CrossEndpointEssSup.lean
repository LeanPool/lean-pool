/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinMollifiedMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Measurability of the slice `L∞` norm

For a jointly measurable velocity, the essential supremum of the Euclidean norm
of its time slices is a measurable function of time. This is used to integrate
the endpoint Serrin coefficient in `lem:lps-comparison`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_essSup_slice_measurable {G : ℝ × Vec3 → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun t : ℝ => essSup (fun x : Vec3 => G (t, x)) (volume : Measure Vec3)) := by
  refine measurable_of_Iic fun a => ?_
  have hset : MeasurableSet {z : ℝ × Vec3 | a < G z} := measurableSet_lt measurable_const hG
  have hmeas : Measurable fun t : ℝ =>
      (volume : Measure Vec3) (Prod.mk t ⁻¹' {z : ℝ × Vec3 | a < G z}) :=
    measurable_measure_prodMk_left hset
  have hpre : (fun t : ℝ => essSup (fun x : Vec3 => G (t, x)) (volume : Measure Vec3)) ⁻¹'
      Iic a = (fun t : ℝ =>
        (volume : Measure Vec3) (Prod.mk t ⁻¹' {z : ℝ × Vec3 | a < G z})) ⁻¹' {0} := by
    ext t
    simp only [mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · intro h
      have hae : ∀ᵐ x ∂(volume : Measure Vec3), G (t, x) ≤ a :=
        (ENNReal.ae_le_essSup (fun x : Vec3 => G (t, x))).mono fun x hx => hx.trans h
      have := measure_eq_zero_iff_ae_notMem.mpr (by
        filter_upwards [hae] with x hx
        exact not_lt.mpr hx :
          ∀ᵐ x ∂(volume : Measure Vec3), x ∉ Prod.mk t ⁻¹' {z : ℝ × Vec3 | a < G z})
      exact this
    · intro h
      refine essSup_le_of_ae_le a ?_
      have h0 := measure_eq_zero_iff_ae_notMem.mp h
      filter_upwards [h0] with x hx
      exact not_lt.mp hx
  rw [hpre]
  exact hmeas (measurableSet_singleton 0)

/-- Almost everywhere strong measurability on a slab gives measurability on the
product space with the product slab measure. -/
theorem lps_aesm_slab_to_prod {a b : ℝ} {E : Type} [TopologicalSpace E]
    {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))) :
    AEStronglyMeasurable (fun z : Vec3 × ℝ => F z)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
  have hslab : (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) :
      Measure (Vec3 × ℝ)) = (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
    change (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) = _
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  exact hslab ▸ hF

/-- The essential supremum of the Euclidean norm of the time slices of a
space-time velocity is an almost everywhere measurable function of time. -/
theorem lps_essSup_norm_slice_aemeasurable {a b : ℝ} {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))) :
    AEMeasurable (fun t : ℝ => essSup
      (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x,t))))
      (volume : Measure Vec3)) (volume.restrict (Ioo a b)) := by
  have hu' := lps_aesm_slab_to_prod hu
  have hs := hu'.prod_swap
  let u' : ℝ × Vec3 → Vec3 := hs.mk _
  have hu'meas : Measurable u' := hs.stronglyMeasurable_mk.measurable
  have hG : Measurable (fun z : ℝ × Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u' z))) :=
    ENNReal.measurable_ofReal.comp
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp hu'meas)
  refine (lps_essSup_slice_measurable hG).aemeasurable.congr ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hs.ae_eq_mk] with t ht
  refine essSup_congr_ae ?_
  filter_upwards [ht] with x hx
  have : u' (t, x) = u (x, t) := hx.symm
  simp only [this]

/-- The endpoint Serrin coefficient: the `L∞` norm of the slices, its
measurability, its square moment, and its pointwise bound on the Euclidean
norm of the velocity. -/
theorem lps_endpoint_norm_slice_facts {a b : ℝ} {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hEndpoint : (∫⁻ t in Ioo a b,
      (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x,t))))
        (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    AEMeasurable (fun τ : ℝ => ENNReal.ofReal
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) ⊤ volume).toReal)
      (volume.restrict (Ioo a b)) ∧
    (∫⁻ τ in Ioo a b, ENNReal.ofReal
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) ⊤ volume).toReal ^ (2 : ℝ)) < ⊤ ∧
    (∀ᵐ τ ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
      vec3EuclideanNorm (u (x,τ)) ≤
        (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) ⊤ volume).toReal) ∧
    IntegrableOn (fun τ : ℝ =>
      (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) ⊤ volume).toReal ^ 2)
      (Ioo a b) := by
  let μt : Measure ℝ := volume.restrict (Ioo a b)
  let N : ℝ → ℝ≥0∞ := fun τ =>
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) ⊤ volume
  have hNeq : ∀ᵐ τ ∂μt, N τ = essSup
      (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x,τ)))) volume := by
    filter_upwards [(lps_aesm_slab_to_prod hu).prodMk_right] with τ hτ
    have hmeas : AEStronglyMeasurable (fun x : Vec3 => vec3EuclideanNorm (u (x,τ))) volume :=
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hτ
    change eLpNorm _ ⊤ volume = _
    rw [eLpNorm_exponent_top hmeas]
    refine essSup_congr_ae (Eventually.of_forall fun x => ?_)
    change ‖vec3EuclideanNorm (u (x,τ))‖ₑ = _
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  have hNmeas : AEMeasurable N μt := by
    refine (lps_essSup_norm_slice_aemeasurable hu).congr ?_
    filter_upwards [hNeq] with τ hτ using hτ.symm
  have hNsq : (∫⁻ τ, N τ ^ (2 : ℝ) ∂μt) < ⊤ := by
    have h : (∫⁻ τ, N τ ^ (2 : ℝ) ∂μt) = ∫⁻ t in Ioo a b,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x,t))))
          (volume : Measure Vec3)) ^ (2 : ℝ) :=
      lintegral_congr_ae (by filter_upwards [hNeq] with τ hτ; rw [hτ])
    rw [h]
    exact hEndpoint
  have hNfin : ∀ᵐ τ ∂μt, N τ ≠ ⊤ := by
    filter_upwards [ae_lt_top' (hNmeas.pow_const (2 : ℝ)) hNsq.ne] with τ hτ
    intro h
    rw [h] at hτ
    simp at hτ
  have hRealMeas : AEMeasurable (fun τ : ℝ => ENNReal.ofReal (N τ).toReal) μt :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (ENNReal.measurable_toReal.comp_aemeasurable hNmeas)
  refine ⟨hRealMeas, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt (lintegral_mono fun τ => ?_) hNsq
    exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le (by norm_num)
  · filter_upwards [hNfin, hNeq] with τ hτ hNτ
    have hae := ENNReal.ae_le_essSup (μ := (volume : Measure Vec3))
      (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x,τ))))
    filter_upwards [hae] with x hx
    rw [← hNτ] at hx
    exact (ENNReal.ofReal_le_iff_le_toReal hτ).mp hx
  · have hmeas : AEStronglyMeasurable (fun τ : ℝ => (N τ).toReal ^ 2) μt :=
      ((ENNReal.measurable_toReal.comp_aemeasurable hNmeas).pow_const 2).aestronglyMeasurable
    refine ⟨hmeas, ?_⟩
    change (∫⁻ τ, ‖(N τ).toReal ^ 2‖ₑ ∂μt) < ⊤
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hNsq
    filter_upwards [hNfin] with τ hτ
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hτ]
    simp

end ESS

end
