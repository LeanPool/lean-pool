/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureBound

/-!
# Blowup Time AE

Almost-everywhere time-slice bounds used in endpoint compactness.
-/

public section

open MeasureTheory Filter Set CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- A fixed past time interval remains in the original time interval after
a sufficiently small positive rescaling. -/
theorem blowupPastInterval_subset_source
    (t₀ r a : ℝ) (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : 0 < r) (htime : r ^ 2 * (-a) < 3 / 4) :
    Ioo a 0 ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0) := by
  intro t ht
  change t₀ + r ^ 2 * t ∈ Ioo (-(1 : ℝ)) 0
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hlow : r ^ 2 * a < r ^ 2 * t :=
    mul_lt_mul_of_pos_left ht.1 hr2
  have hupp : r ^ 2 * t < 0 := mul_neg_of_pos_of_neg hr2 ht.2
  have htime' : -(3 / 4 : ℝ) < r ^ 2 * a := by
    linarith only [htime]
  exact ⟨by linarith only [ht₀.1, htime', hlow],
    by linarith only [ht₀.2, hupp]⟩

/-- Zero extension in time preserves joint strong measurability of a
whole-space pressure. -/
theorem blowupTimeExtendedPressure_aestronglyMeasurable
    (p₁ : ParabolicPoint → ℝ)
    (hp₁ : AEStronglyMeasurable p₁
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0))) :
    AEStronglyMeasurable (blowupTimeExtendedPressure p₁)
      (volume : Measure ParabolicPoint) := by
  let S : Set ParabolicPoint := Set.univ ×ˢ Ioo (-1 : ℝ) 0
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioo
  have hEq : blowupTimeExtendedPressure p₁ = S.indicator p₁ := by
    funext z
    by_cases hz : z.2 ∈ Ioo (-1 : ℝ) 0
    · have hzS : z ∈ S := ⟨Set.mem_univ _, hz⟩
      simp only [blowupTimeExtendedPressure,
        Set.indicator_of_mem hz, Set.indicator_of_mem hzS]
      cases z
      rfl
    · have hzS : z ∉ S := fun h => hz h.2
      simp only [blowupTimeExtendedPressure,
        Set.indicator_of_notMem hz, Set.indicator_of_notMem hzS]
  rw [hEq]
  exact (aestronglyMeasurable_indicator_iff hS).mpr hp₁

/-- The rescaled whole-space pressure remains jointly strongly measurable. -/
theorem blowupRieszPressure_aestronglyMeasurable
    (p₁ : ParabolicPoint → ℝ)
    (hp₁ : AEStronglyMeasurable p₁
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)))
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    AEStronglyMeasurable (blowupRieszPressure x₀ t₀ r p₁)
      (volume : Measure ParabolicPoint) := by
  exact blowupRescaledPressure_aestronglyMeasurable
    (blowupTimeExtendedPressure p₁)
    (blowupTimeExtendedPressure_aestronglyMeasurable p₁ hp₁)
    x₀ t₀ r hr

/-- An almost everywhere source-time property pulls back through a positive
parabolic time rescaling. -/
theorem blowup_ae_time_pullback
    (r t₀ : ℝ) (hr : 0 < r) (I : Set ℝ)
    (hI : MeasurableSet I) (P : ℝ → Prop)
    (hP : ∀ᵐ s ∂volume.restrict I, P s) :
    ∀ᵐ t ∂volume.restrict (CKN.rescaledTime r t₀ I),
      P (CKN.scalingTime r t₀ t) := by
  have hmap := CKN.map_scalingTime_restrict hr t₀ hI
  have hPmap : ∀ᵐ s ∂Measure.map (CKN.scalingTime r t₀)
      (volume.restrict (CKN.rescaledTime r t₀ I)), P s := by
    rw [hmap]
    exact hP.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hscaleMeas : Measurable (CKN.scalingTime r t₀) := by
    unfold CKN.scalingTime
    fun_prop
  exact ae_of_ae_map hscaleMeas.aemeasurable hPmap

/-- The pulled-back property also holds on every smaller rescaled time
interval. -/
theorem blowup_ae_time_pullback_on
    (r t₀ : ℝ) (hr : 0 < r) (I J : Set ℝ)
    (hI : MeasurableSet I) (hJ : J ⊆ CKN.rescaledTime r t₀ I)
    (P : ℝ → Prop) (hP : ∀ᵐ s ∂volume.restrict I, P s) :
    ∀ᵐ t ∂volume.restrict J, P (CKN.scalingTime r t₀ t) :=
  ae_restrict_of_ae_restrict_of_subset hJ
    (blowup_ae_time_pullback r t₀ hr I hI P hP)

/-- A source-time uniform whole-space pressure bound persists on a rescaled
past time interval contained in the source interval. -/
theorem blowupRieszPressure_slice_bound_ae
    (p₁ : ParabolicPoint → ℝ) (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) (J : Set ℝ) (hJmeas : MeasurableSet J)
    (hJ : J ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (M : ℝ≥0∞)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s))
        (volume : Measure Vec3) ∧
      eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞)
        (volume : Measure Vec3) ≤ M) :
    ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x : Vec3 => blowupRieszPressure x₀ t₀ r p₁ (x,t))
        (3 / 2 : ℝ≥0∞) (volume : Measure Vec3) ≤ M := by
  have hpull := blowup_ae_time_pullback_on r t₀ hr
    (Ioo (-1 : ℝ) 0) J measurableSet_Ioo hJ
    (fun s => AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞) volume ≤ M)
    hsource
  filter_upwards [hpull, ae_restrict_mem hJmeas] with t ht htJ
  have htime : CKN.scalingTime r t₀ t ∈ Ioo (-1 : ℝ) 0 := hJ htJ
  have heq (x : Vec3) :
      blowupRieszPressure x₀ t₀ r p₁ (x,t) =
        r ^ 2 * p₁ (x₀ + r • x, CKN.scalingTime r t₀ t) := by
    simp only [blowupRieszPressure, parabolicRescalePressure,
      blowupTimeExtendedPressure, CKN.scalingTime,
      parabolicTranslate, parabolicScale]
    change t₀ + r ^ 2 * t ∈ Ioo (-1 : ℝ) 0 at htime
    rw [Set.indicator_of_mem htime]
  simp_rw [heq]
  exact (blowup_rescaled_pressureSlice_eLpNorm_threeHalves_eq
    (fun x => p₁ (x, CKN.scalingTime r t₀ t)) ht.1 x₀ r hr).le.trans ht.2

/-- A uniform source-time pressure bound controls the time-integrated
rescaled `L^(3/2)` norm. -/
theorem blowupRieszPressure_time_threeHalves_bound
    (p₁ : ParabolicPoint → ℝ) (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) (J : Set ℝ) (hJmeas : MeasurableSet J)
    (hJ : J ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (M : ℝ≥0∞)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s))
        (volume : Measure Vec3) ∧
      eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞)
        (volume : Measure Vec3) ≤ M) :
    (∫⁻ t in J,
      eLpNorm (fun x : Vec3 => blowupRieszPressure x₀ t₀ r p₁ (x,t))
        (3 / 2 : ℝ≥0∞) (volume : Measure Vec3) ^ (3 / 2 : ℝ)) ≤
      volume J * M ^ (3 / 2 : ℝ) := by
  have hslice := blowupRieszPressure_slice_bound_ae
    p₁ x₀ t₀ r hr J hJmeas hJ M hsource
  calc
    (∫⁻ t in J,
      eLpNorm (fun x : Vec3 => blowupRieszPressure x₀ t₀ r p₁ (x,t))
        (3 / 2 : ℝ≥0∞) volume ^ (3 / 2 : ℝ)) ≤
      ∫⁻ _t in J, M ^ (3 / 2 : ℝ) := by
        apply lintegral_mono_ae
        filter_upwards [hslice] with t ht
        exact ENNReal.rpow_le_rpow ht (by norm_num)
    _ = volume J * M ^ (3 / 2 : ℝ) := by
      rw [setLIntegral_const]
      exact mul_comm _ _

/-- The rescaled whole-space pressure has a uniform space-time
`L^(3/2)` mass bound on a past time interval. -/
theorem blowupRieszPressure_spaceTime_mass_bound
    (p₁ : ParabolicPoint → ℝ)
    (hp₁ : AEStronglyMeasurable p₁
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)))
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (J : Set ℝ) (hJmeas : MeasurableSet J)
    (hJ : J ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (M : ℝ≥0∞)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞) volume ≤ M) :
    (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal |blowupRieszPressure x₀ t₀ r p₁ z| ^ (3 / 2 : ℝ)
      ∂((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict J))) ≤
      volume J * M ^ (3 / 2 : ℝ) := by
  let P := blowupRieszPressure x₀ t₀ r p₁
  have hPm := blowupRieszPressure_aestronglyMeasurable p₁ hp₁ x₀ t₀ r hr
  have hProd : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => P (z.1,z.2))
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict J)) := by
    have hPm' := hPm.restrict
      (s := ((Set.univ : Set Vec3) ×ˢ J : Set ParabolicPoint))
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod] at hPm'
    change AEStronglyMeasurable (fun z : Vec3 × ℝ => P (z.1,z.2))
      ((volume.prod volume).restrict ((Set.univ : Set Vec3) ×ˢ J)) at hPm'
    rw [Measure.prod_restrict]
    exact hPm'
  have hTonelli := blowupScalarTimeThreeHalves_eq
    (Ω := (Set.univ : Set Vec3)) (J := J) P hProd
  have htime := blowupRieszPressure_time_threeHalves_bound
    p₁ x₀ t₀ r hr J hJmeas hJ M hsource
  rw [← hTonelli]
  simpa only [Measure.restrict_univ, P] using htime


end ESS
