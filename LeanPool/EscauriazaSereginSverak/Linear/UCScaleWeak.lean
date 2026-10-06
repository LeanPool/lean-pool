/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleL2
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Weak derivatives under the Gaussian parabolic dilation

Smooth compactly supported tests transport through the affine coordinates
used in `lem:uc-gaussian`.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Parabolic scaling about a spatial center, with quadratic scaling of time. -/
@[expose] def ucScaleHomeomorph (scale : ℝ) (hscale : 0 < scale)
    (x₀ : Vec3) : (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero scale hscale.ne').trans (Homeomorph.addLeft x₀))
    ((Homeomorph.smulOfNeZero (scale ^ 2) (sq_pos_of_pos hscale).ne').trans
      (Homeomorph.addLeft 0))

private theorem ucScaleHomeomorph_eq (scale : ℝ) (hscale : 0 < scale)
    (x₀ : Vec3) :
    ⇑(ucScaleHomeomorph scale hscale x₀) = ucScaledPoint x₀ scale := by
  funext z
  change (x₀ + scale • z.1, 0 + scale ^ 2 * z.2) =
    (x₀ + scale • z.1, scale ^ 2 * z.2)
  simp only [zero_add]

private theorem ucScaleHomeomorph_symm_eq (scale : ℝ) (hscale : 0 < scale)
    (x₀ : Vec3) :
    ⇑(ucScaleHomeomorph scale hscale x₀).symm =
      (fun z : Vec3 × ℝ =>
        (scale⁻¹ • (z.1 - x₀), (scale ^ 2)⁻¹ * z.2)) := by
  ext z
  all_goals simp [ucScaleHomeomorph, Homeomorph.trans, Homeomorph.prodCongr,
      Homeomorph.smulOfNeZero, Homeomorph.addLeft,
      Equiv.addLeft, Units.smul_def]
  all_goals ring

private theorem ucScaleHomeomorph_symm_contDiff (scale : ℝ)
    (hscale : 0 < scale) (x₀ : Vec3) :
    ContDiff ℝ (⊤ : ℕ∞) (ucScaleHomeomorph scale hscale x₀).symm := by
  rw [ucScaleHomeomorph_symm_eq scale hscale x₀]
  fun_prop

private theorem ucScaleHomeomorph_image_cylinder
    (scale ρ : ℝ) (hscale : 0 < scale) (x₀ : Vec3) :
    ucScaleHomeomorph scale hscale x₀ '' ucCylinder ρ =
      spaceTimeSet (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2)) := by
  have hpre := uc_scaled_cylinder_preimage x₀ scale ρ hscale
  have hscaleEq : scalingParabolic scale ((x₀, 0) : ParabolicPoint) =
      (ucScaleHomeomorph scale hscale x₀) := by
    funext z
    rw [ucScaleHomeomorph_eq]
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  have hpre' : (ucScaleHomeomorph scale hscale x₀) ⁻¹'
      spaceTimeSet (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2)) =
        ucCylinder ρ := by
    calc
      _ = scalingParabolic scale ((x₀, 0) : ParabolicPoint) ⁻¹'
          spaceTimeSet (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2)) := by
            rw [hscaleEq]
            rfl
      _ = spaceTimeSet
          (rescaledSpace scale x₀ (vec3Ball x₀ (scale * ρ)))
          (rescaledTime scale 0 (Ioo 0 (scale ^ 2 * 2))) := by
            exact (rescaledSpaceTimeSet_eq_preimage scale
              ((x₀, 0) : ParabolicPoint) _ _).symm
      _ = ucCylinder ρ := hpre
  rw [← hpre']
  exact (ucScaleHomeomorph scale hscale x₀).image_preimage _

private theorem uc_scale_pullback_test
    (scale ρ : ℝ) (hscale : 0 < scale) (x₀ : Vec3)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (vec3Ball 0 ρ) (Ioo 0 2)) :
    (ψ ∘ (ucScaleHomeomorph scale hscale x₀).symm) ∈
      spaceTimeTestFunction (V := ℝ)
        (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2)) := by
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  refine ⟨hψdiff.comp (ucScaleHomeomorph_symm_contDiff scale hscale x₀),
    hψcompact.comp_homeomorph (ucScaleHomeomorph scale hscale x₀).symm, ?_⟩
  rw [tsupport_comp_eq_preimage ψ (ucScaleHomeomorph scale hscale x₀).symm]
  rw [← (ucScaleHomeomorph scale hscale x₀).image_eq_preimage_symm]
  exact (image_mono hψsupport).trans_eq
    (ucScaleHomeomorph_image_cylinder scale ρ hscale x₀)

private theorem uc_scaled_field_aestronglyMeasurable
    {E : Type*} [NormedAddCommGroup E]
    (x₀ : Vec3) (scale ρ : ℝ) (hscale : 0 < scale)
    (f : ParabolicPoint → E)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet
        (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2))))) :
    AEStronglyMeasurable (f ∘ ucScaledPoint x₀ scale)
      (volume.restrict (ucCylinder ρ)) := by
  have hΩ : MeasurableSet (vec3Ball x₀ (scale * ρ)) :=
    vec3Ball_measurable _ _
  have hI : MeasurableSet (Ioo 0 (scale ^ 2 * 2)) := measurableSet_Ioo
  have hmap := CKN.map_scalingParabolic_restrict hscale
    ((x₀, 0) : ParabolicPoint) hΩ hI
  have hpoint : scalingParabolic scale ((x₀, 0) : ParabolicPoint) =
      ucScaledPoint x₀ scale := by
    funext z
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  rw [uc_scaled_cylinder_preimage x₀ scale ρ hscale, hpoint] at hmap
  have hfm : AEStronglyMeasurable f
      (Measure.map (ucScaledPoint x₀ scale)
        (volume.restrict (ucCylinder ρ))) := by
    rw [hmap]
    exact hf.smul_measure (ENNReal.ofReal (scale⁻¹ ^ 5))
  have hpointMeas : Measurable (ucScaledPoint x₀ scale) := by
    change Measurable (fun z : ParabolicPoint =>
      (x₀ + scale • z.1, scale ^ 2 * z.2))
    have hs : Measurable (fun y : Vec3 => x₀ + scale • y) :=
      (measurable_const_add x₀).comp (measurable_const_smul scale)
    have ht : Measurable (fun s : ℝ => scale ^ 2 * s) :=
      measurable_const_mul (scale ^ 2)
    exact (hs.comp measurable_fst).prodMk (ht.comp measurable_snd)
  exact hfm.comp_measurable hpointMeas

private theorem uc_integrableOn_of_l2
    {E : Type*} [NormedAddCommGroup E]
    (Q : Set ParabolicPoint) (hQ : volume Q < ⊤)
    (f : ParabolicPoint → E)
    (hfmeas : AEStronglyMeasurable f (volume.restrict Q))
    (hL2 : (∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤) :
    IntegrableOn f Q volume := by
  have hfinite : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa using hQ⟩
  have hfLp : MemLp f (2 : ℝ≥0∞) (volume.restrict Q) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (μ := volume.restrict Q)
      (by norm_num) (by norm_num) hfmeas).2
    simpa using hL2
  exact (letI := hfinite; hfLp.integrable (by norm_num))

private theorem uc_spatial_weak_identity_scaled
    (x₀ : Vec3) (scale ρ c : ℝ) (hscale : 0 < scale)
    (f g : ParabolicPoint → ℝ) (j : Fin 3)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))))
    (hsource : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2)) →
      (∫ z in spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)), f z * spatialPartial φ j z) =
        -∫ z in spaceTimeSet (vec3Ball x₀ (scale * ρ))
          (Ioo 0 (scale ^ 2 * 2)), g z * φ z)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (vec3Ball 0 ρ) (Ioo 0 2)) :
    (∫ z in ucCylinder ρ,
      (c * f (ucScaledPoint x₀ scale z)) * spatialPartial ψ j z) =
      -∫ z in ucCylinder ρ,
        (c * scale * g (ucScaledPoint x₀ scale z)) * ψ z := by
  let ψhat : Vec3 × ℝ → ℝ :=
    ψ ∘ (ucScaleHomeomorph scale hscale x₀).symm
  have hψhat : ψhat ∈ spaceTimeTestFunction (V := ℝ)
      (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2)) :=
    uc_scale_pullback_test scale ρ hscale x₀ hψ
  have hS := hsource ψhat hψhat
  let Q := spaceTimeSet (vec3Ball x₀ (scale * ρ))
    (Ioo 0 (scale ^ 2 * 2))
  let A := fun z : ParabolicPoint => f z * spatialPartial ψhat j z
  let B := fun z : ParabolicPoint => g z * ψhat z
  have hpartC : Continuous (fun z : ParabolicPoint => spatialPartial ψhat j z) := by
    have hc := (spatialPartial_contDiff hψhat.1 j).continuous.comp
      parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  have hhatC : Continuous (fun z : ParabolicPoint => ψhat z) := by
    have hc := hψhat.1.continuous.comp parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  have hAm : AEStronglyMeasurable A (volume.restrict Q) :=
    hf.mul hpartC.aestronglyMeasurable
  have hBm : AEStronglyMeasurable B (volume.restrict Q) :=
    hg.mul hhatC.aestronglyMeasurable
  have hpoint : scalingParabolic scale ((x₀, 0) : ParabolicPoint) =
      ucScaledPoint x₀ scale := by
    funext z
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  have hchange (F : ParabolicPoint → ℝ)
      (hFm : AEStronglyMeasurable F (volume.restrict Q)) :
      (∫ z in ucCylinder ρ, F (ucScaledPoint x₀ scale z)) =
        scale⁻¹ ^ 5 * ∫ z in Q, F z := by
    have hΩ : MeasurableSet (vec3Ball x₀ (scale * ρ)) :=
      vec3Ball_measurable _ _
    have hI : MeasurableSet (Ioo 0 (scale ^ 2 * 2)) := measurableSet_Ioo
    have hc := CKN.integral_comp_scaling_test scale hscale
      ((x₀, 0) : ParabolicPoint)
      (Ω := vec3Ball x₀ (scale * ρ)) (I := Ioo 0 (scale ^ 2 * 2))
      (F := F) hΩ hI hFm
    rw [uc_scaled_cylinder_preimage x₀ scale ρ hscale, hpoint] at hc
    rw [ENNReal.toReal_ofReal (by positivity)] at hc
    simpa only [Q, smul_eq_mul] using hc
  have hAchange := hchange A hAm
  have hBchange := hchange B hBm
  have hψhat_eq : ψhat = ψ ∘
      (fun z : Vec3 × ℝ =>
        (scale⁻¹ • (z.1 - x₀), (scale ^ 2)⁻¹ * z.2)) := by
    exact congrArg (fun k => ψ ∘ k)
      (ucScaleHomeomorph_symm_eq scale hscale x₀)
  have hhat_at (z : ParabolicPoint) :
      ψhat (ucScaledPoint x₀ scale z) = ψ z := by
    rw [hψhat_eq]
    change ψ (scale⁻¹ • (x₀ + scale • z.1 - x₀),
      (scale ^ 2)⁻¹ * (scale ^ 2 * z.2)) = ψ z
    have hs : scale⁻¹ • (x₀ + scale • z.1 - x₀) = z.1 := by
      simp [smul_smul, hscale.ne']
    have ht : (scale ^ 2)⁻¹ * (scale ^ 2 * z.2) = z.2 := by
      field_simp [hscale.ne']
    rw [hs, ht]
    rfl
  have hderiv (z : ParabolicPoint) :
      spatialPartial ψhat j (ucScaledPoint x₀ scale z) =
        scale⁻¹ * spatialPartial ψ j z := by
    rw [hψhat_eq]
    have hp := CKN.spatialPartial_pullback scale hscale
      ((x₀, 0) : ParabolicPoint) hψ.1 j z
    rw [hpoint] at hp
    simp only [sub_zero] at hp
    exact hp
  have hderiv' (z : ParabolicPoint) :
      spatialPartial ψ j z =
        scale * spatialPartial ψhat j (ucScaledPoint x₀ scale z) := by
    rw [hderiv]
    field_simp [hscale.ne']
  have hAint :
      (∫ z in ucCylinder ρ,
        (c * f (ucScaledPoint x₀ scale z)) * spatialPartial ψ j z) =
      c * scale * (∫ z in ucCylinder ρ,
        A (ucScaledPoint x₀ scale z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [A]
    rw [hderiv']
    ring
  have hBint :
      (∫ z in ucCylinder ρ,
        (c * scale * g (ucScaledPoint x₀ scale z)) * ψ z) =
      c * scale * (∫ z in ucCylinder ρ,
        B (ucScaledPoint x₀ scale z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [B]
    rw [hhat_at]
    ring
  calc
    (∫ z in ucCylinder ρ,
        (c * f (ucScaledPoint x₀ scale z)) * spatialPartial ψ j z) =
        c * scale * (scale⁻¹ ^ 5 * ∫ z in Q, A z) := by
          rw [hAint, hAchange]
    _ = -(c * scale * (scale⁻¹ ^ 5 * ∫ z in Q, B z)) := by
      have hs : (∫ z in Q, A z) = -∫ z in Q, B z := hS
      rw [hs]
      ring
    _ = -∫ z in ucCylinder ρ,
        (c * scale * g (ucScaledPoint x₀ scale z)) * ψ z := by
      rw [hBint, hBchange]

private theorem uc_time_weak_identity_scaled
    (x₀ : Vec3) (scale ρ c : ℝ) (hscale : 0 < scale)
    (f g : ParabolicPoint → ℝ)
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))))
    (hsource : ∀ φ : ParabolicPoint → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2)) →
      (∫ z in spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)), f z * timePartial φ z) =
        -∫ z in spaceTimeSet (vec3Ball x₀ (scale * ρ))
          (Ioo 0 (scale ^ 2 * 2)), g z * φ z)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (vec3Ball 0 ρ) (Ioo 0 2)) :
    (∫ z in ucCylinder ρ,
      (c * f (ucScaledPoint x₀ scale z)) * timePartial ψ z) =
      -∫ z in ucCylinder ρ,
        (c * scale ^ 2 * g (ucScaledPoint x₀ scale z)) * ψ z := by
  let ψhat : Vec3 × ℝ → ℝ :=
    ψ ∘ (ucScaleHomeomorph scale hscale x₀).symm
  have hψhat : ψhat ∈ spaceTimeTestFunction (V := ℝ)
      (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2)) :=
    uc_scale_pullback_test scale ρ hscale x₀ hψ
  have hS := hsource ψhat hψhat
  let Q := spaceTimeSet (vec3Ball x₀ (scale * ρ))
    (Ioo 0 (scale ^ 2 * 2))
  let A := fun z : ParabolicPoint => f z * timePartial ψhat z
  let B := fun z : ParabolicPoint => g z * ψhat z
  have hpartC : Continuous (fun z : ParabolicPoint => timePartial ψhat z) := by
    have hc := (contDiff_timePartial hψhat.1).continuous.comp
      parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  have hhatC : Continuous (fun z : ParabolicPoint => ψhat z) := by
    have hc := hψhat.1.continuous.comp parabolicHomeomorph.continuous
    exact hc.congr (fun _ => rfl)
  have hAm : AEStronglyMeasurable A (volume.restrict Q) :=
    hf.mul hpartC.aestronglyMeasurable
  have hBm : AEStronglyMeasurable B (volume.restrict Q) :=
    hg.mul hhatC.aestronglyMeasurable
  have hpoint : scalingParabolic scale ((x₀, 0) : ParabolicPoint) =
      ucScaledPoint x₀ scale := by
    funext z
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  have hchange (F : ParabolicPoint → ℝ)
      (hFm : AEStronglyMeasurable F (volume.restrict Q)) :
      (∫ z in ucCylinder ρ, F (ucScaledPoint x₀ scale z)) =
        scale⁻¹ ^ 5 * ∫ z in Q, F z := by
    have hΩ : MeasurableSet (vec3Ball x₀ (scale * ρ)) :=
      vec3Ball_measurable _ _
    have hI : MeasurableSet (Ioo 0 (scale ^ 2 * 2)) := measurableSet_Ioo
    have hc := CKN.integral_comp_scaling_test scale hscale
      ((x₀, 0) : ParabolicPoint)
      (Ω := vec3Ball x₀ (scale * ρ)) (I := Ioo 0 (scale ^ 2 * 2))
      (F := F) hΩ hI hFm
    rw [uc_scaled_cylinder_preimage x₀ scale ρ hscale, hpoint] at hc
    rw [ENNReal.toReal_ofReal (by positivity)] at hc
    simpa only [Q, smul_eq_mul] using hc
  have hAchange := hchange A hAm
  have hBchange := hchange B hBm
  have hψhat_eq : ψhat = ψ ∘
      (fun z : Vec3 × ℝ =>
        (scale⁻¹ • (z.1 - x₀), (scale ^ 2)⁻¹ * z.2)) := by
    exact congrArg (fun k => ψ ∘ k)
      (ucScaleHomeomorph_symm_eq scale hscale x₀)
  have hhat_at (z : ParabolicPoint) :
      ψhat (ucScaledPoint x₀ scale z) = ψ z := by
    rw [hψhat_eq]
    change ψ (scale⁻¹ • (x₀ + scale • z.1 - x₀),
      (scale ^ 2)⁻¹ * (scale ^ 2 * z.2)) = ψ z
    have hs : scale⁻¹ • (x₀ + scale • z.1 - x₀) = z.1 := by
      simp [smul_smul, hscale.ne']
    have ht : (scale ^ 2)⁻¹ * (scale ^ 2 * z.2) = z.2 := by
      field_simp [hscale.ne']
    rw [hs, ht]
    rfl
  have hderiv (z : ParabolicPoint) :
      timePartial ψhat (ucScaledPoint x₀ scale z) =
        (scale ^ 2)⁻¹ * timePartial ψ z := by
    rw [hψhat_eq]
    have hp := CKN.timePartial_pullback scale hscale
      ((x₀, 0) : ParabolicPoint) hψ.1 z
    rw [hpoint] at hp
    simp only [sub_zero] at hp
    exact hp
  have hderiv' (z : ParabolicPoint) :
      timePartial ψ z =
        scale ^ 2 * timePartial ψhat (ucScaledPoint x₀ scale z) := by
    rw [hderiv]
    field_simp [hscale.ne']
  have hAint :
      (∫ z in ucCylinder ρ,
        (c * f (ucScaledPoint x₀ scale z)) * timePartial ψ z) =
      c * scale ^ 2 * (∫ z in ucCylinder ρ,
        A (ucScaledPoint x₀ scale z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [A]
    rw [hderiv']
    ring
  have hBint :
      (∫ z in ucCylinder ρ,
        (c * scale ^ 2 * g (ucScaledPoint x₀ scale z)) * ψ z) =
      c * scale ^ 2 * (∫ z in ucCylinder ρ,
        B (ucScaledPoint x₀ scale z)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [B]
    rw [hhat_at]
    ring
  calc
    (∫ z in ucCylinder ρ,
        (c * f (ucScaledPoint x₀ scale z)) * timePartial ψ z) =
        c * scale ^ 2 * (scale⁻¹ ^ 5 * ∫ z in Q, A z) := by
          rw [hAint, hAchange]
    _ = -(c * scale ^ 2 * (scale⁻¹ ^ 5 * ∫ z in Q, B z)) := by
      have hs : (∫ z in Q, A z) = -∫ z in Q, B z := hS
      rw [hs]
      ring
    _ = -∫ z in ucCylinder ρ,
        (c * scale ^ 2 * g (ucScaledPoint x₀ scale z)) * ψ z := by
      rw [hBint, hBchange]

/-- The specified weak derivative identities transport under a positive
parabolic dilation onto the normalized Gaussian cylinder. -/
theorem uc_scaled_weak_derivatives
    (x₀ : Vec3) (scale ρ : ℝ) (hscale : 0 < scale)
    (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs
      (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2))
      w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ (scale * ρ))
      (Ioo 0 (scale ^ 2 * 2)),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      (ucScaledField x₀ scale w) (ucScaledDw x₀ scale Dw)
      (ucScaledD2w x₀ scale D2w) (ucScaledDtw x₀ scale Dtw) := by
  have hQfinite : volume (ucCylinder ρ) < ⊤ := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change ((volume : Measure Vec3).prod (volume : Measure ℝ))
      (vec3Ball 0 ρ ×ˢ Ioo 0 2) < ⊤
    rw [Measure.prod_prod, volume_vec3Ball_eq, Real.volume_Ioo]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by finiteness) (by finiteness)) (by finiteness)
  have hL2scaled := uc_scaled_l2_data x₀ (scale * ρ) (scale ^ 2 * 2)
    scale ρ hscale hscale1 le_rfl (by rw [mul_comm])
      w Dw D2w Dtw hweak hL2
  have hwm : AEStronglyMeasurable (ucScaledField x₀ scale w)
      (volume.restrict (ucCylinder ρ)) := by
    change AEStronglyMeasurable (w ∘ ucScaledPoint x₀ scale)
      (volume.restrict (ucCylinder ρ))
    exact uc_scaled_field_aestronglyMeasurable x₀ scale ρ hscale w
      hweak.1.aestronglyMeasurable
  have hDwm : AEStronglyMeasurable (ucScaledDw x₀ scale Dw)
      (volume.restrict (ucCylinder ρ)) := by
    have hm := uc_scaled_field_aestronglyMeasurable x₀ scale ρ hscale Dw
      hweak.2.1.aestronglyMeasurable
    change AEStronglyMeasurable
      (fun z => scale • (Dw (ucScaledPoint x₀ scale z)))
      (volume.restrict (ucCylinder ρ))
    exact hm.const_smul scale
  have hD2m : AEStronglyMeasurable (ucScaledD2w x₀ scale D2w)
      (volume.restrict (ucCylinder ρ)) := by
    have hm := uc_scaled_field_aestronglyMeasurable x₀ scale ρ hscale D2w
      hweak.2.2.1.aestronglyMeasurable
    change AEStronglyMeasurable
      (fun z => scale ^ 2 • (D2w (ucScaledPoint x₀ scale z)))
      (volume.restrict (ucCylinder ρ))
    exact hm.const_smul (scale ^ 2)
  have hDtm : AEStronglyMeasurable (ucScaledDtw x₀ scale Dtw)
      (volume.restrict (ucCylinder ρ)) := by
    have hm := uc_scaled_field_aestronglyMeasurable x₀ scale ρ hscale Dtw
      hweak.2.2.2.1.aestronglyMeasurable
    change AEStronglyMeasurable
      (fun z => scale ^ 2 • (Dtw (ucScaledPoint x₀ scale z)))
      (volume.restrict (ucCylinder ρ))
    exact hm.const_smul (scale ^ 2)
  have hwL2 : (∫⁻ z in ucCylinder ρ,
      ‖(ucScaledField x₀ scale w) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt hL2scaled
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
  have hDwL2 : (∫⁻ z in ucCylinder ρ,
      ‖(ucScaledDw x₀ scale Dw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt hL2scaled
    exact le_add_of_nonneg_left (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
  have hD2L2 : (∫⁻ z in ucCylinder ρ,
      ‖(ucScaledD2w x₀ scale D2w) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt hL2scaled
    exact le_add_of_nonneg_left (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity))
  have hDtL2 : (∫⁻ z in ucCylinder ρ,
      ‖(ucScaledDtw x₀ scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt hL2scaled
    exact le_add_of_nonneg_left (by positivity)
  have hwloc : LocallyIntegrableOn (ucScaledField x₀ scale w)
      (ucCylinder ρ) volume :=
    (uc_integrableOn_of_l2 (ucCylinder ρ) hQfinite _ hwm hwL2).locallyIntegrableOn
  have hDwloc : LocallyIntegrableOn (ucScaledDw x₀ scale Dw)
      (ucCylinder ρ) volume :=
    (uc_integrableOn_of_l2 (ucCylinder ρ) hQfinite _ hDwm hDwL2).locallyIntegrableOn
  have hD2loc : LocallyIntegrableOn (ucScaledD2w x₀ scale D2w)
      (ucCylinder ρ) volume :=
    (uc_integrableOn_of_l2 (ucCylinder ρ) hQfinite _ hD2m hD2L2).locallyIntegrableOn
  have hDtloc : LocallyIntegrableOn (ucScaledDtw x₀ scale Dtw)
      (ucCylinder ρ) volume :=
    (uc_integrableOn_of_l2 (ucCylinder ρ) hQfinite _ hDtm hDtL2).locallyIntegrableOn
  have hwm_i (i : Fin 3) : AEStronglyMeasurable (fun z => w z i)
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))) :=
    (continuous_apply i).comp_aestronglyMeasurable
      hweak.1.aestronglyMeasurable
  have hDwm_ij (i j : Fin 3) : AEStronglyMeasurable (fun z => Dw z i j)
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))) :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable
        hweak.2.1.aestronglyMeasurable)
  have hD2m_ijk (i j k : Fin 3) : AEStronglyMeasurable
      (fun z => D2w z i j k)
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))) :=
    (continuous_apply k).comp_aestronglyMeasurable
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply i).comp_aestronglyMeasurable
          hweak.2.2.1.aestronglyMeasurable))
  have hDtm_i (i : Fin 3) : AEStronglyMeasurable (fun z => Dtw z i)
      (volume.restrict (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))) :=
    (continuous_apply i).comp_aestronglyMeasurable
      hweak.2.2.2.1.aestronglyMeasurable
  refine ⟨hwloc, hDwloc, hD2loc, hDtloc, ?_⟩
  intro ψ hψ
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have h := uc_spatial_weak_identity_scaled x₀ scale ρ 1 hscale
      (fun z => w z i) (fun z => Dw z i j) j
      (hwm_i i) (hDwm_ij i j)
      (fun φ hφ => (hweak.2.2.2.2 φ hφ).1 i j) ψ hψ
    simpa only [ucCylinder, ucScaledField, ucScaledDw, one_mul, Pi.smul_apply,
      smul_eq_mul] using h
  · intro i j k
    have h := uc_spatial_weak_identity_scaled x₀ scale ρ scale hscale
      (fun z => Dw z i j) (fun z => D2w z i j k) k
      (hDwm_ij i j) (hD2m_ijk i j k)
      (fun φ hφ => (hweak.2.2.2.2 φ hφ).2.1 i j k) ψ hψ
    simpa only [ucCylinder, ucScaledDw, ucScaledD2w, Pi.smul_apply,
      smul_eq_mul, pow_two, mul_assoc] using h
  · intro i
    have h := uc_time_weak_identity_scaled x₀ scale ρ 1 hscale
      (fun z => w z i) (fun z => Dtw z i)
      (hwm_i i) (hDtm_i i)
      (fun φ hφ => (hweak.2.2.2.2 φ hφ).2.2 i) ψ hψ
    simpa only [ucCylinder, ucScaledField, ucScaledDtw, Pi.smul_apply,
      smul_eq_mul, one_mul] using h

end ESS
