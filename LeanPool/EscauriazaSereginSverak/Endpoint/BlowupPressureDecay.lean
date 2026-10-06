/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

private theorem pressureCylinder_lintegral_le_timeBound
    (p : ParabolicPoint → ℝ) (H : ℝ → ℝ≥0∞)
    (x₀ : Vec3) (t₀ ρ : ℝ)
    (hball : vec3Ball x₀ ρ ⊆ CKN.euclideanBall 0 (3 / 4 : ℝ))
    (hp : AEStronglyMeasurable p
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hbound : ∀ᵐ t ∂(volume.restrict (Ioc (t₀ - ρ ^ 2) t₀)),
      ∀ᵐ x ∂(volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))),
        ENNReal.ofReal |p (x,t)| ≤ H t) :
    (∫⁻ z in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) ≤
      volume (vec3Ball x₀ ρ) *
        (∫⁻ t in Ioc (t₀ - ρ ^ 2) t₀, H t ^ (3 / 2 : ℝ)) := by
  let Ω := vec3Ball x₀ ρ
  let J := Ioc (t₀ - ρ ^ 2) t₀
  have hmeas : AEMeasurable
      (fun z : ParabolicPoint => ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    simpa only [Real.enorm_eq_ofReal_abs, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hp.enorm)
  rw [CKN.Foundation.Parabolic.Integration.lintegral_parabolicCylinder hmeas]
  have hspatial : ∀ᵐ t ∂(volume.restrict J),
      (∫⁻ x in Ω, ENNReal.ofReal |p (x,t)| ^ (3 / 2 : ℝ)) ≤
        volume Ω * H t ^ (3 / 2 : ℝ) := by
    filter_upwards [hbound] with t ht
    have hsmall := ae_restrict_of_ae_restrict_of_subset hball ht
    have hpoint : ∀ᵐ x ∂(volume.restrict Ω),
        ENNReal.ofReal |p (x,t)| ^ (3 / 2 : ℝ) ≤
          H t ^ (3 / 2 : ℝ) := by
      filter_upwards [hsmall] with x hx
      exact ENNReal.rpow_le_rpow hx (by norm_num)
    calc
      (∫⁻ x in Ω, ENNReal.ofReal |p (x,t)| ^ (3 / 2 : ℝ)) ≤
          ∫⁻ x in Ω, H t ^ (3 / 2 : ℝ) := lintegral_mono_ae hpoint
      _ = volume Ω * H t ^ (3 / 2 : ℝ) := by simp [mul_comm]
  have htime :
      (∫⁻ t in J, ∫⁻ x in Ω,
          ENNReal.ofReal |p (x,t)| ^ (3 / 2 : ℝ)) ≤
        ∫⁻ t in J, volume Ω * H t ^ (3 / 2 : ℝ) :=
    lintegral_mono_ae hspatial
  rw [lintegral_const_mul' (volume Ω) _ (by
    rw [CKN.Foundation.Parabolic.volume_vec3Ball_eq]
    finiteness)] at htime
  exact htime

end ESS

namespace ESS

private theorem rescaledPressure_lintegral_eq
    (f : ParabolicPoint → ℝ) (x₀ : Vec3) (t₀ r S : ℝ)
    (hr : 0 < r) :
    (∫⁻ z in parabolicCylinder 0 0 S,
      ENNReal.ofReal |parabolicRescalePressure x₀ t₀ r f z| ^ (3 / 2 : ℝ)) =
      ENNReal.ofReal (r⁻¹ ^ 2) *
        (∫⁻ z in parabolicCylinder x₀ t₀ (r*S),
          ENNReal.ofReal |f z| ^ (3 / 2 : ℝ)) := by
  have hscaled (z : ParabolicPoint) :
      ENNReal.ofReal |parabolicRescalePressure x₀ t₀ r f z| ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (r ^ 3) *
        ENNReal.ofReal |f (parabolicTranslate x₀ t₀ (parabolicScale r z))| ^
          (3 / 2 : ℝ) := by
    rw [parabolicRescalePressure, abs_mul,
      abs_of_nonneg (sq_nonneg r), ENNReal.ofReal_mul (sq_nonneg r),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2),
      ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r)
        (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    have hscalar : (r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r 3,
        ← Real.rpow_mul hr.le]
      norm_num
    rw [hscalar]
  simp_rw [hscaled]
  have hscale := CKN.Core.Endgame.force_slot_lintegral_scaling hr (x₀,t₀)
    (0,0) S (fun z : ParabolicPoint =>
      ENNReal.ofReal (r ^ 3) * ENNReal.ofReal |f z| ^ (3 / 2 : ℝ))
  have hscale' :
      (∫⁻ z in parabolicCylinder 0 0 S,
        ENNReal.ofReal (r ^ 3) *
          ENNReal.ofReal |f (parabolicTranslate x₀ t₀ (parabolicScale r z))| ^
            (3 / 2 : ℝ)) =
        ENNReal.ofReal (r⁻¹ ^ 5) *
          (∫⁻ z in parabolicCylinder x₀ t₀ (r*S),
            ENNReal.ofReal (r ^ 3) *
              ENNReal.ofReal |f z| ^ (3 / 2 : ℝ)) := by
    simpa [CKN.scalingParabolic, parabolicTranslate, parabolicScale] using hscale
  rw [hscale']
  rw [lintegral_const_mul' (ENNReal.ofReal (r ^ 3)) _ ENNReal.ofReal_ne_top]
  have hcoeff : ENNReal.ofReal (r⁻¹ ^ 5) * ENNReal.ofReal (r ^ 3) =
      ENNReal.ofReal (r⁻¹ ^ 2) := by
    rw [← ENNReal.ofReal_mul (p := r⁻¹ ^ 5) (q := r ^ 3)
      (by positivity : 0 ≤ r⁻¹ ^ 5)]
    congr 1
    field_simp
  rw [← mul_assoc, hcoeff]

end ESS

namespace ESS

/-- The rescaled pressure has order-`r` critical mass on a fixed cylinder
when its unscaled slices have an integrable spatial supremum bound. -/
theorem blowupHarmonicRemainder_mass_le
    (f : ParabolicPoint → ℝ) (H : ℝ → ℝ≥0∞)
    (x₀ : Vec3) (t₀ r S : ℝ) (hr : 0 < r) (hS : 0 < S)
    (hball : vec3Ball x₀ (r*S) ⊆ CKN.euclideanBall 0 (3 / 4 : ℝ))
    (hf : AEStronglyMeasurable f
      (volume.restrict (parabolicCylinder x₀ t₀ (r*S))))
    (hbound : ∀ᵐ t ∂(volume.restrict (Ioc (t₀ - (r*S) ^ 2) t₀)),
      ∀ᵐ x ∂(volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))),
        ENNReal.ofReal |f (x,t)| ≤ H t) :
    (∫⁻ z in parabolicCylinder 0 0 S,
      ENNReal.ofReal |parabolicRescalePressure x₀ t₀ r f z| ^ (3 / 2 : ℝ)) ≤
        ENNReal.ofReal (r*S^3) *
          ENNReal.ofReal (Real.pi * 4 / 3) *
            (∫⁻ t, H t ^ (3 / 2 : ℝ)) := by
  have hscale := rescaledPressure_lintegral_eq f x₀ t₀ r S hr
  have hsource := pressureCylinder_lintegral_le_timeBound f H x₀ t₀ (r*S)
    hball hf hbound
  have htime :
      (∫⁻ t in Ioc (t₀ - (r*S)^2) t₀, H t ^ (3 / 2 : ℝ)) ≤
        ∫⁻ t, H t ^ (3 / 2 : ℝ) :=
    by simpa only [setLIntegral_univ] using
      (lintegral_mono_set (subset_univ _))
  have hcoeff :
      ENNReal.ofReal (r⁻¹ ^ 2) * volume (vec3Ball x₀ (r*S)) =
        ENNReal.ofReal (r*S^3) * ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [CKN.Foundation.Parabolic.volume_vec3Ball_eq,
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ r*S) 3,
      ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ r⁻¹ ^ 2)]
    congr 1
    field_simp
  calc
    _ = ENNReal.ofReal (r⁻¹ ^ 2) *
        (∫⁻ z in parabolicCylinder x₀ t₀ (r*S),
          ENNReal.ofReal |f z| ^ (3 / 2 : ℝ)) := hscale
    _ ≤ ENNReal.ofReal (r⁻¹ ^ 2) *
        (volume (vec3Ball x₀ (r*S)) *
          (∫⁻ t in Ioc (t₀ - (r*S)^2) t₀, H t ^ (3 / 2 : ℝ))) := by
            gcongr
    _ ≤ ENNReal.ofReal (r⁻¹ ^ 2) *
        (volume (vec3Ball x₀ (r*S)) *
          (∫⁻ t, H t ^ (3 / 2 : ℝ))) := by
            gcongr
    _ = _ := by rw [← mul_assoc, hcoeff]

/-- The rescaled remainder vanishes in critical mass on each fixed cylinder
when its source slices have a finite time-integrated supremum bound. -/
theorem blowupHarmonicRemainder_mass_tendsto_zero
    (f : ParabolicPoint → ℝ) (H : ℝ → ℝ≥0∞)
    (x₀ : Vec3) (t₀ S : ℝ) (hS : 0 < S) (r : ℕ → ℝ)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (hH : (∫⁻ t, H t ^ (3 / 2 : ℝ)) < ⊤)
    (hball : ∀ᶠ k in atTop,
      vec3Ball x₀ (r k*S) ⊆ CKN.euclideanBall 0 (3 / 4 : ℝ))
    (hf : ∀ᶠ k in atTop,
      AEStronglyMeasurable f
        (volume.restrict (parabolicCylinder x₀ t₀ (r k*S))))
    (hbound : ∀ᶠ k in atTop,
      ∀ᵐ t ∂(volume.restrict (Ioc (t₀ - (r k*S) ^ 2) t₀)),
        ∀ᵐ x ∂(volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))),
          ENNReal.ofReal |f (x,t)| ≤ H t) :
    Tendsto (fun k =>
      ∫⁻ z in parabolicCylinder 0 0 S,
        ENNReal.ofReal |parabolicRescalePressure x₀ t₀ (r k) f z| ^
          (3 / 2 : ℝ)) atTop (nhds 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3) *
    (∫⁻ t, H t ^ (3 / 2 : ℝ))
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH
  have hR : Tendsto (fun k => r k * S^3) atTop (nhds (0 : ℝ)) := by
    simpa only [zero_mul] using hr0.mul_const (S^3)
  have hRenn : Tendsto (fun k => ENNReal.ofReal (r k * S^3))
      atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hR
  have hRbound : Tendsto (fun k => ENNReal.ofReal (r k*S^3) * C)
      atTop (nhds 0) := by
    have h := ENNReal.Tendsto.mul hRenn (Or.inr hC.ne)
      tendsto_const_nhds (Or.inr ENNReal.zero_ne_top)
    simpa only [zero_mul] using h
  have hupper : ∀ᶠ k in atTop,
      (∫⁻ z in parabolicCylinder 0 0 S,
        ENNReal.ofReal |parabolicRescalePressure x₀ t₀ (r k) f z| ^
          (3 / 2 : ℝ)) ≤ ENNReal.ofReal (r k*S^3) * C := by
    filter_upwards [hball, hf, hbound] with k hkB hkF hkH
    have h := blowupHarmonicRemainder_mass_le f H x₀ t₀ (r k) S
      (hr k) hS hkB hkF hkH
    simpa only [C, mul_assoc] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hRbound
    (Eventually.of_forall fun k => bot_le) hupper

/-- Positive parabolic rescaling preserves almost-everywhere strong
measurability of a whole-space scalar pressure. -/
theorem blowupRescaledPressure_aestronglyMeasurable
    (f : ParabolicPoint → ℝ) (hf : AEStronglyMeasurable f (volume : Measure ParabolicPoint))
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    AEStronglyMeasurable (parabolicRescalePressure x₀ t₀ r f)
      (volume : Measure ParabolicPoint) := by
  let z₀ : ParabolicPoint := (x₀,t₀)
  let c : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 5)
  have hmap : Measure.map (CKN.scalingParabolic r z₀) volume =
      c • (volume : Measure ParabolicPoint) :=
    CKN.map_scalingParabolic r hr z₀
  have hfc : AEStronglyMeasurable f (c • (volume : Measure ParabolicPoint)) :=
    hf.mono_ac Measure.smul_absolutelyContinuous
  have hfm : AEStronglyMeasurable f
      (Measure.map (CKN.scalingParabolic r z₀) volume) := by
    rw [hmap]
    exact hfc
  have hscaleMeas : Measurable (CKN.scalingParabolic r z₀) := by
    unfold CKN.scalingParabolic parabolicTranslate parabolicScale
    fun_prop
  have hcomp : AEStronglyMeasurable (f ∘ CKN.scalingParabolic r z₀)
      (volume : Measure ParabolicPoint) :=
    hfm.comp_aemeasurable hscaleMeas.aemeasurable
  have hmul := hcomp.const_mul (r^2)
  change AEStronglyMeasurable (fun z : ParabolicPoint =>
    r^2 * f (parabolicTranslate x₀ t₀ (parabolicScale r z))) volume
  simpa only [Function.comp_def, CKN.scalingParabolic, z₀] using hmul

end ESS
