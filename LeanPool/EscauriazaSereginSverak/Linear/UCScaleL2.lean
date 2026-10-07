/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleFlatness

/-!
# Quadratic weak-derivative data under scaling

The parabolic dilation used in `lem:uc-gaussian` preserves finite quadratic
energy on the normalized cylinder.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem uc_enorm_smul_sq_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (v : E) :
    ‖c • v‖ₑ ^ (2 : ℝ) ≤ ‖v‖ₑ ^ (2 : ℝ) := by
  rw [enorm_smul, ← ofReal_norm c, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [ENNReal.rpow_ofNat, mul_pow]
  have hcoef : ENNReal.ofReal c ^ (2 : ℕ) ≤ 1 := by
    exact pow_le_one₀ bot_le (ENNReal.ofReal_le_one.mpr hc1)
  simpa only [ENNReal.rpow_ofNat] using
    (mul_le_of_le_one_left (b := ‖v‖ₑ ^ 2) bot_le hcoef)

/-- Finite quadratic weak-derivative data transfers to the normalized
Gaussian cylinder. -/
theorem uc_scaled_l2_data
    (x₀ : Vec3) (R T scale ρ : ℝ) (hscale : 0 < scale)
    (hscale1 : scale ≤ 1) (hball : scale * ρ ≤ R)
    (htime : 2 * scale ^ 2 ≤ T)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball x₀ R) (Ioo 0 T)
      w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    (∫⁻ z in ucCylinder ρ,
      ‖(ucScaledField x₀ scale w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDw x₀ scale Dw) z‖ₑ ^ (2 : ℝ) +
      ‖(ucScaledD2w x₀ scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDtw x₀ scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  let S := spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)
  let Q := spaceTimeSet (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2))
  let F := fun z : ParabolicPoint =>
    ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
      ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)
  have hQsubS : Q ⊆ S := by
    intro z hz
    exact ⟨(mem_vec3Ball).2 ((mem_vec3Ball).1 hz.1 |>.trans_le hball),
      ⟨hz.2.1, hz.2.2.trans_le (by simpa only [mul_comm] using htime)⟩⟩
  have hFfin : (∫⁻ z in Q, F z) < ⊤ :=
    (lintegral_mono_set hQsubS).trans_lt hL2
  have hwm : AEMeasurable (fun z : ParabolicPoint => ‖w z‖ₑ ^ (2 : ℝ))
      (volume.restrict Q) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hweak.1.mono_set hQsubS).aestronglyMeasurable.enorm)
  have hDwm : AEMeasurable (fun z : ParabolicPoint => ‖Dw z‖ₑ ^ (2 : ℝ))
      (volume.restrict Q) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hweak.2.1.mono_set hQsubS).aestronglyMeasurable.enorm)
  have hD2m : AEMeasurable (fun z : ParabolicPoint => ‖D2w z‖ₑ ^ (2 : ℝ))
      (volume.restrict Q) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hweak.2.2.1.mono_set hQsubS).aestronglyMeasurable.enorm)
  have hDtm : AEMeasurable (fun z : ParabolicPoint => ‖Dtw z‖ₑ ^ (2 : ℝ))
      (volume.restrict Q) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hweak.2.2.2.1.mono_set hQsubS).aestronglyMeasurable.enorm)
  have hFm : AEMeasurable F (volume.restrict Q) :=
    ((hwm.add hDwm).add hD2m).add hDtm
  have hΩ : MeasurableSet (vec3Ball x₀ (scale * ρ)) :=
    vec3Ball_measurable _ _
  have hI : MeasurableSet (Ioo 0 (scale ^ 2 * 2)) := measurableSet_Ioo
  have hmap := CKN.map_scalingParabolic_restrict hscale (x₀, 0) hΩ hI
  have hFmap : AEMeasurable F
      (Measure.map (scalingParabolic scale (x₀, 0))
        (volume.restrict
          (spaceTimeSet (rescaledSpace scale x₀ (vec3Ball x₀ (scale * ρ)))
            (rescaledTime scale 0 (Ioo 0 (scale ^ 2 * 2)))))) := by
    rw [hmap]
    exact hFm.smul_measure (ENNReal.ofReal (scale⁻¹ ^ 5))
  have hscaleMeas : Measurable
      (scalingParabolic scale ((x₀, 0) : ParabolicPoint)) := by
    change Measurable (fun z : ParabolicPoint =>
      (scalingSpace scale x₀ z.1, scalingTime scale 0 z.2))
    have hs : Measurable (scalingSpace scale x₀) := by
      exact (measurable_const_add x₀).comp (measurable_const_smul scale)
    have ht : Measurable (scalingTime scale 0) := by
      exact (measurable_const_add (0 : ℝ)).comp
        (measurable_const_mul (scale ^ 2))
    exact (hs.comp measurable_fst).prodMk (ht.comp measurable_snd)
  have hcomp := lintegral_map' hFmap hscaleMeas.aemeasurable
  rw [hmap, lintegral_smul_measure] at hcomp
  have hpoint : scalingParabolic scale (x₀, 0) = ucScaledPoint x₀ scale := by
    funext z
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  have hchange :
      (∫⁻ z in ucCylinder ρ, F (ucScaledPoint x₀ scale z)) =
      ENNReal.ofReal (scale⁻¹ ^ 5) * ∫⁻ z in Q, F z := by
    rw [uc_scaled_cylinder_preimage x₀ scale ρ hscale] at hcomp
    rw [hpoint] at hcomp
    simpa only [Q, Function.comp_def, smul_eq_mul] using hcomp.symm
  have hscale2le : scale ^ 2 ≤ 1 := pow_le_one₀ hscale.le hscale1
  have hpointwise (z : ParabolicPoint) :
      ‖(ucScaledField x₀ scale w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDw x₀ scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledD2w x₀ scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDtw x₀ scale Dtw) z‖ₑ ^ (2 : ℝ) ≤
      F (ucScaledPoint x₀ scale z) := by
    let q := ucScaledPoint x₀ scale z
    change ‖w q‖ₑ ^ (2 : ℝ) +
      ‖scale • Dw q‖ₑ ^ (2 : ℝ) +
      ‖scale ^ 2 • D2w q‖ₑ ^ (2 : ℝ) +
      ‖scale ^ 2 • Dtw q‖ₑ ^ (2 : ℝ) ≤
      ‖w q‖ₑ ^ (2 : ℝ) + ‖Dw q‖ₑ ^ (2 : ℝ) +
        ‖D2w q‖ₑ ^ (2 : ℝ) + ‖Dtw q‖ₑ ^ (2 : ℝ)
    exact add_le_add
      (add_le_add
        (add_le_add le_rfl (uc_enorm_smul_sq_le scale hscale.le hscale1 (Dw q)))
        (uc_enorm_smul_sq_le (scale ^ 2) (sq_nonneg scale) hscale2le (D2w q)))
      (uc_enorm_smul_sq_le (scale ^ 2) (sq_nonneg scale) hscale2le (Dtw q))
  calc
    (∫⁻ z in ucCylinder ρ,
      ‖(ucScaledField x₀ scale w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDw x₀ scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledD2w x₀ scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(ucScaledDtw x₀ scale Dtw) z‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ z in ucCylinder ρ, F (ucScaledPoint x₀ scale z) :=
      lintegral_mono hpointwise
    _ = ENNReal.ofReal (scale⁻¹ ^ 5) * ∫⁻ z in Q, F z := hchange
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin

end ESS
