/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCTargetGeometry
public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleIntegration

/-!
# Returning the Gaussian target box to the source variables

The target box under parabolic dilation is the box appearing in
`eq:uc-gaussian-box`.
-/

public section


open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The normalized target box is the inverse image of the source box under
the Gaussian parabolic dilation (`lem:uc-gaussian`). -/
theorem uc_target_box_preimage
    (x₀ x : Vec3) (scale t : ℝ) (hscale : 0 < scale)
    (hscaleSq : scale ^ 2 = 2 * t) :
    spaceTimeSet
      (rescaledSpace scale x₀ (vec3Ball x scale))
      (rescaledTime scale 0 (Ioo t (2 * t))) =
        spaceTimeSet (vec3Ball (scale⁻¹ • (x - x₀)) 1)
          (Ioo (1 / 2) 1) := by
  ext z
  have hs2 : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hspace :
      z.1 ∈ rescaledSpace scale x₀ (vec3Ball x scale) ↔
        z.1 ∈ vec3Ball (scale⁻¹ • (x - x₀)) 1 := by
    change vec3EuclideanNorm (x₀ + scale • z.1 - x) < scale ↔
      vec3EuclideanNorm (z.1 - scale⁻¹ • (x - x₀)) < 1
    have heq : x₀ + scale • z.1 - x =
        scale • (z.1 - scale⁻¹ • (x - x₀)) := by
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [ne_of_gt hscale]
      ring
    rw [heq, vec3EuclideanNorm_smul, abs_of_pos hscale]
    simpa only [mul_one] using
      (mul_lt_mul_iff_of_pos_left hscale :
        (scale * vec3EuclideanNorm (z.1 - scale⁻¹ • (x - x₀)) < scale * 1) ↔
          vec3EuclideanNorm (z.1 - scale⁻¹ • (x - x₀)) < 1)
  have htime :
      z.2 ∈ rescaledTime scale 0 (Ioo t (2 * t)) ↔
        z.2 ∈ Ioo (1 / 2) 1 := by
    change (t < 0 + scale ^ 2 * z.2 ∧
      0 + scale ^ 2 * z.2 < 2 * t) ↔
      (1 / 2 < z.2 ∧ z.2 < 1)
    have ht : t = scale ^ 2 * (1 / 2) := by
      linarith only [hscaleSq]
    have h2t : 2 * t = scale ^ 2 * 1 := by
      linarith only [hscaleSq]
    rw [h2t, ht]
    simp only [zero_add, mul_one]
    exact and_congr
      (mul_lt_mul_iff_of_pos_left hs2 :
        (scale ^ 2 * (1 / 2) < scale ^ 2 * z.2) ↔ 1 / 2 < z.2)
      (by simpa only [mul_one] using
        (mul_lt_mul_iff_of_pos_left hs2 :
          (scale ^ 2 * z.2 < scale ^ 2 * 1) ↔ z.2 < 1))
  exact and_congr hspace htime

/-- Parabolic change of variables for the target-box integral in
`eq:uc-gaussian-box`. -/
theorem uc_target_box_integral_scaling
    (x₀ x : Vec3) (scale t : ℝ) (hscale : 0 < scale)
    (hscaleSq : scale ^ 2 = 2 * t)
    (w : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x scale) (Ioo t (2 * t))) volume) :
    (∫ z in spaceTimeSet (vec3Ball (scale⁻¹ • (x - x₀)) 1)
        (Ioo (1 / 2) 1),
      vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2) =
      Real.rpow scale (-5 : ℝ) *
        ∫ z in spaceTimeSet (vec3Ball x scale) (Ioo t (2 * t)),
          vec3EuclideanNorm (w z) ^ 2 := by
  let F : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (w z) ^ 2
  have hΩ : MeasurableSet (vec3Ball x scale) := vec3Ball_measurable _ _
  have hI : MeasurableSet (Ioo t (2 * t)) := measurableSet_Ioo
  have hc := CKN.integral_comp_scaling_test scale hscale (x₀, 0)
    (Ω := vec3Ball x scale) (I := Ioo t (2 * t)) (F := F)
    hΩ hI hInt.aestronglyMeasurable
  rw [uc_target_box_preimage x₀ x scale t hscale hscaleSq] at hc
  have hpoint : scalingParabolic scale (x₀, 0) = ucScaledPoint x₀ scale := by
    funext z
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  rw [hpoint] at hc
  have hcoef : (ENNReal.ofReal (scale⁻¹ ^ 5)).toReal =
      Real.rpow scale (-5 : ℝ) := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    norm_num [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  rw [hcoef] at hc
  simpa only [F, ucScaledField, smul_eq_mul] using hc

end ESS
