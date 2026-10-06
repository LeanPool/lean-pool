/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortFixedCylinder

/-!
# Support of the lower-time derivative term

The singular coefficient in the cutoff heat error is confined to the
time interval in which the lower-time cutoff changes.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The lower-time derivative is supported in its closed transition
strip. -/
theorem buShortTimeCutoff_abs_deriv_le_indicator
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    |deriv (buShortTimeCutoff ε) s| ≤
      if 1 / 2 + ε ≤ s ∧ s ≤ 1 / 2 + 2 * ε then 8 / ε else 0 := by
  by_cases hstrip : 1 / 2 + ε ≤ s ∧ s ≤ 1 / 2 + 2 * ε
  · simpa only [ite_eq_left hstrip] using buShortTimeCutoff_abs_deriv_le hε s
  · rw [ite_eq_right hstrip]
    by_cases hbefore : s < 1 / 2 + ε
    · rw [buShortTimeCutoff_deriv_eq_zero_early hε hbefore]
      simp
    · have hafter : 1 / 2 + 2 * ε < s := by
        have hfirst : 1 / 2 + ε ≤ s := le_of_not_gt hbefore
        by_contra hnot
        exact hstrip ⟨hfirst, le_of_not_gt hnot⟩
      rw [buShortTimeCutoff_deriv_eq_zero_late hε hafter]
      simp

/-- The scalar heat derivative contains only one term supported on the
initial-time transition strip. -/
theorem buShortCutoffHeatScalarSize_le_spacePhase_indicator
    (scale R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (z : ParabolicPoint) :
    |timePartial (buCutScalar (buShortFullCutoff scale R hR ε)) z +
      ∑ j : Fin 3,
        spatialSecondPartial (buCutScalar (buShortFullCutoff scale R hR ε))
          j j z| ≤
      buShortSpacePhaseHeatSize scale R hR z +
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then 8 / ε else 0) := by
  let ψ := buShortSpacePhaseCutoff scale R hR
  let θ := buShortTimeCutoff ε
  have hθ := ucInitialTimeCutoff_bounds ε (z.2 - 1 / 2)
  have hθ0 : 0 ≤ θ z.2 := hθ.1
  have hθ1 : θ z.2 ≤ 1 := hθ.2
  have hψ := buShortSpacePhaseCutoff_bounds scale R hR (z.1, z.2)
  have hψ0 : 0 ≤ ψ (z.1, z.2) := hψ.1
  have hψ1 : ψ (z.1, z.2) ≤ 1 := hψ.2
  have hderiv := buShortTimeCutoff_abs_deriv_le_indicator hε z.2
  have hformula :
      timePartial (buCutScalar (buShortFullCutoff scale R hR ε)) z +
        ∑ j : Fin 3,
          spatialSecondPartial
            (buCutScalar (buShortFullCutoff scale R hR ε)) j j z =
      (timePartial (buCutScalar ψ) z +
        ∑ j : Fin 3, spatialSecondPartial (buCutScalar ψ) j j z) * θ z.2 +
        ψ (z.1, z.2) * deriv θ z.2 := by
    rw [buShortFullCutoff_timePartial_time_factor]
    simp_rw [buShortFullCutoff_spatialSecondPartial_time_factor]
    rw [← Finset.sum_mul]
    ring
  rw [hformula]
  calc
    _ ≤ |(timePartial (buCutScalar ψ) z +
          ∑ j : Fin 3, spatialSecondPartial (buCutScalar ψ) j j z) * θ z.2| +
        |ψ (z.1, z.2) * deriv θ z.2| := abs_add_le _ _
    _ = buShortSpacePhaseHeatSize scale R hR z * θ z.2 +
        ψ (z.1, z.2) * |deriv θ z.2| := by
      simp only [abs_mul, abs_of_nonneg hθ0, abs_of_nonneg hψ0]
      rfl
    _ ≤ buShortSpacePhaseHeatSize scale R hR z +
          (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
            8 / ε else 0) := by
      apply add_le_add
      · exact mul_le_of_le_one_right (abs_nonneg _) hθ1
      · have hnonneg : 0 ≤
            (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
              8 / ε else 0) := by
          split_ifs <;> positivity
        exact (mul_le_mul_of_nonneg_left hderiv hψ0).trans
          (mul_le_of_le_one_left hnonneg hψ1)

/-- The singular part of the full cutoff heat error is supported only
in the initial-time transition strip. -/
theorem buShortCutoffHeatErrorSize_le_spacePhase_indicator
    (scale R ε c₁ : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (hscale : 0 ≤ scale) (hc₁ : 0 ≤ c₁)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) :
    buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ≤
      (3 * (c₁ * scale) * buShortSpacePhaseGradientSize scale R hR z +
        buShortSpacePhaseHeatSize scale R hR z) * vec3EuclideanNorm (v z) +
      18 * buShortSpacePhaseGradientSize scale R hR z *
        Real.sqrt (spatialGradientSq v Dv z) +
      (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
        8 / ε * vec3EuclideanNorm (v z) else 0) := by
  have hgrad := buShortCutoffGradientSize_le_spacePhase scale R ε hR z
  have hheat := buShortCutoffHeatScalarSize_le_spacePhase_indicator
    scale R ε hR hε z
  have hv0 := vec3EuclideanNorm_nonneg (v z)
  have hroot := Real.sqrt_nonneg (spatialGradientSq v Dv z)
  have hq : 0 ≤ 3 * (c₁ * scale) := by positivity
  have hcoef :
      3 * (c₁ * scale) * buShortCutoffGradientSize scale R hR ε z +
        |timePartial (buCutScalar (buShortFullCutoff scale R hR ε)) z +
          ∑ j : Fin 3,
            spatialSecondPartial (buCutScalar
              (buShortFullCutoff scale R hR ε)) j j z| ≤
      3 * (c₁ * scale) * buShortSpacePhaseGradientSize scale R hR z +
        (buShortSpacePhaseHeatSize scale R hR z +
          if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then 8 / ε else 0) :=
    add_le_add (mul_le_mul_of_nonneg_left hgrad hq) hheat
  have hfirst := mul_le_mul_of_nonneg_right hcoef hv0
  have hsecond := mul_le_mul_of_nonneg_left hgrad
    (show 0 ≤ 18 * Real.sqrt (spatialGradientSq v Dv z) by positivity)
  dsimp [buShortCutoffHeatErrorSize]
  split_ifs at hfirst ⊢ <;> nlinarith only [hfirst, hsecond]

end ESS
