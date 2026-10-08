/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialGradientSqENorm

/-!
# Integrals under the Gaussian parabolic dilation

The affine map in `lem:uc-gaussian` carries the normalized cylinder onto
the corresponding source cylinder.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A parabolic box is the preimage of its translated, dilated box. -/
theorem uc_scaled_box_preimage
    (x₀ : Vec3) (scale r s : ℝ) (hscale : 0 < scale) :
    spaceTimeSet
      (rescaledSpace scale x₀ (vec3Ball x₀ (scale * r)))
      (rescaledTime scale 0 (Ioo 0 (scale ^ 2 * s))) =
        spaceTimeSet (vec3Ball 0 r) (Ioo 0 s) := by
  ext z
  have hscale2 : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hspace :
      z.1 ∈ rescaledSpace scale x₀ (vec3Ball x₀ (scale * r)) ↔
        z.1 ∈ vec3Ball 0 r := by
    change vec3EuclideanNorm (x₀ + scale • z.1 - x₀) < scale * r ↔
      vec3EuclideanNorm (z.1 - 0) < r
    rw [add_sub_cancel_left, vec3EuclideanNorm_smul, abs_of_pos hscale, sub_zero]
    exact (mul_lt_mul_iff_of_pos_left hscale)
  have htime :
      z.2 ∈ rescaledTime scale 0 (Ioo 0 (scale ^ 2 * s)) ↔
        z.2 ∈ Ioo 0 s := by
    simp only [rescaledTime, mem_Ioo]
    constructor
    · rintro ⟨ha, hb⟩
      change 0 < 0 + scale ^ 2 * z.2 at ha
      change 0 + scale ^ 2 * z.2 < scale ^ 2 * s at hb
      simp only [zero_add] at ha hb
      exact ⟨(mul_pos_iff_of_pos_left hscale2).mp ha,
        (mul_lt_mul_iff_of_pos_left hscale2).mp hb⟩
    · rintro ⟨ha, hb⟩
      refine ⟨?_, ?_⟩
      · change 0 < 0 + scale ^ 2 * z.2
        simpa only [zero_add] using mul_pos hscale2 ha
      · change 0 + scale ^ 2 * z.2 < scale ^ 2 * s
        simpa only [zero_add] using
          (mul_lt_mul_iff_of_pos_left hscale2).mpr hb
  exact and_congr hspace htime

/-- The normalized Gaussian cylinder is the preimage of its translated,
dilated source cylinder. -/
theorem uc_scaled_cylinder_preimage
    (x₀ : Vec3) (scale ρ : ℝ) (hscale : 0 < scale) :
    spaceTimeSet
      (rescaledSpace scale x₀ (vec3Ball x₀ (scale * ρ)))
      (rescaledTime scale 0 (Ioo 0 (scale ^ 2 * 2))) =
        ucCylinder ρ := by
  simpa only [ucCylinder] using uc_scaled_box_preimage x₀ scale ρ 2 hscale

private theorem uc_gradient_sq_integrable
    (S : Set ParabolicPoint) (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (hweak : LocallyIntegrableOn Dw S volume)
    (hL2 : (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    IntegrableOn (fun z => spatialGradientSq w Dw z) S volume := by
  have hmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => spatialGradientSq w Dw z)
      (volume.restrict S) := by
    have hcont : Continuous
        (fun v : Fin 3 → Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by
      fun_prop
    simpa only [spatialGradientSq] using
      hcont.comp_aestronglyMeasurable hweak.aestronglyMeasurable
  have hfin : (∫⁻ z in S, ENNReal.ofReal (spatialGradientSq w Dw z)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in S, 9 * ‖Dw z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (fun z => CKN.ofReal_spatialGradientSq_le_nine_mul w Dw z)
      _ = 9 * ∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const_mul' 9 _ (by norm_num)]
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hL2
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas
    (Filter.Eventually.of_forall (fun z => by
      dsimp [spatialGradientSq]
      positivity))).mp hfin.ne

/-- The normalized cylinder energy is controlled by the source energy after
parabolic dilation (`lem:uc-gaussian`). -/
theorem uc_gaussian_energy_rescaling
    (R T scale ρ : ℝ) (hR : 0 < R) (hT : 0 < T) (hscale : 0 < scale)
    (hball : scale * ρ ≤ 3 * R / 4)
    (htime : 2 * scale ^ 2 ≤ 3 * T / 4)
    (x₀ : Vec3) (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball x₀ R) (Ioo 0 T)
      w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    (∫ z in ucCylinder ρ,
      vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
        spatialGradientSq (ucScaledField x₀ scale w)
          (ucScaledDw x₀ scale Dw) z) ≤
      2 * Real.rpow scale (-5 : ℝ) * ucLocalEnergy x₀ R T w Dw := by
  let S := spaceTimeSet (vec3Ball x₀ R) (Ioo 0 T)
  let B := spaceTimeSet (vec3Ball x₀ (3 * R / 4)) (Ioo 0 (3 * T / 4))
  let Q := spaceTimeSet (vec3Ball x₀ (scale * ρ)) (Ioo 0 (scale ^ 2 * 2))
  let G := fun z : ParabolicPoint =>
    vec3EuclideanNorm (w z) ^ 2 + scale ^ 2 * spatialGradientSq w Dw z
  let E := fun z : ParabolicPoint =>
    vec3EuclideanNorm (w z) ^ 2 + T * spatialGradientSq w Dw z
  have hL2w : (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (fun z => le_add_of_nonneg_right (by positivity))
      _ < ⊤ := hL2
  have hL2Dw : (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono (fun z => le_add_of_nonneg_left (by positivity))
      _ < ⊤ := hL2
  have hwInt : IntegrableOn
      (fun z : ParabolicPoint => vec3EuclideanNorm (w z) ^ 2) S volume :=
    uc_squared_norm_integrable_on_subset S S w hweak.1 hL2w Subset.rfl
  have hDwInt : IntegrableOn
      (fun z : ParabolicPoint => spatialGradientSq w Dw z) S volume :=
    uc_gradient_sq_integrable S w Dw hweak.2.1 hL2Dw
  have hBsubS : B ⊆ S := by
    intro z hz
    have hR' : 3 * R / 4 ≤ R := by linarith only [hR]
    have hT' : 3 * T / 4 ≤ T := by linarith only [hT]
    exact ⟨(mem_vec3Ball).2 ((mem_vec3Ball).1 hz.1 |>.trans_le hR'),
      ⟨hz.2.1, hz.2.2.trans_le hT'⟩⟩
  have hQsubB : Q ⊆ B := by
    intro z hz
    exact ⟨(mem_vec3Ball).2 ((mem_vec3Ball).1 hz.1 |>.trans_le hball),
      ⟨hz.2.1, hz.2.2.trans_le (by simpa only [mul_comm] using htime)⟩⟩
  have hQsubS : Q ⊆ S := hQsubB.trans hBsubS
  have hGQ : IntegrableOn G Q volume :=
    (hwInt.mono_set hQsubS).add
      ((hDwInt.mono_set hQsubS).const_mul (scale ^ 2))
  have hEB : IntegrableOn E B volume :=
    (hwInt.mono_set hBsubS).add
      ((hDwInt.mono_set hBsubS).const_mul T)
  have hpoint : scalingParabolic scale (x₀, 0) = ucScaledPoint x₀ scale := by
    funext z
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  have hchange :
      (∫ z in ucCylinder ρ, G (ucScaledPoint x₀ scale z)) =
        Real.rpow scale (-5 : ℝ) * ∫ z in Q, G z := by
    have hΩ : MeasurableSet (vec3Ball x₀ (scale * ρ)) :=
      vec3Ball_measurable _ _
    have hI : MeasurableSet (Ioo 0 (scale ^ 2 * 2)) := measurableSet_Ioo
    have hc := CKN.integral_comp_scaling_test scale hscale (x₀, 0)
      (Ω := vec3Ball x₀ (scale * ρ)) (I := Ioo 0 (scale ^ 2 * 2))
      (F := G) hΩ hI hGQ.aestronglyMeasurable
    rw [uc_scaled_cylinder_preimage x₀ scale ρ hscale] at hc
    rw [hpoint] at hc
    have hcoef : (ENNReal.ofReal (scale⁻¹ ^ 5)).toReal =
        Real.rpow scale (-5 : ℝ) := by
      rw [ENNReal.toReal_ofReal (by positivity)]
      norm_num [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
    rw [hcoef] at hc
    simpa only [Q, smul_eq_mul] using hc
  have hleft :
      (∫ z in ucCylinder ρ,
        vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
          spatialGradientSq (ucScaledField x₀ scale w)
            (ucScaledDw x₀ scale Dw) z) =
        ∫ z in ucCylinder ρ, G (ucScaledPoint x₀ scale z) := by
    apply integral_congr_ae
    filter_upwards [] with z
    rw [uc_scaled_gradient_sq]
    rfl
  have hscaleT : scale ^ 2 ≤ T := by
    linarith only [htime, hT, sq_nonneg scale]
  have hGE (z : ParabolicPoint) : G z ≤ E z := by
    have hgrad : 0 ≤ spatialGradientSq w Dw z := by
      dsimp [spatialGradientSq]
      positivity
    dsimp [G, E]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hscaleT hgrad) _
  have hEpos (z : ParabolicPoint) : 0 ≤ E z := by
    have hgrad : 0 ≤ spatialGradientSq w Dw z := by
      dsimp [spatialGradientSq]
      positivity
    dsimp [E]
    positivity
  have hQmeas : MeasurableSet Q :=
    (CKN.Foundation.Parabolic.isOpen_spaceTimeSet _ _
      (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hEQ : IntegrableOn E Q volume := hEB.mono_set hQsubB
  have hmono : (∫ z in Q, G z) ≤ ∫ z in B, E z := by
    calc
      (∫ z in Q, G z) ≤ ∫ z in Q, E z :=
        setIntegral_mono_on hGQ hEQ hQmeas (fun z _ => hGE z)
      _ ≤ ∫ z in B, E z :=
        setIntegral_mono_set hEB
          (Filter.Eventually.of_forall hEpos)
          (Filter.Eventually.of_forall (fun z hz => hQsubB hz))
  have hE_nonneg : 0 ≤ ∫ z in B, E z := by
    apply integral_nonneg_of_ae
    exact Filter.Eventually.of_forall hEpos
  have hcpos : 0 ≤ Real.rpow scale (-5 : ℝ) :=
    (Real.rpow_pos_of_pos hscale _).le
  have hscaled_nonneg :
      0 ≤ Real.rpow scale (-5 : ℝ) * ∫ z in B, E z :=
    mul_nonneg hcpos hE_nonneg
  calc
    (∫ z in ucCylinder ρ,
        vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
          spatialGradientSq (ucScaledField x₀ scale w)
            (ucScaledDw x₀ scale Dw) z) =
        Real.rpow scale (-5 : ℝ) * ∫ z in Q, G z := by rw [hleft, hchange]
    _ ≤ Real.rpow scale (-5 : ℝ) * ∫ z in B, E z :=
      mul_le_mul_of_nonneg_left hmono hcpos
    _ ≤ 2 * Real.rpow scale (-5 : ℝ) * ∫ z in B, E z := by
      nlinarith only [hscaled_nonneg]
    _ = 2 * Real.rpow scale (-5 : ℝ) * ucLocalEnergy x₀ R T w Dw := by
      rfl

end ESS
