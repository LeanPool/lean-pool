/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianRescaling
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Returning from the Gaussian rescaling

The normalized space-time box maps onto the physical averaging box in
`lem:bu-gaussian` with parabolic Jacobian `scale⁻⁵`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- The original field expressed in the translated Gaussian coordinates. -/
@[expose] def buGaussianAverageScaledField (x : Vec3) (scale σ : ℝ)
    (w : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => w (buGaussianScaledPoint x scale σ z)

/-- The normalized Gaussian box integral changes variables to its physical
space-time average (`lem:bu-gaussian#change-back`). -/
theorem buGaussian_change_back_integral
    (x : Vec3) (scale : ℝ) (hscale : 0 < scale)
    (w : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x scale)
        (Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6))) volume) :
    (∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (1 / 2) 1),
      vec3EuclideanNorm (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2) =
      (scale ^ 5)⁻¹ *
        ∫ z in spaceTimeSet (vec3Ball x scale)
          (Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6)),
          vec3EuclideanNorm (w z) ^ 2 := by
  let Ω : Set Vec3 := vec3Ball x scale
  let I : Set ℝ := Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6)
  let shift : ℝ := -(scale ^ 2 / 6)
  let F : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (w z) ^ 2
  have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hΩ : MeasurableSet Ω := vec3Ball_measurable x scale
  have hI : MeasurableSet I := measurableSet_Ioo
  have hF : AEStronglyMeasurable F (volume.restrict (spaceTimeSet Ω I)) := by
    exact hInt.aestronglyMeasurable
  have hspace : rescaledSpace scale x Ω = vec3Ball 0 1 := by
    ext y
    change vec3EuclideanNorm (x + scale • y - x) < scale ↔
      vec3EuclideanNorm (y - 0) < 1
    rw [add_sub_cancel_left, vec3EuclideanNorm_smul, abs_of_pos hscale, sub_zero]
    constructor
    · intro hy
      have hm : scale * vec3EuclideanNorm y < scale * 1 := by
        simpa only [mul_one] using hy
      exact (mul_lt_mul_iff_of_pos_left hscale).mp hm
    · intro hy
      have hm := mul_lt_mul_of_pos_left hy hscale
      simpa only [mul_one] using hm
  have htime : rescaledTime scale shift I = Ioo (1 / 2) 1 := by
    ext s
    change shift + scale ^ 2 * s ∈ Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6) ↔
      s ∈ Ioo (1 / 2) 1
    simp only [mem_Ioo]
    constructor
    · rintro ⟨hslo, hshi⟩
      constructor
      · apply (mul_lt_mul_iff_of_pos_left hscaleSq).mp
        dsimp [shift] at hslo
        nlinarith only [hslo]
      · apply (mul_lt_mul_iff_of_pos_left hscaleSq).mp
        dsimp [shift] at hshi
        nlinarith only [hshi]
    · rintro ⟨hslo, hshi⟩
      constructor
      · dsimp [shift]
        nlinarith only [mul_lt_mul_of_pos_left hslo hscaleSq]
      · dsimp [shift]
        nlinarith only [mul_lt_mul_of_pos_left hshi hscaleSq]
  have hpre : spaceTimeSet (rescaledSpace scale x Ω) (rescaledTime scale shift I) =
      spaceTimeSet (vec3Ball 0 1) (Ioo (1 / 2) 1) := by
    rw [hspace, htime]
  have hpoint : scalingParabolic scale (x, shift) =
      fun z => buGaussianScaledPoint x scale (1 / 6) z := by
    funext z
    change (x + scale • z.1, shift + scale ^ 2 * z.2) =
      (x + scale • z.1, scale ^ 2 * (z.2 - 1 / 6))
    dsimp [shift]
    congr 1
    ring
  have hchange := CKN.integral_comp_scaling_test scale hscale (x, shift)
    (Ω := Ω) (I := I) (F := F) hΩ hI hF
  have hcoef : (ENNReal.ofReal (scale⁻¹ ^ 5)).toReal = (scale ^ 5)⁻¹ := by
    rw [ENNReal.toReal_ofReal (by positivity), inv_pow]
  rw [hpre, hpoint, hcoef, smul_eq_mul] at hchange
  dsimp [F] at hchange
  simpa [buGaussianAverageScaledField, Ω, I] using hchange

/-- The averaging normalization and the parabolic Jacobian combine to the
absolute factor `3^(5/2)` in `lem:bu-gaussian#change-back`. -/
theorem buGaussian_change_back_factor {t : ℝ} (ht : 0 < t) :
    Real.rpow t (-(5 / 2 : ℝ)) * (Real.sqrt (3 * t)) ^ 5 =
      Real.rpow 3 (5 / 2 : ℝ) := by
  have h3t : 0 < 3 * t := by positivity
  have hsquare : Real.sqrt (3 * t) ^ 5 = Real.rpow (3 * t) (5 / 2 : ℝ) := by
    have h : Real.rpow (3 * t) (5 / 2 : ℝ) =
        Real.rpow (Real.sqrt (3 * t)) (5 : ℝ) :=
      Real.rpow_div_two_eq_sqrt (x := 3 * t) (r := (5 : ℝ)) h3t.le
    exact (Real.rpow_natCast (Real.sqrt (3 * t)) 5).symm.trans h.symm
  have hmul : Real.rpow (3 * t) (5 / 2 : ℝ) =
      Real.rpow 3 (5 / 2 : ℝ) * Real.rpow t (5 / 2 : ℝ) :=
    Real.mul_rpow (x := 3) (y := t) (z := (5 / 2 : ℝ))
      (by norm_num) ht.le
  rw [hsquare, hmul]
  have hcancel : Real.rpow t (-(5 / 2 : ℝ)) * Real.rpow t (5 / 2 : ℝ) = 1 := by
    have hneg : Real.rpow t (-(5 / 2 : ℝ)) =
        (Real.rpow t (5 / 2 : ℝ))⁻¹ := Real.rpow_neg ht.le _
    rw [hneg]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht (5 / 2 : ℝ)))
  calc
    Real.rpow t (-(5 / 2 : ℝ)) *
        (Real.rpow 3 (5 / 2 : ℝ) * Real.rpow t (5 / 2 : ℝ)) =
        Real.rpow 3 (5 / 2 : ℝ) *
          (Real.rpow t (-(5 / 2 : ℝ)) * Real.rpow t (5 / 2 : ℝ)) := by ring
    _ = Real.rpow 3 (5 / 2 : ℝ) := by rw [hcancel, mul_one]

/-- The source average is the normalized Gaussian box integral times
`3^(5/2)` (`lem:bu-gaussian#change-back`). -/
theorem buGaussian_change_back_average
    (x : Vec3) (t : ℝ) (ht : 0 < t) (w : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2))) volume) :
    Real.rpow t (-(5 / 2 : ℝ)) *
        ∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (3 * t)))
          (Ioo t (5 * t / 2)), vec3EuclideanNorm (w z) ^ 2 =
      Real.rpow 3 (5 / 2 : ℝ) *
        ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (1 / 2) 1),
          vec3EuclideanNorm
            (buGaussianAverageScaledField x (Real.sqrt (3 * t)) (1 / 6) w z) ^ 2 := by
  let scale : ℝ := Real.sqrt (3 * t)
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hscaleSq : scale ^ 2 = 3 * t := by
    dsimp [scale]
    exact Real.sq_sqrt (by positivity)
  have htimeEq : Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6) =
      Ioo t (5 * t / 2) := by
    rw [hscaleSq]
    congr 1 <;> ring
  have hInt' : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x scale)
        (Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6))) volume := by
    rw [htimeEq]
    simpa only [scale] using hInt
  have hchange := buGaussian_change_back_integral x scale hscale w hInt'
  have hphys :
      ∫ z in spaceTimeSet (vec3Ball x scale)
          (Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6)),
          vec3EuclideanNorm (w z) ^ 2 =
        scale ^ 5 *
          ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (1 / 2) 1),
            vec3EuclideanNorm (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2 := by
    have hnonzero : scale ^ 5 ≠ 0 := ne_of_gt (pow_pos hscale 5)
    rw [hchange]
    field_simp
  rw [htimeEq] at hphys
  have hphysTarget :
      ∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (3 * t)))
          (Ioo t (5 * t / 2)), vec3EuclideanNorm (w z) ^ 2 =
        scale ^ 5 *
          ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (1 / 2) 1),
            vec3EuclideanNorm (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2 := by
    simpa only [scale] using hphys
  have hfactor := buGaussian_change_back_factor ht
  calc
    _ = Real.rpow t (-(5 / 2 : ℝ)) * (scale ^ 5 *
        ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (1 / 2) 1),
          vec3EuclideanNorm (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2) := by
      rw [hphysTarget]
    _ = (Real.rpow t (-(5 / 2 : ℝ)) * scale ^ 5) *
        ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (1 / 2) 1),
          vec3EuclideanNorm (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2 := by
      ring
    _ = Real.rpow 3 (5 / 2 : ℝ) *
        ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (1 / 2) 1),
          vec3EuclideanNorm (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2 := by
      have hfactor' : Real.rpow t (-(5 / 2 : ℝ)) * scale ^ 5 =
          Real.rpow 3 (5 / 2 : ℝ) := by
        simpa only [scale] using hfactor
      rw [hfactor']

end ESS
