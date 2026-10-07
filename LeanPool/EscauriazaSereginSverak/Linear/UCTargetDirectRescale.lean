/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCTargetDirect

/-!
# Direct rescaling of the Gaussian target box

The weighted target box yields the unweighted Gaussian estimate after
parabolic change of variables.
-/

public section


open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Rescaling the target-box weighted estimate gives the Gaussian box estimate
in `lem:uc-gaussian`, with the absolute factor from the weight lower bound
kept explicit. -/
theorem uc_gaussian_target_box_direct_rescaling
    (x₀ x : Vec3) (R T t ρ scale a C₀ : ℝ)
    (ht : 0 < t) (hscale : scale = Real.sqrt (2 * t))
    (hρ : 4 ≤ ρ) (hC₀ : 0 < C₀)
    (hρdef : ρ = 2 * vec3EuclideanNorm
      ((Real.sqrt (2 / 100))⁻¹ • (x - x₀)) / scale)
    (ha : a = (1 / 100) * ρ ^ 2 /
      (2 * Real.log (gaussCarlemanTimeWeight (3 / 2))))
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (hsourceInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x scale) (Ioo t (2 * t))) volume)
    (hboxInt : IntegrableOn
      (fun z => vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2)
      (spaceTimeSet (vec3Ball (scale⁻¹ • (x - x₀)) 1)
        (Ioo (1 / 2) 1)) volume)
    (hweightedInt : IntegrableOn (fun z => ucGaussianWeight a z *
      (vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
        spatialGradientSq (ucScaledField x₀ scale w)
          (ucScaledDw x₀ scale Dw) z)) (spaceTimeSet (vec3Ball (scale⁻¹ • (x - x₀)) 1)
        (Ioo (1 / 2) 1)) volume)
    (hweighted : (∫ z in spaceTimeSet
      (vec3Ball (scale⁻¹ • (x - x₀)) 1) (Ioo (1 / 2) 1), ucGaussianWeight a z *
      (vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
        spatialGradientSq (ucScaledField x₀ scale w)
          (ucScaledDw x₀ scale Dw) z)) ≤
        C₀ * Real.exp (-(ρ ^ 2) / 100) *
          (∫ z in ucCylinder ρ,
            vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
              spatialGradientSq (ucScaledField x₀ scale w)
                (ucScaledDw x₀ scale Dw) z))
    (henergy : (∫ z in ucCylinder ρ,
      vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
        spatialGradientSq (ucScaledField x₀ scale w)
          (ucScaledDw x₀ scale Dw) z) ≤
        2 * Real.rpow scale (-5 : ℝ) * ucLocalEnergy x₀ R T w Dw) :
    (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t)))
        (Ioo t (2 * t)), vec3EuclideanNorm (w z) ^ 2) ≤
      2 * Real.exp 1 * C₀ * ucLocalEnergy x₀ R T w Dw *
        Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)) := by
  have hscalePos : 0 < scale := by rw [hscale]; positivity
  have hscaleSq : scale ^ 2 = 2 * t := by
    rw [hscale, Real.sq_sqrt (by positivity)]
  have hlog : 0 < Real.log (gaussCarlemanTimeWeight (3 / 2)) := by
    have hlo := uc_log_weight_three_half_bounds.1
    linarith only [hlo]
  have ha0 : 0 ≤ a := by
    rw [ha]
    positivity
  let center : Vec3 := scale⁻¹ • (x - x₀)
  let v := ucScaledField x₀ scale w
  let Dv := ucScaledDw x₀ scale Dw
  let B : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)
  let M : ℝ := ∫ z in B, ucGaussianWeight a z *
    (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)
  let E : ℝ := ∫ z in ucCylinder ρ,
    vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
  let N : ℝ := ucLocalEnergy x₀ R T w Dw
  let J : ℝ := ∫ z in B, vec3EuclideanNorm (v z) ^ 2
  let I : ℝ := ∫ z in spaceTimeSet (vec3Ball x scale) (Ioo t (2 * t)),
    vec3EuclideanNorm (w z) ^ 2
  have htarget : J ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) * M :=
    uc_target_box_le_weighted_box a ha0 center
      v Dv hboxInt hweightedInt
  have hinterior' : M ≤ C₀ * Real.exp (-(ρ ^ 2) / 100) * E := hweighted
  have henergy' : E ≤ 2 * Real.rpow scale (-5 : ℝ) * N := henergy
  have hchange : J = Real.rpow scale (-5 : ℝ) * I :=
    uc_target_box_integral_scaling x₀ x scale t hscalePos hscaleSq w hsourceInt
  have hcoef : scale ^ 5 * Real.rpow scale (-5 : ℝ) = 1 := by
    norm_num [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
    field_simp [ne_of_gt hscalePos]
  have hIeq : I = scale ^ 5 * J := by
    rw [hchange, ← mul_assoc, hcoef, one_mul]
  have hexp := uc_target_exponential_identity x₀ x scale t ρ
    hscalePos hscaleSq hρdef
  have hJbound : J ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
      (C₀ * Real.exp (-(ρ ^ 2) / 100) *
        (2 * Real.rpow scale (-5 : ℝ) * N)) := by
    calc
      J ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) * M := htarget
      _ ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
          (C₀ * Real.exp (-(ρ ^ 2) / 100) * E) :=
        mul_le_mul_of_nonneg_left hinterior' (Real.exp_pos _).le
      _ ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
          (C₀ * Real.exp (-(ρ ^ 2) / 100) *
            (2 * Real.rpow scale (-5 : ℝ) * N)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left henergy'
          (mul_nonneg hC₀.le (Real.exp_pos _).le)
  have hfinal : I ≤ 2 * Real.exp 1 * C₀ * N *
      Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)) := by
    rw [hIeq]
    have hmul := mul_le_mul_of_nonneg_left hJbound
      (pow_pos hscalePos 5).le
    calc
      scale ^ 5 * J ≤ scale ^ 5 *
        (Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
          (C₀ * Real.exp (-(ρ ^ 2) / 100) *
            (2 * Real.rpow scale (-5 : ℝ) * N))) := hmul
      _ = 2 * Real.exp 1 * C₀ * N *
          Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)) := by
        change scale ^ 5 *
          (Real.exp (vec3EuclideanNorm (scale⁻¹ • (x - x₀)) ^ 2 + 1) *
            (C₀ * Real.exp (-(ρ ^ 2) / 100) *
              (2 * Real.rpow scale (-5 : ℝ) * N))) = _
        calc
          _ = (scale ^ 5 * Real.rpow scale (-5 : ℝ)) *
              (Real.exp (vec3EuclideanNorm (scale⁻¹ • (x - x₀)) ^ 2 + 1) *
                Real.exp (-(ρ ^ 2) / 100)) * (2 * C₀ * N) := by ring
          _ = _ := by rw [hcoef, hexp]; ring
  simpa only [I, N, hscale] using hfinal

end ESS
