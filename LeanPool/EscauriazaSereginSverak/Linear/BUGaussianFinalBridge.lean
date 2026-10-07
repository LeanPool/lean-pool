/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianErrorAssembly
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianAverageBase
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianParameters

/-!
# Physical Gaussian average

The rescaled integral and the radial Gaussian decay give the physical
space-time average in `lem:bu-gaussian`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The physical averaging box is integrable at the chosen short time. -/
theorem buGaussian_metric_average_integrable_at_small_time
    (A : ℝ) (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hderiv : HasSpaceTimeWeakDerivs buHalfSpace (Ioo 0 1) w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint, S ⊆ buHalfCylinder →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
        ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hgrowth : ∀ z ∈ buHalfCylinder,
      vec3EuclideanNorm (w z) ≤ Real.exp (A * vec3EuclideanNorm z.1 ^ 2))
    (x : Vec3) (t : ℝ) (hx : 2 < x 2)
    (ht : 0 < t) (htsmall : t ≤ 1 / 24) :
    IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (Metric.ball x (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2))) volume := by
  have hscaleSq : Real.sqrt (3 * t) ^ 2 = 3 * t :=
    Real.sq_sqrt (by positivity)
  have hscalele : Real.sqrt (3 * t) ≤ 1 := by
    have hs : 3 * t ≤ 1 / 8 := by nlinarith only [htsmall]
    nlinarith only [hscaleSq, hs, Real.sqrt_nonneg (3 * t)]
  have htop : 5 * t / 2 < 1 := by nlinarith only [htsmall]
  exact buGaussian_metric_average_physical_integrable A w Dw D2w Dtw
    hderiv hL2 hgrowth x (Real.sqrt (3 * t)) t hx hscalele ht htop

/-- Translation of a scaled field agrees with the field in Gaussian
averaging coordinates. -/
theorem buGaussian_shifted_scaled_eq_average
    (x : Vec3) (scale σ : ℝ) (w : ParabolicPoint → Vec3) :
    buGaussianShiftedField σ (ucScaledField x scale w) =
      buGaussianAverageScaledField x scale σ w := by
  funext z
  simp only [buGaussianShiftedField, buGaussian_timeShift_point_symm_apply,
    ucScaledField, ucScaledPoint, buGaussianAverageScaledField,
    buGaussianScaledPoint]

/-- The metric-ball change of variables with the source averaging
normalization. -/
theorem buGaussian_metric_average_normalized
    (x : Vec3) (t : ℝ) (ht : 0 < t) (w : ParabolicPoint → Vec3)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (Metric.ball x (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2))) volume) :
    Real.rpow t (-(5 / 2 : ℝ)) *
        ∫ z in spaceTimeSet (Metric.ball x (Real.sqrt (3 * t)))
          (Ioo t (5 * t / 2)), vec3EuclideanNorm (w z) ^ 2 =
      Real.rpow 3 (5 / 2 : ℝ) *
        ∫ z in spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1),
          vec3EuclideanNorm
            (buGaussianShiftedField (1 / 6)
              (ucScaledField x (Real.sqrt (3 * t)) w) z) ^ 2 := by
  let scale : ℝ := Real.sqrt (3 * t)
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hscaleSq : scale ^ 2 = 3 * t := by
    dsimp [scale]
    exact Real.sq_sqrt (by positivity)
  have htimeEq : Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6) =
      Ioo t (5 * t / 2) := by
    rw [hscaleSq]
    congr 1 <;> ring_nf
  have hInt' : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (Metric.ball x scale)
        (Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6))) volume := by
    rw [htimeEq]
    simpa only [scale] using hInt
  have hchange := buGaussian_change_back_metric_average x scale hscale w hInt'
  have hphys :
      (∫ z in spaceTimeSet (Metric.ball x scale)
          (Ioo (scale ^ 2 / 3) (5 * scale ^ 2 / 6)),
          vec3EuclideanNorm (w z) ^ 2) =
        scale ^ 5 *
          ∫ z in spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1),
            vec3EuclideanNorm
              (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2 := by
    have hnonzero : scale ^ 5 ≠ 0 := ne_of_gt (pow_pos hscale 5)
    rw [hchange]
    field_simp
  rw [htimeEq] at hphys
  have hfactor := buGaussian_change_back_factor ht
  have hsource := buGaussian_shifted_scaled_eq_average x scale (1 / 6) w
  calc
    _ = Real.rpow t (-(5 / 2 : ℝ)) *
        (scale ^ 5 * ∫ z in spaceTimeSet (Metric.ball 0 1)
          (Ioo (1 / 2 : ℝ) 1),
          vec3EuclideanNorm
            (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2) := by
          rw [show scale = Real.sqrt (3 * t) by rfl, hphys]
    _ = (Real.rpow t (-(5 / 2 : ℝ)) * scale ^ 5) *
        ∫ z in spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1),
          vec3EuclideanNorm
            (buGaussianAverageScaledField x scale (1 / 6) w z) ^ 2 := by ring_nf
    _ = Real.rpow 3 (5 / 2 : ℝ) *
        ∫ z in spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1),
          vec3EuclideanNorm
            (buGaussianShiftedField (1 / 6)
              (ucScaledField x (Real.sqrt (3 * t)) w) z) ^ 2 := by
          rw [show Real.rpow t (-(5 / 2 : ℝ)) * scale ^ 5 =
            Real.rpow 3 (5 / 2 : ℝ) by simpa only [scale] using hfactor]
          rw [← hsource]

/-- The Carleman-box estimate gives the physical Gaussian average decay. -/
theorem buGaussian_physical_average_of_core
    (β H c P Ctail Ccore k₀ k₁ Cacc : ℝ)
    (x : Vec3) (t ρ a barA I : ℝ) (w : ParabolicPoint → Vec3)
    (hβ : 0 < β) (hH : 0 < H) (ht : 0 < t) (hx : 2 < x 2)
    (hρlarge : 4 < ρ)
    (hρ : ρ = (x 2 - 1) / Real.sqrt (3 * t))
    (ha : a = β * ρ ^ 2 / H)
    (hCtail : Ctail = 64 * (1 + β / (2 * H)) /
      (β / 2) ^ 2 / Real.sqrt β)
    (hCcore : Ccore = 2 * Real.exp (3 / 2) * c * P * Ctail)
    (hc : 0 ≤ c)
    (hPform : P = 192 * (k₀ ^ 2 + k₁ ^ 2 * Cacc) + 49153)
    (hCacc : 0 ≤ Cacc)
    (hInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (Metric.ball x (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2))) volume)
    (hMass : Real.exp (-(3 / 2 : ℝ)) *
      (∫ z in spaceTimeSet (Metric.ball 0 1) (Ioo (1 / 2 : ℝ) 1),
        vec3EuclideanNorm
          (buGaussianShiftedField (1 / 6)
            (ucScaledField x (Real.sqrt (3 * t)) w) z) ^ 2) ≤ I)
    (hI : I ≤ 2 * c * P *
      ((1 + a) * (1 + ρ) ^ 3 *
        (Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
          Real.exp (-2 * β * ρ ^ 2)))) :
    Real.rpow t (-(5 / 2 : ℝ)) *
      (∫ z in spaceTimeSet (Metric.ball x (Real.sqrt (3 * t)))
        (Ioo t (5 * t / 2)), vec3EuclideanNorm (w z) ^ 2) ≤
      Real.rpow 3 (5 / 2 : ℝ) * Ccore *
        Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
        Real.exp (-(β * x 2 ^ 2) / (12 * t)) := by
  have hHeight : (x 2) ^ 2 / (12 * t) ≤ ρ ^ 2 := by
    rw [hρ]
    exact buGaussian_scaled_height_lower hx ht
  have hρone : 1 ≤ ρ := (by norm_num : (1 : ℝ) ≤ 4).trans hρlarge.le
  have ha' : a = (β / H) * ρ ^ 2 := by rw [ha]; ring_nf
  have hP : 0 ≤ P := by rw [hPform]; positivity
  have hD := buGaussian_final_scalar_bound hβ hH hρone ha'
    (rfl : (Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
      Real.exp (-2 * β * ρ ^ 2)) = _)
    hCtail hCcore hHeight hMass hI hc hP (Real.exp_nonneg _)
  rw [buGaussian_metric_average_normalized x t ht w hInt]
  have hmul := mul_le_mul_of_nonneg_left hD
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (5 / 2 : ℝ)).le
  simpa only [Real.rpow_eq_pow, mul_assoc] using hmul

end ESS
