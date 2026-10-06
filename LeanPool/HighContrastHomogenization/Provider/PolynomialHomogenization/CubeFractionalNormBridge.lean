/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalKernelBallScaling
public import LeanPool.HighContrastHomogenization.Analytic.AffineNegSobolevNorm
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.EuclideanWspSmoothDensity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.EuclideanWspLpMembership
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.CubeFractionalNormBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fractional square norms on triadic cubes

This file identifies the normalized Euclidean fractional norms at exponent two
with the square quantities used by the high-contrast estimates.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

theorem normalizedEuclideanLpENorm_two_sq_eq_eVolumeAverage
    {d : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (fun x => euclideanNorm (F x)) (normalizedCubeMeasure Q)) :
    ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm 2 F) ^ (2 : ℕ) =
      eVolumeAverage (openCubeSet Q)
        (fun x ↦ ENNReal.ofReal (vecNormSq (F x))) := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hF]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  norm_num
  unfold eVolumeAverage normalizedCubeMeasure cubeMeasure
  rw [lintegral_smul_measure]
  simp_rw [Real.enorm_eq_ofReal (euclideanNorm_nonneg _),
    ← ENNReal.ofReal_pow (euclideanNorm_nonneg _),
    euclideanNorm_sq]
  rw [volume_openCubeSet_eq_volume_cubeSet]
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hvol : volume (cubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_cubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_cubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])
  rw [hvol, ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  simp only [div_eq_mul_inv, smul_eq_mul]
  ac_rfl

private theorem cubeEuclideanWspScalePowerWeight_two_eq_hsWeight
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder) :
    cubeEuclideanWspScalePowerWeight Q s FiniteLpExponent.two =
      volume (openCubeSet Q) ^ (-(2 * s.1) / (d : ℝ)) := by
  have hvol : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])
  rw [hvol]
  unfold cubeEuclideanWspScalePowerWeight
  norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
  rw [cubeVolume_eq_pow_scale]
  rw [ENNReal.ofReal_pow (le_of_lt (by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)))]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  field_simp

private theorem enorm_cubeEuclideanWspKernel_two_sq_eq
    {d : ℕ} (s : FractionalOrder) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    ‖cubeEuclideanWspKernel s FiniteLpExponent.two F z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal
        (vecNormSq (F z.1 - F z.2) /
          euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s.1)) := by
  rw [← ofReal_norm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 2)]
  rw [norm_cubeEuclideanWspKernel]
  norm_num
  let a : ℝ := s.1 * 2 + (d : ℝ)
  rw [show (d : ℝ) + 2 * s.1 = a by simp [a, add_comm, mul_comm]]
  rw [show -((d : ℝ) / 2) + -s.1 = -a / 2 by dsimp [a]; ring]
  rw [mul_pow, euclideanNorm_sq]
  by_cases hxy : z.1 = z.2
  · rw [hxy]
    simp [euclideanDist, vecNormSq, vecDot]
  · have hdist : 0 < euclideanDist z.1 z.2 := by
      exact lt_of_le_of_ne (euclideanDist_nonneg z.1 z.2)
        (Ne.symm ((euclideanDist_eq_zero_iff).not.mpr hxy))
    have hpower :
        (euclideanDist z.1 z.2 ^ (-a / 2)) ^ 2 =
          euclideanDist z.1 z.2 ^ (-a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hdist.le]
      congr 1
      ring
    rw [hpower, Real.rpow_neg hdist.le a, div_eq_mul_inv]
    congr 1
    exact mul_comm _ _

private theorem enorm_cubeEuclideanWspKernel_two_unfolded_sq_eq
    {d : ℕ} (s : FractionalOrder) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    ‖(euclideanDist z.1 z.2 ^ (-((d : ℝ) / 2) + -s.1)) •
        (HilbertVec.ofVec (F z.1) - HilbertVec.ofVec (F z.2))‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal
        (vecNormSq (F z.1 - F z.2) /
          euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s.1)) := by
  rw [← ENNReal.rpow_natCast]
  simpa only [cubeEuclideanWspKernel_apply,
    FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat, map_sub,
    neg_add_rev, add_comm, HilbertVec.ofVec, WithLp.toLp_sub,
    Nat.cast_ofNat] using
      enorm_cubeEuclideanWspKernel_two_sq_eq s F z

theorem cubeEuclideanWspESeminorm_two_sq_eq_fracSeminormSq
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (F : Vec d → Vec d)
    (hFmeas : AEStronglyMeasurable F
      (volume.restrict (openCubeSet Q))) :
    (cubeEuclideanWspESeminorm Q s FiniteLpExponent.two F) ^ (2 : ℕ) =
      fracSeminormSq (openCubeSet Q) s.1 F := by
  have hK : AEStronglyMeasurable (cubeEuclideanWspKernel s FiniteLpExponent.two F)
      (Gagliardo.gagliardoCubeMeasure Q) := by
    have : SFinite (cubeMeasure Q) := by
      unfold cubeMeasure
      infer_instance
    have hcube : AEStronglyMeasurable F (cubeMeasure Q) := by
      simpa only [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
        using hFmeas
    have hnorm : AEStronglyMeasurable F (normalizedCubeMeasure Q) := by
      unfold normalizedCubeMeasure
      exact hcube.mono_ac Measure.smul_absolutelyContinuous
    have hfst := hnorm.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (ν := cubeMeasure Q))
    have hsnd := hcube.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := normalizedCubeMeasure Q))
    have hdist : Measurable fun z : Vec d × Vec d => euclideanDist z.1 z.2 := by
      simp only [euclideanDist_eq_norm_sub_ofVec]
      exact (((HilbertVec.ofVecL d).continuous.comp continuous_fst).sub
        ((HilbertVec.ofVecL d).continuous.comp continuous_snd)).norm.measurable
    exact (hdist.pow measurable_const).aestronglyMeasurable.smul
      ((HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable (hfst.sub hsnd))
  unfold cubeEuclideanWspESeminorm
  norm_num only [FiniteLpExponent.two_exponent]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hK]
  norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  change (∫⁻ z : Vec d × Vec d,
      ‖(euclideanDist z.1 z.2 ^ (-((d : ℝ) / 2) + -s.1)) •
        (HilbertVec.ofVec (F z.1) - HilbertVec.ofVec (F z.2))‖ₑ ^ (2 : ℕ)
      ∂Gagliardo.gagliardoCubeMeasure Q) =
    fracSeminormSq (openCubeSet Q) s.1 F
  simp_rw [enorm_cubeEuclideanWspKernel_two_unfolded_sq_eq]
  let μ : Measure (Vec d) := volume.restrict (cubeSet Q)
  let K : Vec d × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal
    (vecNormSq (F z.1 - F z.2) /
      euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s.1))
  have hFcube : AEStronglyMeasurable F μ := by
    simpa only [μ, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hFmeas
  have hfst : AEStronglyMeasurable (fun z : Vec d × Vec d => F z.1)
      (μ.prod μ) :=
    hFcube.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun z : Vec d × Vec d => F z.2)
      (μ.prod μ) :=
    hFcube.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hnum : AEMeasurable (fun z : Vec d × Vec d =>
      vecNormSq (F z.1 - F z.2)) (μ.prod μ) :=
    (continuous_vecNormSq.measurable.comp_aemeasurable
      (hfst.sub hsnd).aemeasurable)
  have hdist : Continuous (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2) := by
    unfold euclideanDist euclideanNorm
    exact (continuous_vecNormSq.comp (continuous_fst.sub continuous_snd)).sqrt
  have hden : Measurable (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s.1)) := by
    exact hdist.measurable.pow measurable_const
  have hK : AEMeasurable K (μ.prod μ) := by
    exact (hnum.div hden.aemeasurable).ennreal_ofReal
  unfold fracSeminormSq eVolumeAverage Gagliardo.gagliardoCubeMeasure
    normalizedCubeMeasure cubeMeasure
  rw [Measure.prod_smul_left, lintegral_smul_measure]
  change ENNReal.ofReal (cubeVolume Q)⁻¹ • ∫⁻ z, K z ∂(μ.prod μ) = _
  rw [lintegral_prod K hK]
  rw [show μ = volume.restrict (openCubeSet Q) by
    simp only [μ, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]]
  simp only [K, euclideanDist, euclideanNorm]
  have hvol : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    exact (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).1 (by
        rw [volume_openCubeSet_toReal,
          ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])
  rw [hvol, ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  simp only [div_eq_mul_inv, smul_eq_mul]
  ac_rfl

theorem cubeEuclideanWspFullENorm_two_sq_eq_hsNormSq
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (s : FractionalOrder) (F : Vec d → Vec d)
    (hFmeas : AEStronglyMeasurable F
      (volume.restrict (openCubeSet Q))) :
    (cubeEuclideanWspFullENorm Q s FiniteLpExponent.two F) ^ (2 : ℝ) =
      hsNormSq (openCubeSet Q) s.1 F := by
  unfold cubeEuclideanWspFullENorm hsNormSq
  norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_mul]
  norm_num
  apply congrArg₂ (fun a b : ℝ≥0∞ => a + b)
  · have hnorm : AEStronglyMeasurable F (normalizedCubeMeasure Q) := by
      unfold normalizedCubeMeasure cubeMeasure
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
      exact hFmeas.mono_ac Measure.smul_absolutelyContinuous
    have hnormF : AEStronglyMeasurable (fun x => euclideanNorm (F x))
        (normalizedCubeMeasure Q) := by
      have hcont : Continuous (fun v : Vec d => euclideanNorm v) := by
        simp_rw [euclideanNorm_eq_norm_ofVec]
        exact (PiLp.continuous_toLp 2 fun _ : Fin d => ℝ).norm
      exact hcont.comp_aestronglyMeasurable hnorm
    rw [normalizedEuclideanLpENorm_two_sq_eq_eVolumeAverage Q F hnormF]
    rw [cubeEuclideanWspScalePowerWeight_two_eq_hsWeight]
  · rw [cubeEuclideanWspESeminorm_two_sq_eq_fracSeminormSq Q s F hFmeas]


end

end HighContrast
end HCPolySupport
