/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalMeanJumpAmplitudeAssembly
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalAmplitudeCrossEstimate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cross-set distance control by the Gagliardo amplitude
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem ofReal_distance_factorization
    {s : ℝ} (G : Vec d → Vec d)
    (x y : Vec d) :
    ENNReal.ofReal (euclideanDist (G x) (G y)) =
      ENNReal.ofReal
          (vecNormSq (G x - G y) /
            euclideanDist x y ^ ((d : ℝ) + 2 * s)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (euclideanDist x y ^ ((d : ℝ) + 2 * s)) ^
          (1 / 2 : ℝ) := by
  by_cases hxy : x = y
  · subst y
    simp [euclideanDist, euclideanNorm, vecNormSq, vecDot]
  · have hr : 0 < euclideanDist x y :=
      lt_of_le_of_ne (euclideanDist_nonneg x y)
        (Ne.symm ((euclideanDist_eq_zero_iff).not.mpr hxy))
    have hden : 0 < euclideanDist x y ^ ((d : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos hr _
    have hnum : 0 ≤ vecNormSq (G x - G y) := vecNormSq_nonneg _
    change ENNReal.ofReal (Real.sqrt (vecNormSq (G x - G y))) = _
    rw [Real.sqrt_eq_rpow]
    rw [← ENNReal.ofReal_rpow_of_nonneg hnum
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 2
    rw [← ENNReal.ofReal_mul (div_nonneg hnum hden.le)]
    congr 1
    exact (div_mul_cancel₀ _ hden.ne').symm

private theorem measurable_crossFactor
    {s : ℝ} {G : Vec d → Vec d} (hG : Measurable G) (x : Vec d) :
    Measurable fun y => ENNReal.ofReal
      (vecNormSq (G x - G y) /
        euclideanDist x y ^ ((d : ℝ) + 2 * s)) ^ (1 / 2 : ℝ) := by
  have hnum : Measurable fun y => vecNormSq (G x - G y) :=
    continuous_vecNormSq.measurable.comp (measurable_const.sub hG)
  have hdist : Measurable fun y => euclideanDist x y := by
    unfold euclideanDist euclideanNorm
    exact (continuous_vecNormSq.comp (continuous_const.sub continuous_id)).sqrt.measurable
  exact ((hnum.div (hdist.pow measurable_const)).ennreal_ofReal).pow_const _

private theorem measurable_distanceFactor (x : Vec d) (s : ℝ) :
    Measurable fun y =>
      ENNReal.ofReal (euclideanDist x y ^ ((d : ℝ) + 2 * s)) ^
        (1 / 2 : ℝ) := by
  have hdist : Measurable fun y => euclideanDist x y := by
    unfold euclideanDist euclideanNorm
    exact (continuous_vecNormSq.comp (continuous_const.sub continuous_id)).sqrt.measurable
  exact ((hdist.pow measurable_const).ennreal_ofReal).pow_const _

/-- On a set lying within distance `D` of `x`, the integral of field
increments is bounded by the global fractional amplitude at `x`. -/
theorem setLIntegral_fieldDistance_le_fractionalAmplitude
    {U F : Set (Vec d)} {x : Vec d} {s D : ℝ} {G : Vec d → Vec d}
    (hFmeas : MeasurableSet F) (hFsub : F ⊆ U)
    (hG : Measurable G) (hs : 0 ≤ (d : ℝ) + 2 * s)
    (hdist : ∀ y ∈ F, euclideanDist x y ≤ D) :
    (∫⁻ y in F, ENNReal.ofReal (euclideanDist (G x) (G y)) ∂volume) ≤
      fractionalGagliardoAmplitude U s G x *
        (volume F * ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s))) ^
          (1 / 2 : ℝ) := by
  let f : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal
    (vecNormSq (G x - G y) /
      euclideanDist x y ^ ((d : ℝ) + 2 * s)) ^ (1 / 2 : ℝ)
  let g : Vec d → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (euclideanDist x y ^ ((d : ℝ) + 2 * s)) ^ (1 / 2 : ℝ)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict F)
    (p := 2) (q := 2) (f := f) (g := g)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (measurable_crossFactor (s := s) hG x).aemeasurable
    (measurable_distanceFactor x s).aemeasurable
  have hf : (∫⁻ y in F, f y ^ (2 : ℝ) ∂volume) ≤
      fractionalGagliardoSquareFunction U s G x := by
    simp_rw [f, ← ENNReal.rpow_mul]
    norm_num
    exact lintegral_mono_set hFsub
  have hg : (∫⁻ y in F, g y ^ (2 : ℝ) ∂volume) ≤
      volume F * ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s)) := by
    simp_rw [g, ← ENNReal.rpow_mul]
    norm_num
    calc
      (∫⁻ y in F, ENNReal.ofReal
          (euclideanDist x y ^ ((d : ℝ) + 2 * s)) ∂volume) ≤
          ∫⁻ _y in F, ENNReal.ofReal
            (D ^ ((d : ℝ) + 2 * s)) ∂volume := by
        exact setLIntegral_mono' hFmeas fun y hy =>
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
            (euclideanDist_nonneg x y) (hdist y hy) hs)
      _ = volume F * ENNReal.ofReal
          (D ^ ((d : ℝ) + 2 * s)) := by
        rw [setLIntegral_const, mul_comm]
  calc
    (∫⁻ y in F, ENNReal.ofReal (euclideanDist (G x) (G y)) ∂volume) =
        ∫⁻ y in F, f y * g y ∂volume := by
      apply lintegral_congr
      intro y
      exact ofReal_distance_factorization G x y
    _ ≤ (∫⁻ y in F, f y ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
        (∫⁻ y in F, g y ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
      simpa only [one_div] using! hholder
    _ ≤ fractionalGagliardoSquareFunction U s G x ^ (1 / 2 : ℝ) *
        (volume F * ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s))) ^
          (1 / 2 : ℝ) :=
      mul_le_mul (ENNReal.rpow_le_rpow hf (by norm_num))
        (ENNReal.rpow_le_rpow hg (by norm_num)) bot_le bot_le
    _ = _ := rfl

end

end HighContrast
end HCPolySupport
