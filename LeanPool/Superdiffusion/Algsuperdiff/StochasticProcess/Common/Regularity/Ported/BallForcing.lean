/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ForcingLp
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.SourceExponent

/-!
# BallForcing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Dimension-only normalization of the source term on Euclidean balls
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- A dimension-only upper bound for the harmless unit-ball normalization. -/
def smallContrastUnitBallVolumePrice (d : ℕ) : ℝ :=
  max 1 ((volume (smallContrastUnitBall d)).toReal)⁻¹

theorem smallContrastUnitBallVolumePrice_nonneg (d : ℕ) :
    0 ≤ smallContrastUnitBallVolumePrice d :=
  le_trans zero_le_one (le_max_left _ _)

theorem unitBallVolume_rpow_neg_inv_le_price
    {p : ℝ} (hp : 1 ≤ p) :
    (volume (smallContrastUnitBall d)).toReal ^ (-1 / p) ≤
      smallContrastUnitBallVolumePrice d := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hV : 0 < (volume (smallContrastUnitBall d)).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        (0 : Vec d) (by norm_num)))
  by_cases hVone : 1 ≤ (volume (smallContrastUnitBall d)).toReal
  · have hexp : -1 / p ≤ (0 : ℝ) :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le
    have hpow := Real.rpow_le_rpow_of_exponent_le hVone hexp
    rw [Real.rpow_zero] at hpow
    exact hpow.trans (le_max_left _ _)
  · have hVle : (volume (smallContrastUnitBall d)).toReal ≤ 1 := le_of_not_ge hVone
    have hexp : (-1 : ℝ) ≤ -1 / p := by
      have hinv : p⁻¹ ≤ 1 := (inv_le_one₀ hp0).2 hp
      simp only [div_eq_mul_inv]
      simpa only [neg_one_mul] using neg_le_neg hinv
    have hpow := Real.rpow_le_rpow_of_exponent_ge hV hVle hexp
    rw [Real.rpow_neg_one] at hpow
    exact hpow.trans (le_max_right _ _)

/-- Exact scaling of Euclidean-ball volume from the unit ball. -/
theorem volume_euclideanBall_toReal_eq_unit_mul_pow [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall z r)).toReal =
      (volume (smallContrastUnitBall d)).toReal * r ^ d := by
  have hunit : (volume (smallContrastUnitBall d)).toReal =
      (Algsuperdiff.Section4.Provider.ExcessDecay.Schauder.sphereMeasure d).real Set.univ *
        ((1 : ℝ) ^ d / (d : ℝ)) := by
    simpa only [smallContrastUnitBall] using
      (volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div (0 : Vec d)
        (by norm_num : (0 : ℝ) < 1))
  rw [volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div z hr, hunit]
  norm_num
  ring

/-- The local normalized `L²` source row on a ball, with all dependence on its
radius explicit and the remaining normalization depending only on `d`. -/
theorem vectorNormalizedL2On_euclideanBall_le_price_mul_rpow_mul_globalLp
    [NeZero d] {U : Set (Vec d)} (z : Vec d) {r p : ℝ} {f : Vec d → Vec d}
    (hr : 0 < r) (hp : 2 ≤ p)
    (hball : euclideanBall z r ⊆ U)
    (hf : MemVectorLpOn U p f) :
    vectorNormalizedL2On (euclideanBall z r) f ≤
      smallContrastUnitBallVolumePrice d * r ^ (-(d : ℝ) / p) *
        vectorLpSizeOn U p f := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hvol : 0 < (volume (euclideanBall z r)).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hr))
  have hbase := vectorNormalizedL2On_le_volume_rpow_mul_vectorLpSizeOn
    hp0 hp hball hvol hf
  have hV : 0 ≤ (volume (smallContrastUnitBall d)).toReal := ENNReal.toReal_nonneg
  have hr0 : 0 ≤ r := hr.le
  have hscale : (volume (euclideanBall z r)).toReal ^ (-1 / p) =
      (volume (smallContrastUnitBall d)).toReal ^ (-1 / p) *
        r ^ (-(d : ℝ) / p) := by
    rw [volume_euclideanBall_toReal_eq_unit_mul_pow z hr,
      Real.mul_rpow hV (pow_nonneg hr0 d), ← Real.rpow_natCast,
      ← Real.rpow_mul hr0]
    congr 2
    ring
  rw [hscale] at hbase
  have hprice := unitBallVolume_rpow_neg_inv_le_price (d := d)
    (show (1 : ℝ) ≤ p by linarith only [hp])
  have hrpow0 : 0 ≤ r ^ (-(d : ℝ) / p) := Real.rpow_nonneg hr0 _
  have hmul := mul_le_mul_of_nonneg_right hprice hrpow0
  calc
    vectorNormalizedL2On (euclideanBall z r) f ≤
        ((volume (smallContrastUnitBall d)).toReal ^ (-1 / p) *
          r ^ (-(d : ℝ) / p)) * vectorLpSizeOn U p f := hbase
    _ ≤ (smallContrastUnitBallVolumePrice d * r ^ (-(d : ℝ) / p)) *
          vectorLpSizeOn U p f := by
      exact mul_le_mul_of_nonneg_right hmul
        ENNReal.toReal_nonneg

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
