/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.LayerCakeBasic
import LeanPool.LiebThirring.Kinetic.CurryingProductBasic

/-!
# High-field mass and extended Fourier layer cake

Plancherel gives the literal strict high-frequency mass at each cutoff.

Integrating the strict threshold over real nonnegative energies gives its length.
-/

public section

open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace LiebThirring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Plancherel gives the literal strict high-frequency mass at each cutoff. -/
theorem lintegral_highFourierField (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) (hE : 0 ≤ E) :
    (∫⁻ x : Position, ‖highFourierField h E x‖ₑ ^ 2) =
      ∫⁻ ξ : Position, if E < fourierKineticMultiplier ξ then
        ‖(Lp.fourierTransformₗᵢ Position H h) ξ‖ₑ ^ 2 else 0 := by
  calc
    _ = ∫⁻ x : Position, ‖(𝓕⁻ (highFrequencyClass h E) : Lp H 2 volume) x‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [highFourierField_ae h E hE] with x hx
      rw [hx]
    _ = ‖(𝓕⁻ (highFrequencyClass h E) : Lp H 2 volume)‖ₑ ^ 2 :=
      lintegral_l2_enorm_sq _
    _ = ‖highFrequencyClass h E‖ₑ ^ 2 := by
      change ‖(Lp.fourierTransformₗᵢ Position H).symm (highFrequencyClass h E)‖ₑ ^ 2 = _
      rw [LinearIsometryEquiv.enorm_map]
    _ = ∫⁻ ξ : Position, ‖highFrequencyClass h E ξ‖ₑ ^ 2 :=
      (lintegral_l2_enorm_sq _).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [((Lp.memLp (Lp.fourierTransformₗᵢ Position H h)).indicator
        (measurableSet_lowMomentumRegion E).compl).coeFn_toLp] with ξ hξ
      change highFrequencyClass h E ξ = _ at hξ
      rw [hξ]
      by_cases hc : E < fourierKineticMultiplier ξ
      · rw [ite_eq_left hc, Set.indicator_of_mem]
        exact not_le.mpr hc
      · rw [ite_eq_right hc, Set.indicator_of_notMem, enorm_zero, zero_pow (by decide)]
        exact not_not.mpr (not_lt.mp hc)

/-- Integrating the strict threshold over real nonnegative energies gives its length. -/
theorem lintegral_cutoff_threshold (threshold : ℝ) (a : ℝ≥0∞) :
    (∫⁻ E in Ici (0 : ℝ), if E < threshold then a else 0) = ENNReal.ofReal threshold * a := by
  change (∫⁻ E in Ici (0 : ℝ), (Iio threshold).indicator (fun _ => a) E) = _
  rw [lintegral_indicator measurableSet_Iio, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.restrict_apply measurableSet_Iio]
  have hset : Iio threshold ∩ Ici (0 : ℝ) = Ico 0 threshold := by
    ext E
    simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_Ico]
    exact and_comm
  rw [hset, Real.volume_Ico, sub_zero, mul_comm]

/-- Tonelli integrates the high-field masses to the weighted outer Fourier energy. -/
theorem lintegral_highFourierField_layerCake
    (h : Lp H 2 (volume : Measure Position)) :
    (∫⁻ E in Ici (0 : ℝ), ∫⁻ x : Position, ‖highFourierField h E x‖ₑ ^ 2) =
      ∫⁻ ξ : Position, ENNReal.ofReal (fourierKineticMultiplier ξ) *
        ‖(Lp.fourierTransformₗᵢ Position H h) ξ‖ₑ ^ 2 := by
  have heq : (∫⁻ E in Ici (0 : ℝ), ∫⁻ x : Position, ‖highFourierField h E x‖ₑ ^ 2) =
      ∫⁻ E in Ici (0 : ℝ), ∫⁻ ξ : Position,
        if E < fourierKineticMultiplier ξ then
          ‖(Lp.fourierTransformₗᵢ Position H h) ξ‖ₑ ^ 2 else 0 := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with E hE
    exact lintegral_highFourierField h E hE
  rw [heq]
  have hm : Measurable (fun p : ℝ × Position =>
      if p.1 < fourierKineticMultiplier p.2 then
        ‖(Lp.fourierTransformₗᵢ Position H h) p.2‖ₑ ^ 2 else 0) := by
    apply Measurable.ite
    · exact measurableSet_lt measurable_fst
        (continuous_fourierKineticMultiplier.measurable.comp measurable_snd)
    · exact ((Lp.stronglyMeasurable _).enorm.comp measurable_snd).pow_const 2
    · exact measurable_const
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro ξ
  exact lintegral_cutoff_threshold _ _

end LiebThirring
end
