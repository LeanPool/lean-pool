/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSupportHeight
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPointwiseIndicator

/-!
# Integrated squared cutoff error

The pointwise phase and shell error split passes through the compact
support integral with the shifted Carleman weight.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- The squared cutoff error is dominated by its integrated phase,
shell, and lower-time majorant. -/
theorem bu_short_weighted_error_integral_le_split
    (scale R ε c₁ C₁ C₂ a : ℝ)
    (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 1 ≤ R) (hε : 0 < ε) (hc₁ : 0 ≤ c₁)
    (hC₁ : 0 ≤ C₁)
    (hN : ∀ scale y : ℝ,
      |deriv (deriv (buShortNormalCutoff scale)) y| ≤ C₁)
    (hC₂ : 0 ≤ C₂)
    (hP : ∀ x : ℝ,
      |deriv (deriv smoothTransitionProfile) x| ≤ C₂)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hleft : IntegrableOn (fun z =>
      buShortShiftedWeight scale a z *
        buShortCutoffHeatErrorSize scale R (by linarith only [hR])
          ε c₁ v Dv z ^ 2)
      (buCutSupportSet
        (buShortFullCutoff scale R (by linarith only [hR]) ε)) volume)
    (hright : IntegrableOn (fun z =>
      4 * buShortShiftedWeight scale a z *
        (if z ∈ buShortWideGapRegion scale then
          buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
            (1 + z.1 2) ^ 4
        else buShortShellCoeff scale R c₁ ^ 2) *
        (vec3EuclideanNorm (v z) ^ 2 +
          spatialGradientSq v Dv z) +
      2 * buShortShiftedWeight scale a z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2)
      (buCutSupportSet
        (buShortFullCutoff scale R (by linarith only [hR]) ε)) volume) :
    (∫ z in buCutSupportSet
        (buShortFullCutoff scale R (by linarith only [hR]) ε),
      buShortShiftedWeight scale a z *
        buShortCutoffHeatErrorSize scale R (by linarith only [hR])
          ε c₁ v Dv z ^ 2
      ∂(volume : Measure ParabolicPoint)) ≤
    (∫ z in buCutSupportSet
        (buShortFullCutoff scale R (by linarith only [hR]) ε),
      4 * buShortShiftedWeight scale a z *
        (if z ∈ buShortWideGapRegion scale then
          buShortUniformErrorCoeff scale c₁ C₁ C₂ ^ 2 *
            (1 + z.1 2) ^ 4
        else buShortShellCoeff scale R c₁ ^ 2) *
        (vec3EuclideanNorm (v z) ^ 2 +
          spatialGradientSq v Dv z) +
      2 * buShortShiftedWeight scale a z *
        (if 1 / 2 + ε ≤ z.2 ∧ z.2 ≤ 1 / 2 + 2 * ε then
          8 / ε * vec3EuclideanNorm (v z) else 0) ^ 2
      ∂(volume : Measure ParabolicPoint)) := by
  let K := buCutSupportSet
    (buShortFullCutoff scale R (by linarith only [hR]) ε)
  have hR0 : 0 < R := by linarith only [hR]
  have hKcompact : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε
      hscale hscale1 hR0 hε).1
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  apply setIntegral_mono_on hleft hright hKmeas
  intro z hz
  have hstrip := buShortCutSupport_subset_highStrip
    scale R ε hscale hscale1 hR0 hε hz
  have hs : 1 / 2 < z.2 := hstrip.2.1
  have hs1 : z.2 < 1 := hstrip.2.2
  have hsquare := buShortCutoffHeatErrorSize_sq_pointwise_indicator
    hscale hscale1 hR hε hc₁ hC₁ hN hC₂ hP v Dv hs hs1
  have hW : 0 ≤ buShortShiftedWeight scale a z := by
    dsimp [buShortShiftedWeight, buShortCarlemanWeight]
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsquare hW
  convert hmul using 1
  ring

end ESS
