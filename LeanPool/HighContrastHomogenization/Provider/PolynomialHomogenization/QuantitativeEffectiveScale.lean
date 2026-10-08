/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.QuantitativeNormalizedReferenceCertificate
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PowerLossRandomScale

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.QuantitativeEffectiveScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# One effective scale for a quantitative normalized reference certificate

The rate prefactor retained by the quantitative certificate is absorbed into one
deterministic enlargement of the random source scale.  The resulting scale is
measurable, is no smaller than the source scale, and carries the same family,
order, and decay exponent with unit amplitude.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The deterministic prefactor needed to reduce a retained amplitude to a
positive target amplitude. -/
@[expose]
noncomputable def amplitudeReductionFactor (amplitude target : ℝ) : ℝ :=
  max 1 (amplitude / target)

/-- One law-level enlargement that reduces the retained pointwise amplitude
to a prescribed positive target. -/
@[expose]
noncomputable def targetedQuantitativeEffectiveScale
    (amplitude target kappa : ℝ) (X : CoeffSpace d → ℝ) :
    CoeffSpace d → ℝ :=
  _root_.HCPolySupport.HighContrast.powerLossRandomScale
    (amplitudeReductionFactor amplitude target) kappa X

theorem one_le_amplitudeReductionFactor (amplitude target : ℝ) :
    1 ≤ amplitudeReductionFactor amplitude target :=
  le_max_left _ _

theorem amplitude_le_target_mul_amplitudeReductionFactor
    {amplitude target : ℝ} (hTarget : 0 < target) :
    amplitude ≤ target * amplitudeReductionFactor amplitude target := by
  have hratio : amplitude / target ≤
      amplitudeReductionFactor amplitude target := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hratio hTarget.le
  rwa [mul_div_cancel₀ amplitude hTarget.ne'] at hmul

/-- A quantitative certificate can be rebased once to any positive target
amplitude, without changing its family, order, or decay exponent. -/
theorem QuantitativeNormalizedReferenceCertificate.targetedEffectiveScale
    [NeZero d] {abar : Mat d} {s amplitude target kappa : ℝ}
    {X : CoeffSpace d → ℝ} {a : CoeffSpace d}
    (h : QuantitativeNormalizedReferenceCertificate
      abar s amplitude kappa (X a) a)
    (hTarget : 0 < target) :
    QuantitativeNormalizedReferenceCertificate abar s target kappa
      (targetedQuantitativeEffectiveScale amplitude target kappa X a) a := by
  obtain ⟨hS, aRef, hs, hsLt, _,
    hKappa, hX, haRef, htail⟩ := h
  let A : ℝ := amplitudeReductionFactor amplitude target
  have hAOne : 1 ≤ A := one_le_amplitudeReductionFactor amplitude target
  have hAPos : 0 < A := zero_lt_one.trans_le hAOne
  have hXPos : 0 < X a := zero_lt_one.trans_le hX
  have hEffOne : 1 ≤ targetedQuantitativeEffectiveScale
      amplitude target kappa X a :=
    one_le_powerLossRandomScale hAOne hKappa hX
  refine ⟨hS, aRef, hs, hsLt, hTarget.le, hKappa,
    hEffOne, haRef, ?_⟩
  intro k hEffK
  have hXEff : X a ≤ targetedQuantitativeEffectiveScale
      amplitude target kappa X a :=
    le_powerLossRandomScale hAOne hKappa (zero_le_one.trans hX)
  have hXK : X a ≤ (3 : ℝ) ^ k := hXEff.trans hEffK
  have hPow : 0 < (3 : ℝ) ^ k := by positivity
  have hRatioNonneg : 0 ≤ (((3 : ℝ) ^ k) / X a) ^ (-kappa) :=
    Real.rpow_nonneg (div_nonneg hPow.le hXPos.le) _
  have hAmplitude : amplitude ≤ target * A :=
    amplitude_le_target_mul_amplitudeReductionFactor hTarget
  have hAbsorb :
      A * (((3 : ℝ) ^ k) / X a) ^ (-kappa) =
        (((3 : ℝ) ^ k) /
          targetedQuantitativeEffectiveScale amplitude target kappa X a) ^
            (-kappa) := by
    exact prefactor_mul_rpow_ratio_eq_rpow_powerLossRandomScale
      hAPos hKappa hXPos hPow
  calc
    scalarIdentityWeakError aRef s k ≤
        amplitude * (((3 : ℝ) ^ k) / X a) ^ (-kappa) := htail k hXK
    _ ≤ (target * A) * (((3 : ℝ) ^ k) / X a) ^ (-kappa) :=
      mul_le_mul_of_nonneg_right hAmplitude hRatioNonneg
    _ = target *
        (A * (((3 : ℝ) ^ k) / X a) ^ (-kappa)) := by ring
    _ = target * (((3 : ℝ) ^ k) /
          targetedQuantitativeEffectiveScale amplitude target kappa X a) ^
            (-kappa) := by rw [hAbsorb]

/-- Absorbing the retained amplitude into the source scale preserves the
quantitative certificate and normalizes its pointwise prefactor to one. -/
theorem QuantitativeNormalizedReferenceCertificate.powerLossRandomScale
    [NeZero d] {abar : Mat d} {s amplitude kappa : ℝ}
    {X : CoeffSpace d → ℝ} {a : CoeffSpace d}
    (h : QuantitativeNormalizedReferenceCertificate
      abar s amplitude kappa (X a) a)
    (hAmplitude : 1 ≤ amplitude) :
    QuantitativeNormalizedReferenceCertificate abar s 1 kappa
      (_root_.HCPolySupport.HighContrast.powerLossRandomScale
        amplitude kappa X a) a := by
  obtain ⟨hS, aRef, hs, hsLt, _,
    hKappa, hX, haRef, htail⟩ := h
  have hAmplitudePos : 0 < amplitude := zero_lt_one.trans_le hAmplitude
  have hXPos : 0 < X a := zero_lt_one.trans_le hX
  have hEffOne : 1 ≤
      _root_.HCPolySupport.HighContrast.powerLossRandomScale
        amplitude kappa X a :=
    one_le_powerLossRandomScale hAmplitude hKappa hX
  refine ⟨hS, aRef, hs, hsLt, zero_le_one, hKappa,
    hEffOne, haRef, ?_⟩
  intro k hEffK
  have hXEff : X a ≤
      _root_.HCPolySupport.HighContrast.powerLossRandomScale
        amplitude kappa X a :=
    le_powerLossRandomScale hAmplitude hKappa (zero_le_one.trans hX)
  have hXK : X a ≤ (3 : ℝ) ^ k := hXEff.trans hEffK
  have hPow : 0 < (3 : ℝ) ^ k := by positivity
  calc
    scalarIdentityWeakError aRef s k ≤
        amplitude * (((3 : ℝ) ^ k) / X a) ^ (-kappa) := htail k hXK
    _ = (((3 : ℝ) ^ k) /
          _root_.HCPolySupport.HighContrast.powerLossRandomScale
            amplitude kappa X a) ^ (-kappa) :=
      prefactor_mul_rpow_ratio_eq_rpow_powerLossRandomScale
        hAmplitudePos hKappa hXPos hPow
    _ = 1 * (((3 : ℝ) ^ k) /
          _root_.HCPolySupport.HighContrast.powerLossRandomScale
            amplitude kappa X a) ^ (-kappa) := by
      rw [one_mul]

end

end HighContrast
end HCPolySupport
