/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.QuantitativeEffectiveScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CommonQuantitativeAffineScale
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderQuantitativeCertificate

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderEffectiveScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Effective-scale operations for printed-order certificates

The deterministic scale operations do not inspect a small-order upper bound.
They therefore preserve the certificate whose order is selected after `g`.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- Reducing the retained amplitude to a positive target preserves the
printed response order and decay exponent. -/
theorem PrintOrderQuantitativeNormalizedReferenceCertificate.targetedEffectiveScale
    [NeZero d] {abar : Mat d} {g amplitude target kappa : ℝ}
    {X : CoeffSpace d → ℝ} {a : CoeffSpace d}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amplitude kappa (X a) a)
    (hTarget : 0 < target) :
    PrintOrderQuantitativeNormalizedReferenceCertificate abar g target kappa
      (targetedQuantitativeEffectiveScale amplitude target kappa X a) a := by
  obtain ⟨hS, aRef, hs, hsHalf, _, hKappa, hX, haRef, htail⟩ := h
  let A : ℝ := amplitudeReductionFactor amplitude target
  have hAOne : 1 ≤ A := one_le_amplitudeReductionFactor amplitude target
  have hAPos : 0 < A := zero_lt_one.trans_le hAOne
  have hXPos : 0 < X a := zero_lt_one.trans_le hX
  have hEffOne : 1 ≤ targetedQuantitativeEffectiveScale
      amplitude target kappa X a :=
    one_le_powerLossRandomScale hAOne hKappa hX
  refine ⟨hS, aRef, hs, hsHalf, hTarget.le, hKappa,
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
            (-kappa) :=
    prefactor_mul_rpow_ratio_eq_rpow_powerLossRandomScale
      hAPos hKappa hXPos hPow
  calc
    scalarIdentityWeakError aRef (printCertificateOrder g) k ≤
        amplitude * (((3 : ℝ) ^ k) / X a) ^ (-kappa) := htail k hXK
    _ ≤ (target * A) * (((3 : ℝ) ^ k) / X a) ^ (-kappa) :=
      mul_le_mul_of_nonneg_right hAmplitude hRatioNonneg
    _ = target * (A * (((3 : ℝ) ^ k) / X a) ^ (-kappa)) := by ring
    _ = target * (((3 : ℝ) ^ k) /
          targetedQuantitativeEffectiveScale amplitude target kappa X a) ^
            (-kappa) := by rw [hAbsorb]

/-- Enlargement to a later positive scale preserves the same per-`g`
certificate and amplitude. -/
theorem PrintOrderQuantitativeNormalizedReferenceCertificate.enlargeScale
    [NeZero d] {abar : Mat d} {a : CoeffSpace d}
    {g x y amplitude kappa : ℝ}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amplitude kappa x a)
    (hy : 0 < y) (hxy : x ≤ y) :
    PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amplitude kappa y a := by
  obtain ⟨hS, aRef, hs, hsHalf, hAmplitude, hKappa, hx, haRef, htail⟩ := h
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  refine ⟨hS, aRef, hs, hsHalf, hAmplitude, hKappa,
    hx.trans hxy, haRef, ?_⟩
  intro k hyk
  have hxk : x ≤ (3 : ℝ) ^ k := hxy.trans hyk
  have hPow : 0 < (3 : ℝ) ^ k := by positivity
  have hRatio : (3 : ℝ) ^ k / y ≤ (3 : ℝ) ^ k / x :=
    div_le_div_of_nonneg_left hPow.le hxPos hxy
  have hDecay :
      (((3 : ℝ) ^ k) / x) ^ (-kappa) ≤
        (((3 : ℝ) ^ k) / y) ^ (-kappa) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hPow hy) hRatio
      (neg_nonpos.mpr hKappa.le)
  exact (htail k hxk).trans
    (mul_le_mul_of_nonneg_left hDecay hAmplitude)

/-- The common affine enlargement preserves a printed-order certificate. -/
theorem PrintOrderQuantitativeNormalizedReferenceCertificate.commonAffineScale
    [NeZero d] {abar : Mat d} {a : CoeffSpace d}
    {g amplitude target kappaRate Caff overlinePi kappaCube : ℝ}
    {X : CoeffSpace d → ℝ}
    (h : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amplitude kappaRate (X a) a)
    (hTarget : 0 < target) :
    PrintOrderQuantitativeNormalizedReferenceCertificate abar g target kappaRate
      (commonQuantitativeAffineScale amplitude target kappaRate Caff
        overlinePi kappaCube X a) a := by
  have hTargeted := h.targetedEffectiveScale hTarget
  have hTargetedData := hTargeted
  obtain ⟨_, _, _, _, _, _, hRateOne, _, _⟩ := hTargetedData
  have hRateNonneg : 0 ≤ targetedQuantitativeEffectiveScale
      amplitude target kappaRate X a := zero_le_one.trans hRateOne
  have hCommonPos : 0 < roundedAffineEffectiveScale Caff overlinePi kappaCube
      (targetedQuantitativeEffectiveScale amplitude target kappaRate X a) :=
    zero_lt_one.trans_le
      (one_le_roundedAffineEffectiveScale Caff overlinePi kappaCube _ hRateOne)
  have hRateCommon : targetedQuantitativeEffectiveScale
      amplitude target kappaRate X a ≤
        roundedAffineEffectiveScale Caff overlinePi kappaCube
          (targetedQuantitativeEffectiveScale amplitude target kappaRate X a) :=
    le_roundedAffineEffectiveScale Caff overlinePi kappaCube _ hRateNonneg
  simpa only [commonQuantitativeAffineScale] using
    (PrintOrderQuantitativeNormalizedReferenceCertificate.enlargeScale
      hTargeted hCommonPos hRateCommon)

end

end HighContrast
end HCPolySupport
