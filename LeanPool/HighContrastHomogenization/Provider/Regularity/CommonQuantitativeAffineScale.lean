/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.QuantitativeEffectiveScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineEffectiveScale

/-!
# High-contrast homogenization: Provider.Regularity.CommonQuantitativeAffineScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The common quantitative affine effective scale

This module composes the rate-bearing quantitative enlargement with the single
rounded-affine multiplier.  Keeping this composition named
prevents either deterministic loss from being inserted a second time.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The common effective scale: first absorb the quantitative rate amplitude,
then insert the rounded-affine multiplier exactly once. -/
@[expose]
noncomputable def commonQuantitativeAffineScale
    (amplitude target kappaRate Caff overlinePi kappaCube : ℝ)
    (X : CoeffSpace d → ℝ) : CoeffSpace d → ℝ :=
  fun a ↦ roundedAffineEffectiveScale Caff overlinePi kappaCube
    (targetedQuantitativeEffectiveScale amplitude target kappaRate X a)

/-- Under a positive rate exponent, the common scale does not
decrease a nonnegative raw scale. -/
theorem le_commonQuantitativeAffineScale
    {amplitude target kappaRate Caff overlinePi kappaCube : ℝ}
    {X : CoeffSpace d → ℝ} {a : CoeffSpace d}
    (hkappaRate : 0 < kappaRate) (hX : 0 ≤ X a) :
    X a ≤ commonQuantitativeAffineScale amplitude target kappaRate Caff
      overlinePi kappaCube X a := by
  have hRate : X a ≤ targetedQuantitativeEffectiveScale
      amplitude target kappaRate X a :=
    le_powerLossRandomScale
      (one_le_amplitudeReductionFactor amplitude target) hkappaRate hX
  exact hRate.trans (le_roundedAffineEffectiveScale Caff overlinePi kappaCube
    (targetedQuantitativeEffectiveScale amplitude target kappaRate X a)
    (hX.trans hRate))

/-- A pointwise unit lower bound survives the common enlargement. -/
theorem one_le_commonQuantitativeAffineScale
    {amplitude target kappaRate Caff overlinePi kappaCube : ℝ}
    {X : CoeffSpace d → ℝ} {a : CoeffSpace d}
    (hkappaRate : 0 < kappaRate) (hX : 1 ≤ X a) :
    1 ≤ commonQuantitativeAffineScale amplitude target kappaRate Caff
      overlinePi kappaCube X a :=
  hX.trans (le_commonQuantitativeAffineScale hkappaRate
    (zero_le_one.trans hX))

end

end HighContrast
end HCPolySupport
