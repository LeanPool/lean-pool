/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CommonQuantitativeAffineScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.QuantitativeCorrectorThreshold
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedOuterSpatialResponsePowerTail
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderCertificateInhabitation

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRateBearingCommonAffineGoodScaleEvent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rate-bearing root event at the printed fractional order

This is the order-31 event surface with the response order selected from the
already fixed `g`.  Its scale, deterministic length, tail, and common-scale
bookkeeping are unchanged.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

/-- The root-facing rate certificate with its order selected after `g`. -/
@[expose]
def PrintOrderRateBearingCommonAffineGoodScale
    (d : ℕ) [NeZero d] (g c kappaRate : ℝ) (abar : Mat d)
    (a : CoeffSpace d) (x : ℝ) : Prop :=
  ∃ (sourceAmplitude : ℝ) (X : CoeffSpace d → ℝ),
    PrintOrderQuantitativeNormalizedReferenceCertificate
        abar g sourceAmplitude kappaRate (X a) a ∧
      x = commonQuantitativeAffineScale sourceAmplitude
        (correctorTargetAmplitude c kappaRate) kappaRate
        (Transport.roundedOuterResponseAffineConstant d)
        (specBound (symmPart abar) * specBound (symmPart abar)⁻¹)
        kappaRate X a

end

end HighContrast
end HCPolySupport
