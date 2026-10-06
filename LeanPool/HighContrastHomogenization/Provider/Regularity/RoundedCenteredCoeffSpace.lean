/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffinePullbackCoeffSpace
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineFields

/-!
# High-contrast homogenization: Provider.Regularity.RoundedCenteredCoeffSpace

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded centered qualitative coefficient sample

The skew-centered and exactly normalized coefficient is pulled back through
the base rounded grid and packaged on the existing `CoeffSpace` carrier.  The
characterization theorem identifies its representative with the rounded
coefficient field used by the affine response transfer.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The normalized centered coefficient has its literal pointwise
representative almost everywhere. -/
theorem normalizedCenteredCoeff_ae [NeZero d]
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) :
    (⇑(normalizedCenteredCoeff a abar hS).1 : CoeffField d) =ᵐ[volume]
      fun x ↦ specBound ((symmPart abar)⁻¹) •
        ((a.1 x : Mat d) - skewPart abar) := by
  have hscale := CoeffSpace.positiveScale_ae
    (specBound ((symmPart abar)⁻¹)) (normalizedRootScale_pos hS)
    (a.subSkew (skewPart abar) (matTranspose_skewPart abar))
  have hskew := CoeffSpace.subSkew_ae a (skewPart abar)
    (matTranspose_skewPart abar)
  filter_upwards [hscale, hskew] with x hxscale hxskew
  unfold normalizedCenteredCoeff
  rw [hxscale, hxskew]

/-- The qualitative coefficient sample in the source's rounded centered
coordinates. -/
@[expose]
noncomputable def roundedCenteredCoeffSpace [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (a : CoeffSpace d) : CoeffSpace d :=
  affinePullbackCoeffSpace (baseRoundedGrid (symmPart abar))
    (isUnit_det_baseRoundedGrid hS) (normalizedCenteredCoeff a abar hS)

end

end HighContrast
end HCPolySupport
