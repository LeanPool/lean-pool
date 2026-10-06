/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineMap

/-!
# High-contrast homogenization: Provider.Regularity.RoundedAffineFields

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coefficient and field identities for the rounded affine map

This is the algebraic core of the rounded affine transformation.  It transforms
the skew-centered physical coefficient, its symmetric reference, slopes, gradients, and the
centered flux defect through the same lattice-compatible base rounded grid.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The source's rounded-coordinate coefficient: first remove the homogenized
skew part and multiply by the exact scalar normalizer, then apply the rounded
divergence-form pullback. -/
@[expose]
def roundedCenteredCoefficient (abar : Mat d)
    (hS : (symmPart abar).PosDef) (a : CoeffField d) : CoeffField d :=
  affineCoefficient (baseRoundedGrid (symmPart abar))
    (isUnit_det_baseRoundedGrid hS)
    (fun x ↦ specBound ((symmPart abar)⁻¹) •
      (a x - skewPart abar))

/-- The rounded-coordinate constant symmetric reference. -/
@[expose]
def roundedSymmetricReferenceCoefficient (abar : Mat d)
    (hS : (symmPart abar).PosDef) : CoeffField d :=
  affineCoefficient (baseRoundedGrid (symmPart abar))
    (isUnit_det_baseRoundedGrid hS)
    (fun _ ↦ specBound ((symmPart abar)⁻¹) • symmPart abar)

@[simp] theorem roundedSymmetricReferenceCoefficient_apply (abar : Mat d)
    (hS : (symmPart abar).PosDef) (y : Vec d) :
    roundedSymmetricReferenceCoefficient abar hS y =
      (baseRoundedGrid (symmPart abar))⁻¹ *
        (specBound ((symmPart abar)⁻¹) • symmPart abar) *
        matTranspose (baseRoundedGrid (symmPart abar))⁻¹ := by
  rfl

end

end HighContrast
end HCPolySupport
