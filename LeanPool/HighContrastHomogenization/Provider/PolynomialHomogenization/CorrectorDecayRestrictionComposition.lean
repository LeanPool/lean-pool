/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusNegOne
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.CorrectorDecayRestrictionComposition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The restriction part of the physical corrector-decay transport

The normalized negative-one restriction estimate applies simultaneously to
the gradient and flux rows.  Its affine-ellipsoid specialization below stops
at the pulled-back ellipsoid: changing the negative-one norm itself through
the affine map is a separate analytic statement.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Restricting two local square-integrable rows costs one common square-root
volume ratio. -/
theorem negOneNorm_pair_le_sqrt_volumeRatio_of_subset
    {d : ℕ} [NeZero d] {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hV0 : volume V ≠ 0) (hVtop : volume V ≠ ∞)
    (F G : Vec d → Vec d) (hF : MemVectorL2 V F) (hG : MemVectorL2 V G) :
    negOneNorm U F + negOneNorm U G ≤
      ENNReal.ofReal
          (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
        (negOneNorm V F + negOneNorm V G) := by
  have hFrestrict := negOneNorm_le_sqrt_volumeRatio_of_subset
    hUV hU0 hUtop hV0 hVtop F hF
  have hGrestrict := negOneNorm_le_sqrt_volumeRatio_of_subset
    hUV hU0 hUtop hV0 hVtop G hG
  calc
    negOneNorm U F + negOneNorm U G ≤
        ENNReal.ofReal
            (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
          negOneNorm V F +
        ENNReal.ofReal
            (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
          negOneNorm V G := add_le_add hFrestrict hGrestrict
    _ = ENNReal.ofReal
          (Real.sqrt ((volume V).toReal / (volume U).toReal)) *
        (negOneNorm V F + negOneNorm V G) := (mul_add _ _ _).symm

end

end HighContrast
end HCPolySupport
