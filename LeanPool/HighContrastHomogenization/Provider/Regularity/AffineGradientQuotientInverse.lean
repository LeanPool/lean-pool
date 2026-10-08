/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineGradientQuotientPullback

/-!
# High-contrast homogenization: Provider.Regularity.AffineGradientQuotientInverse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Inverse law for affine gradient quotient pullback

The quotient transport is inverted on the same fixed source and target
domains by the inverse coordinate matrix and inverse value action.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- If `V` is the inverse-image of `U` under `L`, then `U` is the inverse-image
of `V` under `L⁻¹`. -/
theorem affinePullbackDomain_inverse {L : Mat d} (hL : IsUnit L.det)
    {U V : Set (Vec d)} (hV : V = matImage L⁻¹ U) :
    U = matImage (L⁻¹)⁻¹ V := by
  rw [hV, Matrix.nonsing_inv_nonsing_inv L hL, matImage_matImage_inv hL]

/-- Push a gradient quotient from the affine inverse-image domain back to the
original domain. -/
@[expose]
noncomputable def affineGradientQuotientPushforward {L : Mat d}
    (hL : IsUnit L.det) {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : V = matImage L⁻¹ U) (A : Mat d) :
    HilbertVectorL2 V → HilbertVectorL2 U :=
  affineGradientQuotientPullback
    (Matrix.isUnit_nonsing_inv_det L hL)
    (by rw [hV]; exact measurableSet_affinePullback hL hU)
    (affinePullbackDomain_inverse hL hV) A

/-- The quotient pushforward has the literal inverse-coordinate
representative almost everywhere on the original domain. -/
theorem coeFn_affineGradientQuotientPushforward {L : Mat d}
    (hL : IsUnit L.det) {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : V = matImage L⁻¹ U) (A : Mat d) (F : HilbertVectorL2 V) :
    affineGradientQuotientPushforward hL hU hV A F
      =ᵐ[volumeMeasureOn U]
      fun x ↦ HilbertVec.ofVec
        (matVecMul A ((F (matVecMul L⁻¹ x)).toVec)) := by
  exact coeFn_affineGradientQuotientPullback
    (Matrix.isUnit_nonsing_inv_det L hL)
    (by rw [hV]; exact measurableSet_affinePullback hL hU)
    (affinePullbackDomain_inverse hL hV) A F

end

end HighContrast
end HCPolySupport
