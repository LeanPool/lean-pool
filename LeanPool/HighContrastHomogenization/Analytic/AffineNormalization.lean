/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry

/-!
# High-contrast homogenization: Analytic.AffineNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalization by the homogenized symmetric geometry

After subtracting the constant homogenized skew part, conjugation by the
inverse square root of the symmetric part sends the homogenized matrix to the
identity.  The associated domain is exactly the inverse-square-root image used
to record its shape.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The affine transform by the square root of a positive matrix normalizes
the corresponding constant coefficient to the identity. -/
theorem affineCoefficient_matSqrt_symmPart_eq_one {abar : Mat d}
    (hS : (symmPart abar).PosDef) (y : Vec d) :
    affineCoefficient (matSqrt (symmPart abar)) (isUnit_det_matSqrt hS)
        (fun _ => symmPart abar) y = 1 := by
  rw [affineCoefficient_apply]
  have htranspose : matTranspose (matSqrt (symmPart abar))⁻¹ =
      matSqrt (symmPart abar)⁻¹ := by
    rw [← matSqrt_inv hS]
    exact transpose_matSqrt_inv hS
  rw [htranspose, ← matSqrt_inv hS]
  exact matSqrt_inv_conj hS

/-- Returning from adapted coordinates recovers the original domain exactly. -/
theorem matImage_matSqrt_matImage_inv {abar : Mat d}
    (hS : (symmPart abar).PosDef) (U : Set (Vec d)) :
    matImage (matSqrt (symmPart abar))
        (matImage (matSqrt (symmPart abar))⁻¹ U) = U :=
  matImage_matImage_inv (isUnit_det_matSqrt hS) U

end

end HighContrast
end HCPolySupport
