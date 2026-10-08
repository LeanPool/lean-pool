/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffinePullbackCoeffSpace

/-!
# High-contrast homogenization: Provider.Regularity.AffinePullbackCoeffSpaceEquiv

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Invertibility of the affine coefficient-space pullback

The literal divergence-form pullback is reversible on the existing
almost-everywhere coefficient quotient.  This gives the exact carrier
equivalence needed to transport families without choosing representatives.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Pulling a coefficient field back by `L` and then by `L⁻¹` returns the
original field pointwise. -/
theorem affineCoefficient_inv_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) (b : CoeffField d) (x : Vec d) :
    affineCoefficient L⁻¹ (Matrix.isUnit_nonsing_inv_det L hL)
        (affineCoefficient L hL b) x = b x := by
  rw [affineCoefficient_apply, affineCoefficient_apply,
    Matrix.nonsing_inv_nonsing_inv L hL]
  have hLT : IsUnit (matTranspose L).det := by
    simpa only [matTranspose] using Matrix.isUnit_det_transpose L hL
  have hinvT : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
    simpa only [matTranspose] using Matrix.transpose_nonsing_inv (A := L)
  rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one, hinvT,
    ← Matrix.mul_assoc L (L⁻¹ * b x) (matTranspose L)⁻¹,
    ← Matrix.mul_assoc L L⁻¹ (b x),
    Matrix.mul_assoc ((L * L⁻¹) * b x) (matTranspose L)⁻¹
      (matTranspose L),
    Matrix.nonsing_inv_mul _ hLT, Matrix.mul_one,
    Matrix.mul_nonsing_inv L hL, Matrix.one_mul]

end

end HighContrast
end HCPolySupport
