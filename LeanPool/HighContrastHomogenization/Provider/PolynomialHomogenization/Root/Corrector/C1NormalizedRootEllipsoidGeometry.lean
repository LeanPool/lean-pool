/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1EquivariantPullbackEliminator
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedEllipsoidTriadicGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedEllipsoidWeightedNormBridge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1NormalizedRootEllipsoidGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact-root geometry for the C1 consumer

The normalized-root coordinate map sends an adapted physical ellipsoid to the
Euclidean quadratic sublevel set at the same intrinsic radius.  This isolates
the geometry needed by the exact-root corrector telescope from the separately
rounded coordinate system used by the finite Lipschitz terminal.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open Set

noncomputable section

variable {d : ℕ}

/-- Pulling an adapted ellipsoid back by the exact normalized root produces
the Euclidean quadratic sublevel set at the same intrinsic radius. -/
theorem matImage_normalizedRoot_inv_ellipsoid_eq
    [NeZero d] {abar : Mat d} (hS : (symmPart abar).PosDef) (r : ℝ) :
    matImage (Selection.normalizedRoot (symmPart abar))⁻¹
        (ellipsoid abar r) =
      {y : Vec d | vecNormSq y ≤ r ^ 2} := by
  let S : Mat d := symmPart abar
  let mu : ℝ := specBound S⁻¹
  let c : ℝ := Real.sqrt mu
  let L : Mat d := Selection.normalizedRoot S
  have hmu : 0 < mu := by
    simpa only [mu, S] using normalizedRootScale_pos hS
  have hL : IsUnit L.det := by
    simpa only [L, S] using
      (Matrix.isUnit_iff_isUnit_det _).mp
        (normalizedRoot_posDef_of_posDef hS).isUnit
  rw [matImage_inv_eq_preimage hL]
  ext y
  change
    vecDot (matVecMul L y)
          (matVecMul S⁻¹ (matVecMul L y)) ≤ mu * r ^ 2 ↔
      vecNormSq y ≤ r ^ 2
  have hLform : L = c • matSqrt S := by
    simp only [L, c, mu, Selection.normalizedRoot_eq]
  rw [hLform, smul_matVecMul, matVecMul_smul,
    vecDot_smul_left, vecDot_smul_right,
    vecDot_matVecMul_inv_matSqrt hS]
  have hcSq : c * c = mu := by
    dsimp only [c]
    rw [Real.mul_self_sqrt hmu.le]
  rw [← mul_assoc, hcSq]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hmu
  · intro h
    exact mul_le_mul_of_nonneg_left h hmu.le

end

end Root
end HighContrast
end HCPolySupport
