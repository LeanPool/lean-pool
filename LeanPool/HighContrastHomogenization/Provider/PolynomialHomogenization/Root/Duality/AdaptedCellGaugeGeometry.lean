/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry
public import LeanPool.HighContrastHomogenization.Support.Geometry.Translation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Duality.AdaptedCellGaugeGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The gauge image of an adapted-cell witness

The frozen Dirichlet domain premise exhibits `U` as an affine image of an open
triadic cube,

  `U = (fun x => z + matVecMul L x) '' S`,

with `L` the exact matrix root of the comparison matrix.  Applying the gauge
`matImage L⁻¹` returns the cube itself, translated by `matVecMul L⁻¹ z` — the
translation is by an arbitrary real vector, not by a lattice vector, so the
gauge image is a *translate* of a triadic cube and not itself one.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The gauge image of an adapted-cell witness is a translated cube.** -/
theorem matImage_inv_affineImage {L : Mat d} (hL : IsUnit L.det)
    (z : Vec d) (S : Set (Vec d)) :
    matImage L⁻¹ ((fun x => z + matVecMul L x) '' S) =
      translateSet (matVecMul L⁻¹ z) S := by
  have hkey : ∀ y : Vec d,
      matVecMul L⁻¹ (z + matVecMul L y) = y + matVecMul L⁻¹ z := by
    intro y
    rw [matVecMul_add, matVecMul_mul, Matrix.nonsing_inv_mul L hL,
      matVecMul_one]
    exact add_comm _ _
  ext p
  constructor
  · rintro ⟨q, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (hkey y).symm ▸ rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨z + matVecMul L y, ⟨y, hy, rfl⟩, hkey y⟩

/-- Translates of open sets are open. -/
theorem isOpen_translateSet {S : Set (Vec d)} (hS : IsOpen S) (z : Vec d) :
    IsOpen (translateSet z S) := by
  rw [← preimage_subRight_eq_translateSet]
  exact hS.preimage (continuous_id.sub continuous_const)

/-- The affine image of an open set under an invertible matrix is open. -/
theorem isOpen_affineImage {L : Mat d} (hL : IsUnit L.det) (z : Vec d)
    {S : Set (Vec d)} (hS : IsOpen S) :
    IsOpen ((fun x => z + matVecMul L x) '' S) := by
  have hpre : (fun x => z + matVecMul L x) '' S =
      (fun y : Vec d => matVecMul L⁻¹ (y - z)) ⁻¹' S := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : matVecMul L⁻¹ (z + matVecMul L y - z) = y := by
        rw [add_sub_cancel_left, matVecMul_mul, Matrix.nonsing_inv_mul L hL,
          matVecMul_one]
      rw [Set.mem_preimage, this]
      exact hy
    · intro hp
      refine ⟨matVecMul L⁻¹ (p - z), hp, ?_⟩
      change z + matVecMul L (matVecMul L⁻¹ (p - z)) = p
      rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one,
        add_sub_cancel]
  rw [hpre]
  exact hS.preimage ((continuous_matVecMul L⁻¹).comp
    (continuous_id.sub continuous_const))

end

end RowSupply
end HighContrast
end HCPolySupport
