/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Selection.RoundedHops

/-!
# High-contrast homogenization: Provider.Regularity.RoundedAffineMap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The rounded affine map for physical regularity transfer

The rounded affine construction uses the base rounded grid.  This module packages its positivity,
symmetry, invertibility, size, and lattice-alignment properties at the single
canonical generation `kZero d`.
-/

namespace HCPolySupport
namespace HighContrast

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The base rounded grid is a rounded grid at its canonical alignment. -/
theorem isRoundedGrid_baseRoundedGrid {m : Mat d} (hm : m.PosDef) :
    IsRoundedGrid (kZero d : ℤ) (baseRoundedGrid m) := by
  exact ⟨le_rfl, m, hm, rfl⟩

/-- The rounded affine map remains positive definite. -/
theorem posDef_baseRoundedGrid {m : Mat d} (hm : m.PosDef) :
    (baseRoundedGrid m).PosDef := by
  exact Recurrence.posDef_of_isRoundedGrid (isRoundedGrid_baseRoundedGrid hm)

/-- The rounded affine map is symmetric. -/
theorem matTranspose_baseRoundedGrid {m : Mat d} (hm : m.PosDef) :
    matTranspose (baseRoundedGrid m) = baseRoundedGrid m := by
  ext i j
  exact Recurrence.roundedGrid_symm (kZero d : ℤ) hm.posSemidef i j

/-- The determinant of the rounded affine map is a unit. -/
theorem isUnit_det_baseRoundedGrid {m : Mat d} (hm : m.PosDef) :
    IsUnit (baseRoundedGrid m).det := by
  exact isUnit_det_of_posDef (posDef_baseRoundedGrid hm)

/-- The rounded affine inverse has a dimension-independent operator bound. -/
theorem norm_inv_baseRoundedGrid_le [NeZero d] {m : Mat d} (hm : m.PosDef) :
    ‖(baseRoundedGrid m)⁻¹‖ ≤ 101 / 100 := by
  exact Selection.norm_inv_roundedGrid_le
    (show (kZero d : ℤ) ≤ (kZero d : ℤ) from le_rfl) hm

end

end HighContrast
end HCPolySupport
