/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CellFamilyAndFluxRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.DatumRowAggregation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincare

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.PrintDirectGradientResponsePrice

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Response price for the direct gradient energy map

The coarse response controls the inverse effective ellipticity in the direct
gradient estimate.  The Whitney geometry supplies a uniform upper bound for
the parent-scale normalization.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The physical dual scale factor written as a single power. -/
theorem physicalDualBesovScaleFactor_eq_rpow
    (Q : TriadicCube d) (s : ℝ) :
    physicalDualBesovScaleFactor Q s =
      Real.rpow (3 : ℝ) (s * ((Q.scale : ℤ) : ℝ)) := by
  unfold physicalDualBesovScaleFactor
  have hneg : Real.rpow (3 : ℝ) (-(s * ((Q.scale : ℤ) : ℝ))) =
      (Real.rpow (3 : ℝ) (s * ((Q.scale : ℤ) : ℝ)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [show -s * ((Q.scale : ℤ) : ℝ) =
    -(s * ((Q.scale : ℤ) : ℝ)) by ring, hneg, inv_inv]

end

end RowSupply
end HighContrast
end HCPolySupport
