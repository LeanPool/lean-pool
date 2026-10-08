/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.DescendantHomogenizationErrorInfinityTwo
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Dilation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.PrintCellAnchoredObservationResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cell-anchored observation response

The dimensionful response row uses the scale of the cube on which it is
evaluated.  With this normalization, restriction to a triadic descendant is
monotone: the growth in the scale-normalized homogenization error is exactly
cancelled by the change of the physical scale factor.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- The physical scale factor carried by the dimensionful Besov row. -/
@[expose]
noncomputable def printCellScaleFactor (Q : TriadicCube d) (s : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (s * (Q.scale : ℝ))

end

end RowSupply
end HighContrast
end HCPolySupport
