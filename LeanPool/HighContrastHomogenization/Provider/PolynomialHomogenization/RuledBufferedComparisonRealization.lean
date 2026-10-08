/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledObservationComparisonPricing
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledPairingAggregation
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.Basic
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfacesComponentwise

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledBufferedComparisonRealization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Buffered comparison realizations on ruled Whitney cells

The constant-coefficient comparison datum is restricted to each inward
physical buffer and translated to its origin-centered observation cube.  A
single observation Dirichlet family supplies the prescribed trace, the
physical-cell comparison fields, and the mixed Caccioppoli row.
-/

namespace HCPolySupport
namespace HighContrast
open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The physical flux defect on one ruled cell. -/
@[expose]
def ruledPhysicalFluxDefectOnCell
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (aPhysical : CoeffField d)
    (a0 : system.CellIndex → ConstantCoeffMatrix d)
    (u : H1Function U) (i : system.CellIndex) (x : Vec d) : Vec d :=
  matVecMul (aPhysical x - (a0 i).matrix) (u.grad x)

end

end HighContrast
end HCPolySupport
