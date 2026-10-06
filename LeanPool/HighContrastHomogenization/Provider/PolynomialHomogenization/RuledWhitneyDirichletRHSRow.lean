/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

/- Dirichlet right-hand-side estimates on ruled Whitney cells. -/

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledWhitneyRowCauchySchwarz
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincareRHS
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseFluxResponseRHS
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.EnergyRHS.Theory

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.RuledWhitneyDirichletRHSRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast
open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The triadic cube represented by one index of a convex Whitney system. -/
@[expose]
def whitneyCellCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : TriadicCube d :=
  translateCube (system.index i) (originCube d (system.scale i))

@[simp] theorem openCubeSet_whitneyCellCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    openCubeSet (whitneyCellCube system i) = system.cell i := rfl

private theorem normalizedWhitneyRowEnergy_mono
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {X Y : system.CellIndex → ℝ≥0∞}
    (hXY : ∀ i, X i ≤ Y i) :
    normalizedWhitneyRowEnergy system X ≤
      normalizedWhitneyRowEnergy system Y := by
  unfold normalizedWhitneyRowEnergy rawWhitneyRowEnergy
  apply mul_le_mul_right
  exact ENNReal.tsum_le_tsum fun i =>
    mul_le_mul_right (hXY i) (volume (system.cell i))

end

end HighContrast
end HCPolySupport
