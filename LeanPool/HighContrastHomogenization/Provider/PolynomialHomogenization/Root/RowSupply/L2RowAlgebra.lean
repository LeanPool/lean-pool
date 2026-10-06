/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledBufferedComparisonRealization

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.RowSupply.L2RowAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized `L²` algebra for ruled Whitney rows

Every physical full-dual Whitney cell energy is priced by the normalized `L²`
average of its own field on the same cell.  That
bridge is *linear in the field on the left and quadratic on the right*, so a
pointwise splitting `H = F + G` of a cell-indexed family costs a factor two at
the level of normalized `L²` cell averages and therefore a factor two at the
level of normalized rows — no dual-norm triangle inequality is needed, and none
is available: `cubeBesovDualFullNorm` is a `sSup` whose value set is bounded
above only under `MemLp` hypotheses.

This module collects
* additivity, scalar homogeneity and monotonicity of `normalizedWhitneyRowEnergy`;
* the same three for the `L²`-priced cell energy of unit 28;
* the pointwise `L²` splitting `⨍|F+G|² ≤ 2⨍|F|² + 2⨍|G|²` on a cube; and
* the resulting **row join**: a family that splits pointwise into two families
  with priced normalized `L²` cell averages has its full-dual row under twice
  the sum of the two priced rows.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Cube averages -/

/-! ## Row algebra -/

variable {U : Set (Vec d)} {rho Rad : ℝ}

/-- Normalized rows are monotone. -/
theorem normalizedWhitneyRowEnergy_mono
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {X Y : system.CellIndex → ℝ≥0∞} (hXY : ∀ i, X i ≤ Y i) :
    normalizedWhitneyRowEnergy system X ≤
      normalizedWhitneyRowEnergy system Y := by
  unfold normalizedWhitneyRowEnergy rawWhitneyRowEnergy
  exact mul_le_mul_right
    (ENNReal.tsum_le_tsum fun i =>
      mul_le_mul_right (hXY i) (volume (system.cell i))) _

/-- Normalized rows are homogeneous. -/
theorem normalizedWhitneyRowEnergy_const_mul
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (c : ℝ≥0∞) (X : system.CellIndex → ℝ≥0∞) :
    normalizedWhitneyRowEnergy system (fun i => c * X i) =
      c * normalizedWhitneyRowEnergy system X := by
  unfold normalizedWhitneyRowEnergy rawWhitneyRowEnergy
  rw [show (∑' i : system.CellIndex,
      volume (system.cell i) * (c * X i)) =
      ∑' i : system.CellIndex, c * (volume (system.cell i) * X i) from
    tsum_congr fun i => by rw [mul_left_comm], ENNReal.tsum_mul_left,
    mul_left_comm]

/-! ## The `L²`-priced cell energy -/

/-! ## The full-dual to `L²` price for an arbitrary ruled family -/

/-! ## The row join -/

end

end RowSupply
end HighContrast
end HCPolySupport
