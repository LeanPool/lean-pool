/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCellRenormalization
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCellArithmetic

/-!
# High-contrast homogenization: Provider.Quenched.Prop211CellRenormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cell-renormalization adapter for the one-time rebase

This file identifies the gain used by the one-time rebase with the gain in
the public unit-range cell-renormalization theorem.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

theorem unitRangeCellGain_eq_publicGain (d : ℕ) (g : ℝ) (E : BlockMat d) :
    unitRangeCellGain d g E =
      32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d *
        (1 + renormShift d) * kappaRef E := by
  rw [unitRangeCellGain, unitRangeRenormShift, renormShift]
  ring

/-- The public cell-renormalization estimate in the gain convention used by
the one-time rebase. -/
theorem hasCellRenormalization_unitRangeCellGain_of_frozen [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    {n l0 h : ℕ}
    (hl : 0 ≤ (n : ℤ) - (l0 : ℤ)) (hh : h ≤ l0 + 1)
    (hhalf : (Psi ((3 : ℝ) ^ ((n : ℤ) - (l0 : ℤ))))⁻¹ ≤ 1 / 2) :
    HasCellRenormalization P S
      (annealedBlock P (centeredCube d ((n : ℤ) - (l0 : ℤ))))
      g ((d : ℝ) / 2) (unitRangeCellGain d g E) n l0 h := by
  have hl0n : l0 ≤ n := by omega
  rw [unitRangeCellGain_eq_publicGain]
  exact hasCellRenormalization_of_frozen hstat hunit hdag hl0n hh hhalf

end

end HCPolySupport.HighContrast.Quenched
