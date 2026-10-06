/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.ResidualFrameResponseRateAlgebra
public import LeanPool.HighContrastHomogenization.Analytic.ConvexDomains

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.CommonResidualObservationParent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A common parent for residual-frame observation cells

After the exact triadic part of the microscopic dilation has been removed,
the residual affine grid is fixed and its scale lies in a compact interval.
All ruled observation cubes are contained in the bounded gauge domain, so
their affine images fit in one normalized-reference parent.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- A ruled observation target in residual affine coordinates is contained in
the affine image of the gauge domain. -/
theorem residualObservationTarget_subset_matImage
    [NeZero d] {U : Set (Vec d)} {rho Rad lambda : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (abar : Mat d) (i : system.CellIndex) :
    adaptedCellTranslate (epsilonAffineGrid lambda abar)
        (ruledObservationCube system i).scale
        (lambda⁻¹ • matVecMul (matSqrt (symmPart abar))
            (ruledObservationCenter system i) +
          adaptedCellCenter (epsilonAffineGrid lambda abar)
            (ruledObservationCube system i).scale 0) ⊆
      matImage (epsilonAffineGrid lambda abar) U := by
  let p := epsilonAffineGrid lambda abar
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  rcases hv with ⟨w, hw, rfl⟩
  have hcenterZero : adaptedCellCenter p
      (ruledObservationCube system i).scale 0 = 0 := by
    rw [Recurrence.adaptedCellCenter_eq]
    have hz : standardCellCenter
        (d := d) (ruledObservationCube system i).scale 0 = 0 := by
      funext j
      simp [standardCellCenter]
    rw [hz, matVecMul_zero]
  have hpsum : lambda⁻¹ •
        matVecMul (matSqrt (symmPart abar))
          (ruledObservationCenter system i) =
      matVecMul p (ruledObservationCenter system i) := by
    simp only [p, epsilonAffineGrid, smul_matVecMul]
  rw [hcenterZero, add_zero, hpsum]
  change matVecMul p (ruledObservationCenter system i) + matVecMul p w ∈
    matImage p U
  rw [← matVecMul_add]
  refine ⟨ruledObservationCenter system i + w, ?_, rfl⟩
  apply (translateSet_observationCube_subset_interiorBuffer system i).trans
    (system.interiorBuffer_subset i)
  have hwopen : w ∈ openCubeSet (ruledObservationCube system i) := by
    simpa only [ruledObservationCube, originCube, centeredCube] using hw
  refine ⟨w, hwopen, ?_⟩
  abel

end

end RowSupply
end HighContrast
end HCPolySupport
