/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.ResponseAttainabilityPricing
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CellFamilyAndFluxRow

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.PhysicalFluxResponseCapPrice

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical-cell flux-response cap price

For zero forcing, the coarse flux-response right-hand side is exactly a cube
response multiplied by the forced-solution energy.  The exponent-gap estimate
converts the outer-one response at the regularity order to the supplied
outer-two response at a lower order before the Whitney cells are summed.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The physical-cell response--energy product after inserting a supplied
outer-two response bound. -/
@[expose]
noncomputable def ruledPhysicalFluxResponseBoundEnergyProduct
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (b r Cflux : ℝ) (responseBound : system.CellIndex → ℝ)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    (i : system.CellIndex) : ℝ :=
  physicalDualBesovScaleFactor
      (whitneyCellCube system i) r *
    Cflux * r⁻¹ *
    constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
    responseOneFromTwoGapFactor b r * responseBound i *
    forcedSolutionEnergyNorm (whitneyCellCube system i) (aCell i) (wCell i)

/-- The squared physical-cell response--energy contribution. -/
@[expose]
noncomputable def ruledPhysicalFluxResponseBoundEnergyCellEnergy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (b r Cflux : ℝ) (responseBound : system.CellIndex → ℝ)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    (i : system.CellIndex) : ℝ≥0∞ :=
  ENNReal.ofReal
    (ruledPhysicalFluxResponseBoundEnergyProduct system b r Cflux
      responseBound aCell wCell i) ^ 2

/-- A response bound on each physical cell prices the exact coarse-response
cap used by the four-row join. -/
theorem physicalFluxResponseCap_le_responseBoundEnergyRow [NeZero d]
    {U : Set (Vec d)} {rho Rad b r Cflux : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (responseBound : system.CellIndex → ℝ)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    (hb : 0 < b) (hbr : b < r) (hCflux : 0 ≤ Cflux)
    (hResponse : ∀ i,
      Book.Ch02.HomogenizationErrorOnCube
          (whitneyCellCube system i) b .infinity (.finite 2)
            (aCell i) (identityConstantCoeffMatrix d).matrix ≤
        responseBound i) :
    normalizedWhitneyRowEnergy system (fun i ↦
        ENNReal.ofReal
          (physicalDualBesovScaleFactor
              (whitneyCellCube system i) r *
            coarseFluxResponseWithRHSRHS Cflux
              (whitneyCellCube system i) (aCell i)
                (identityConstantCoeffMatrix d) r
                (0 : Vec d → Vec d) (wCell i)) ^ 2) ≤
      normalizedWhitneyRowEnergy system
        (ruledPhysicalFluxResponseBoundEnergyCellEnergy system b r Cflux
          responseBound aCell wCell) := by
  have hr : 0 < r := hb.trans hbr
  apply normalizedWhitneyRowEnergy_mono system
  intro i
  let Q := whitneyCellCube system i
  let a0 := identityConstantCoeffMatrix d
  let E := forcedSolutionEnergyNorm Q (aCell i) (wCell i)
  have hE : 0 ≤ E := by
    dsimp only [E, forcedSolutionEnergyNorm]
    unfold h1EnergyNormOnCube
    positivity
  have hnorm : 0 ≤ constantCoeffMatrixNormHalf a0 := by
    unfold constantCoeffMatrixNormHalf
    exact Real.rpow_nonneg (Book.Ch02.matrixNorm_nonneg a0.matrix) _
  have hscale : 0 ≤ physicalDualBesovScaleFactor Q r :=
    physicalDualBesovScaleFactor_nonneg Q r
  have hgap : 0 ≤ responseOneFromTwoGapFactor b r :=
    responseOneFromTwoGapFactor_nonneg hb hbr
  have hfront : 0 ≤
      physicalDualBesovScaleFactor Q r * Cflux * r⁻¹ *
        constantCoeffMatrixNormHalf a0 * E := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hscale hCflux) (inv_nonneg.mpr hr.le)) hnorm)
      hE
  have hresponse :=
    homogenizationErrorOnCube_infinity_one_le_gap_mul_infinity_two
      Q (aCell i) a0.matrix hb hbr
  have hraw :
      physicalDualBesovScaleFactor Q r *
          coarseFluxResponseWithRHSRHS Cflux Q (aCell i) a0 r
            (0 : Vec d → Vec d) (wCell i) ≤
        ruledPhysicalFluxResponseBoundEnergyProduct system b r Cflux
          responseBound aCell wCell i := by
    unfold coarseFluxResponseWithRHSRHS
    simp only [scaleNormalizedPositiveBesovVectorSeminormTwo,
      cubeBesovPositiveVectorSeminormTwo_zero, mul_zero, add_zero]
    unfold ruledPhysicalFluxResponseBoundEnergyProduct
    change
      physicalDualBesovScaleFactor Q r *
          (Cflux * r⁻¹ * constantCoeffMatrixNormHalf a0 * E *
            Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1)
              (aCell i) a0.matrix) ≤
        physicalDualBesovScaleFactor Q r * Cflux * r⁻¹ *
          constantCoeffMatrixNormHalf a0 * responseOneFromTwoGapFactor b r *
          responseBound i * E
    calc
      physicalDualBesovScaleFactor Q r *
          (Cflux * r⁻¹ * constantCoeffMatrixNormHalf a0 * E *
            Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1)
              (aCell i) a0.matrix) =
          (physicalDualBesovScaleFactor Q r * Cflux * r⁻¹ *
            constantCoeffMatrixNormHalf a0 * E) *
              Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1)
                (aCell i) a0.matrix := by ring
      _ ≤ (physicalDualBesovScaleFactor Q r * Cflux * r⁻¹ *
            constantCoeffMatrixNormHalf a0 * E) *
          (responseOneFromTwoGapFactor b r *
            Book.Ch02.HomogenizationErrorOnCube Q b .infinity (.finite 2)
              (aCell i) a0.matrix) :=
        mul_le_mul_of_nonneg_left hresponse hfront
      _ ≤ (physicalDualBesovScaleFactor Q r * Cflux * r⁻¹ *
            constantCoeffMatrixNormHalf a0 * E) *
          (responseOneFromTwoGapFactor b r * responseBound i) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hResponse i) hgap) hfront
      _ = physicalDualBesovScaleFactor Q r * Cflux * r⁻¹ *
          constantCoeffMatrixNormHalf a0 * responseOneFromTwoGapFactor b r *
          responseBound i * E := by ring
  unfold ruledPhysicalFluxResponseBoundEnergyCellEnergy
  exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hraw) 2

end

end RowSupply
end HighContrast
end HCPolySupport
