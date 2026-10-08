/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredResidualFrameRate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PhysicalCellResponseRealization
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PhysicalCellSolutionEnergyAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PhysicalFluxResponseCapPrice

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredObservationToPhysicalFluxRate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Observation response to the physical flux rate

The ruled observation cube contains the centered physical cell at one finer
generation.  The corresponding fixed factor is inserted into the frame bound
before the response--energy aggregation is used.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Multiplying every response bound by a fixed nonnegative scalar multiplies
the physical-frame constant by the same scalar. -/
theorem physicalFluxEpsilonFrameBound_const_mul
    {U : Set (Vec d)} {rho Rad b r Cflux : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (responseBound : system.CellIndex → ℝ)
    {epsilon Xval kappaRate Kframe factor : ℝ}
    (hfactor : 0 ≤ factor)
    (hframe : PhysicalFluxEpsilonFrameBound system b r Cflux responseBound
      epsilon Xval kappaRate Kframe) :
    PhysicalFluxEpsilonFrameBound system b r Cflux
      (fun i ↦ factor * responseBound i) epsilon Xval kappaRate
        (factor * Kframe) := by
  refine ⟨mul_nonneg hfactor hframe.1, ?_⟩
  intro i
  obtain ⟨hcoefficient, hbound⟩ := hframe.2 i
  refine ⟨?_, ?_⟩
  · unfold ruledPhysicalFluxResponseCoefficient
    change 0 ≤ physicalDualBesovScaleFactor (whitneyCellCube system i) r * Cflux *
        r⁻¹ * constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
        responseOneFromTwoGapFactor b r * (factor * responseBound i)
    rw [show physicalDualBesovScaleFactor (whitneyCellCube system i) r * Cflux *
        r⁻¹ * constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
        responseOneFromTwoGapFactor b r * (factor * responseBound i) =
      factor *
        (physicalDualBesovScaleFactor (whitneyCellCube system i) r * Cflux *
          r⁻¹ * constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r * responseBound i) by ring]
    exact mul_nonneg hfactor hcoefficient
  · unfold ruledPhysicalFluxResponseCoefficient at hbound ⊢
    calc
      physicalDualBesovScaleFactor (whitneyCellCube system i) r * Cflux * r⁻¹ *
            constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
            responseOneFromTwoGapFactor b r *
            (factor * responseBound i) =
          factor *
            (physicalDualBesovScaleFactor (whitneyCellCube system i) r *
              Cflux * r⁻¹ *
              constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
              responseOneFromTwoGapFactor b r * responseBound i) := by ring
      _ ≤ factor * (Kframe * (epsilon * Xval) ^ kappaRate) :=
        mul_le_mul_of_nonneg_left hbound hfactor
      _ = factor * Kframe * (epsilon * Xval) ^ kappaRate := by ring

end

end RowSupply
end HighContrast
end HCPolySupport
