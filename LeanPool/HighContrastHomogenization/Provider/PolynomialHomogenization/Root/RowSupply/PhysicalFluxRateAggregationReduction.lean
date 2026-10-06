/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PhysicalFluxResponseCapPrice

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.PhysicalFluxRateAggregationReduction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical flux-response rate aggregation

The cellwise response coefficient and the cellwise solution energy are kept
separate.  A uniform physical-frame estimate for the former and a normalized
energy-row estimate for the latter combine without any further analytic input.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The response-dependent coefficient in the physical flux price, before the
solution energy is inserted. -/
@[expose]
noncomputable def ruledPhysicalFluxResponseCoefficient
    [NeZero d] {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (b r Cflux : ℝ) (responseBound : system.CellIndex → ℝ)
    (i : system.CellIndex) : ℝ :=
  physicalDualBesovScaleFactor
      (whitneyCellCube system i) r *
    Cflux * r⁻¹ *
    constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
    responseOneFromTwoGapFactor b r * responseBound i

/-- A physical-frame response estimate is a uniform power bound on the whole
coefficient multiplying the cell solution energy. -/
@[expose]
def PhysicalFluxEpsilonFrameBound
    [NeZero d] {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (b r Cflux : ℝ) (responseBound : system.CellIndex → ℝ)
    (epsilon Xval kappaRate Kframe : ℝ) : Prop :=
  0 ≤ Kframe ∧ ∀ i,
    0 ≤ ruledPhysicalFluxResponseCoefficient system b r Cflux
        responseBound i ∧
      ruledPhysicalFluxResponseCoefficient system b r Cflux
          responseBound i ≤
        Kframe * (epsilon * Xval) ^ kappaRate

/-- The normalized row of squared cell-solution energies. -/
@[expose]
noncomputable def physicalCellSolutionEnergyRow
    [NeZero d] {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d)) : ℝ≥0∞ :=
  normalizedWhitneyRowEnergy system (fun i ↦
    ENNReal.ofReal
      (forcedSolutionEnergyNorm (whitneyCellCube system i)
        (aCell i) (wCell i)) ^ 2)

/-- A uniform response factor pulls out of the normalized physical-cell row. -/
theorem responseBoundEnergyRow_le_frame_mul_solutionEnergyRow
    [NeZero d] {U : Set (Vec d)} {rho Rad b r Cflux : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (responseBound : system.CellIndex → ℝ)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    {epsilon Xval kappaRate Kframe : ℝ}
    (hbase : 0 ≤ epsilon * Xval)
    (hframe : PhysicalFluxEpsilonFrameBound system b r Cflux responseBound
      epsilon Xval kappaRate Kframe) :
    normalizedWhitneyRowEnergy system
        (ruledPhysicalFluxResponseBoundEnergyCellEnergy system b r Cflux
          responseBound aCell wCell) ≤
      ENNReal.ofReal (Kframe * (epsilon * Xval) ^ kappaRate) ^ 2 *
        physicalCellSolutionEnergyRow system aCell wCell := by
  have hrate : 0 ≤ (epsilon * Xval) ^ kappaRate :=
    Real.rpow_nonneg hbase _
  have hfront : 0 ≤ Kframe * (epsilon * Xval) ^ kappaRate :=
    mul_nonneg hframe.1 hrate
  have hcell : ∀ i,
      ruledPhysicalFluxResponseBoundEnergyCellEnergy system b r Cflux
          responseBound aCell wCell i ≤
        ENNReal.ofReal (Kframe * (epsilon * Xval) ^ kappaRate) ^ 2 *
          ENNReal.ofReal
            (forcedSolutionEnergyNorm (whitneyCellCube system i)
              (aCell i) (wCell i)) ^ 2 := by
    intro i
    let E := forcedSolutionEnergyNorm (whitneyCellCube system i)
      (aCell i) (wCell i)
    have hE : 0 ≤ E := by
      dsimp only [E, forcedSolutionEnergyNorm, h1EnergyNormOnCube]
      positivity
    have hproduct :
        ruledPhysicalFluxResponseBoundEnergyProduct system b r Cflux
            responseBound aCell wCell i ≤
          (Kframe * (epsilon * Xval) ^ kappaRate) * E := by
      calc
        ruledPhysicalFluxResponseBoundEnergyProduct system b r Cflux
            responseBound aCell wCell i =
            ruledPhysicalFluxResponseCoefficient system b r Cflux
              responseBound i * E := by
                rfl
        _ ≤ (Kframe * (epsilon * Xval) ^ kappaRate) * E :=
          mul_le_mul_of_nonneg_right (hframe.2 i).2 hE
    unfold ruledPhysicalFluxResponseBoundEnergyCellEnergy
    calc
      ENNReal.ofReal
          (ruledPhysicalFluxResponseBoundEnergyProduct system b r Cflux
            responseBound aCell wCell i) ^ 2 ≤
          ENNReal.ofReal
            ((Kframe * (epsilon * Xval) ^ kappaRate) * E) ^ 2 :=
        pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hproduct) 2
      _ = ENNReal.ofReal (Kframe * (epsilon * Xval) ^ kappaRate) ^ 2 *
          ENNReal.ofReal E ^ 2 := by
        rw [ENNReal.ofReal_mul hfront, mul_pow]
      _ = ENNReal.ofReal (Kframe * (epsilon * Xval) ^ kappaRate) ^ 2 *
          ENNReal.ofReal
            (forcedSolutionEnergyNorm (whitneyCellCube system i)
              (aCell i) (wCell i)) ^ 2 := by simp only [E]
  refine (normalizedWhitneyRowEnergy_mono system hcell).trans (le_of_eq ?_)
  exact normalizedWhitneyRowEnergy_const_mul system _ _

/-- The frame estimate and an energy-row estimate give the required squared
power rate with an explicit product constant. -/
theorem physicalFluxResponseRateAggregation
    [NeZero d] {U : Set (Vec d)} {rho Rad b r Cflux : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (responseBound : system.CellIndex → ℝ)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    {epsilon Xval kappaRate Kframe Kenergy : ℝ}
    {boundaryEnergy : ℝ≥0∞}
    (hbase : 0 ≤ epsilon * Xval)
    (hframe : PhysicalFluxEpsilonFrameBound system b r Cflux responseBound
      epsilon Xval kappaRate Kframe)
    (hKenergy : 0 ≤ Kenergy)
    (henergy : physicalCellSolutionEnergyRow system aCell wCell ≤
      ENNReal.ofReal Kenergy * boundaryEnergy) :
    0 ≤ Kframe ^ 2 * Kenergy ∧
      normalizedWhitneyRowEnergy system
          (ruledPhysicalFluxResponseBoundEnergyCellEnergy system b r Cflux
            responseBound aCell wCell) ≤
        ENNReal.ofReal
            ((Kframe ^ 2 * Kenergy) *
              (epsilon * Xval) ^ (2 * kappaRate)) * boundaryEnergy := by
  refine ⟨mul_nonneg (sq_nonneg Kframe) hKenergy, ?_⟩
  have hrate : 0 ≤ (epsilon * Xval) ^ kappaRate :=
    Real.rpow_nonneg hbase _
  have hfront : 0 ≤ Kframe * (epsilon * Xval) ^ kappaRate :=
    mul_nonneg hframe.1 hrate
  have hpower : ((epsilon * Xval) ^ kappaRate) ^ 2 =
      (epsilon * Xval) ^ (2 * kappaRate) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hbase]
    congr 1
    ring_nf
  calc
    normalizedWhitneyRowEnergy system
        (ruledPhysicalFluxResponseBoundEnergyCellEnergy system b r Cflux
          responseBound aCell wCell) ≤
        ENNReal.ofReal (Kframe * (epsilon * Xval) ^ kappaRate) ^ 2 *
          physicalCellSolutionEnergyRow system aCell wCell :=
      responseBoundEnergyRow_le_frame_mul_solutionEnergyRow system
        responseBound aCell wCell hbase hframe
    _ ≤ ENNReal.ofReal (Kframe * (epsilon * Xval) ^ kappaRate) ^ 2 *
        (ENNReal.ofReal Kenergy * boundaryEnergy) :=
      mul_le_mul_of_nonneg_left henergy zero_le
    _ = ENNReal.ofReal
          ((Kframe ^ 2 * Kenergy) *
            (epsilon * Xval) ^ (2 * kappaRate)) * boundaryEnergy := by
      calc
        ENNReal.ofReal (Kframe * (epsilon * Xval) ^ kappaRate) ^ 2 *
            (ENNReal.ofReal Kenergy * boundaryEnergy) =
            (ENNReal.ofReal
                ((Kframe * (epsilon * Xval) ^ kappaRate) ^ 2) *
              ENNReal.ofReal Kenergy) * boundaryEnergy := by
                rw [ENNReal.ofReal_pow hfront]
                ac_rfl
        _ = ENNReal.ofReal
              (((Kframe * (epsilon * Xval) ^ kappaRate) ^ 2) * Kenergy) *
            boundaryEnergy := by
              rw [ENNReal.ofReal_mul
                (sq_nonneg (Kframe * (epsilon * Xval) ^ kappaRate))]
        _ = ENNReal.ofReal
              ((Kframe ^ 2 * Kenergy) *
                (epsilon * Xval) ^ (2 * kappaRate)) * boundaryEnergy := by
              congr 1
              rw [mul_pow, hpower]
              ring_nf

end

end RowSupply
end HighContrast
end HCPolySupport
