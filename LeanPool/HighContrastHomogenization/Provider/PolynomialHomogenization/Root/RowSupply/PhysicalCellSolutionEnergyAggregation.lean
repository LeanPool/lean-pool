/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PhysicalFluxRateAggregationReduction
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CellFamilyAndFluxRow

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.PhysicalCellSolutionEnergyAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Aggregation of physical cell-solution energies

The normalized sum of the forced-solution energies on the selected cells is
the normalized coefficient energy of the physical solution on the domain.
This is a measure-theoretic consequence of the disjoint cell covering.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem volume_whitneyCell_ne_top_energy
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : volume (system.cell i) ≠ ⊤ :=
  (volume_openCubeSet_lt_top (whitneyCellCube system i)).ne

/-- On one selected cell, its volume times the squared normalized solution
energy is the integral of the physical coefficient-energy density. -/
theorem volume_mul_cellSolutionEnergy_eq_physicalEnergyIntegral
    [NeZero d] {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (aPhysical : CoeffField d) (u : H1Function U)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    (hfamily : RuledCellPhysicalForcedFamily system aPhysical u aCell wCell)
    (i : system.CellIndex) :
    volume (system.cell i) *
        ENNReal.ofReal
          (forcedSolutionEnergyNorm (whitneyCellCube system i)
            (aCell i) (wCell i)) ^ 2 =
      ∫⁻ x in system.cell i,
        ENNReal.ofReal (coefficientEnergyDensity aPhysical u.grad x) ∂volume := by
  let Q : TriadicCube d := whitneyCellCube system i
  let F : Vec d → Vec d := forcedSolutionGradientField (wCell i)
  let ePublic : Vec d → ℝ :=
    coefficientEnergyDensity (publicCoeffField Q (aCell i)) F
  let ePhysical : Vec d → ℝ :=
    coefficientEnergyDensity aPhysical u.grad
  have hpub : publicCoeffField Q (aCell i) =ᵐ[volume.restrict (system.cell i)]
      ((aCell i).coeffOn Q).toCoeffField := by
    simpa only [Q, openCubeSet_whitneyCellCube] using
      publicCoeffField_ae_eq_openCubeSet Q (aCell i)
  have henergy : ePublic =ᵐ[volume.restrict (system.cell i)] ePhysical := by
    filter_upwards [hpub, hfamily.1 i] with x hxPub hxCell
    simp only [ePublic, ePhysical, coefficientEnergyDensity, F,
      forcedSolutionGradientField]
    rw [hxPub, hxCell, hfamily.2 i x]
  have hEll := publicCoeffField_isEllipticFieldOn_cubeSet Q (aCell i)
  have hnonneg : 0 ≤ cubeAverage Q ePublic :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      Q _ F hEll
  have hint : IntegrableOn ePublic (cubeSet Q) volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      (by
        have hgrad : (wCell i).toH1.toCubeSet.grad = (wCell i).toH1.grad :=
          H1Function.grad_toCubeSet (wCell i).toH1
        simpa [Q, F, forcedSolutionGradientField, hgrad] using
          (wCell i).toH1.toCubeSet.grad_memVectorL2)
  have hpoint : 0 ≤ᵐ[volume.restrict (cubeSet Q)] ePublic := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll F x hx
  have hlint : ENNReal.ofReal (∫ x in cubeSet Q, ePublic x ∂volume) =
      ∫⁻ x in cubeSet Q, ENNReal.ofReal (ePublic x) ∂volume :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hpoint
  have hrestrict : volume.restrict (openCubeSet Q) =
      volume.restrict (cubeSet Q) :=
    (volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q).symm
  have henergyCube : ePublic =ᵐ[volume.restrict (cubeSet Q)] ePhysical := by
    rw [← hrestrict]
    simpa only [Q, openCubeSet_whitneyCellCube] using henergy
  have hlintegral :
      (∫⁻ x in cubeSet Q, ENNReal.ofReal (ePublic x) ∂volume) =
        ∫⁻ x in system.cell i, ENNReal.ofReal (ePhysical x) ∂volume := by
    rw [← hrestrict]
    apply lintegral_congr_ae
    filter_upwards [henergy] with x hx
    rw [hx]
  have hvolTop : volume (openCubeSet Q) ≠ ⊤ :=
    volume_whitneyCell_ne_top_energy system i
  have hvolEq : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [← volume_openCubeSet_toReal Q, ENNReal.ofReal_toReal hvolTop]
  have hcubeVolPos : 0 < cubeVolume Q := cubeVolume_pos Q
  rw [forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField]
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]
  change volume (openCubeSet Q) * ENNReal.ofReal (cubeAverage Q ePublic) = _
  rw [hvolEq]
  unfold cubeAverage
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcubeVolPos.le),
    ENNReal.ofReal_inv_of_pos hcubeVolPos, hlint, hlintegral]
  have hcv0 : ENNReal.ofReal (cubeVolume Q) ≠ 0 := by positivity
  have hcvt : ENNReal.ofReal (cubeVolume Q) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← mul_assoc, ENNReal.mul_inv_cancel hcv0 hcvt, one_mul]

/-- Disjointness and almost-everywhere covering identify the normalized cell
energy row with the normalized physical coefficient energy on the domain. -/
theorem physicalCellSolutionEnergyRow_eq_physicalEnergyAverage
    [NeZero d] {U : Set (Vec d)} {rho Rad : ℝ}
    (hd : 1 ≤ d)
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U)
    (aPhysical : CoeffField d) (u : H1Function U)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    (hfamily : RuledCellPhysicalForcedFamily system aPhysical u aCell wCell) :
    physicalCellSolutionEnergyRow system aCell wCell =
      eVolumeAverage U (fun x =>
        ENNReal.ofReal (coefficientEnergyDensity aPhysical u.grad x)) := by
  let f : Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (coefficientEnergyDensity aPhysical u.grad x)
  have hsum : (∑' i : system.CellIndex,
      ∫⁻ x in system.cell i, f x ∂volume) = ∫⁻ x in U, f x ∂volume := by
    rw [← lintegral_iUnion (fun i => measurableSet_whitneyCell system i)
      (pairwise_disjoint_whitneyCells system) f]
    exact setLIntegral_congr (iUnion_whitneyCells_ae_eq_domain system hd hU)
  unfold physicalCellSolutionEnergyRow normalizedWhitneyRowEnergy
    rawWhitneyRowEnergy eVolumeAverage
  rw [show (∑' i : system.CellIndex,
      volume (system.cell i) *
        ENNReal.ofReal
          (forcedSolutionEnergyNorm (whitneyCellCube system i)
            (aCell i) (wCell i)) ^ 2) =
      ∑' i : system.CellIndex, ∫⁻ x in system.cell i, f x ∂volume by
        congr 1
        funext i
        exact volume_mul_cellSolutionEnergy_eq_physicalEnergyIntegral
          system aPhysical u aCell wCell hfamily i]
  rw [hsum, ENNReal.div_eq_inv_mul]

/-- Any global physical-energy estimate immediately supplies the energy-row
premise of the response-rate aggregation theorem. -/
theorem physicalCellSolutionEnergyRow_le_of_physicalEnergyAverage_le
    [NeZero d] {U : Set (Vec d)} {rho Rad : ℝ}
    (hd : 1 ≤ d)
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U)
    (aPhysical : CoeffField d) (u : H1Function U)
    (aCell : system.CellIndex → CoeffFamily d)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    (hfamily : RuledCellPhysicalForcedFamily system aPhysical u aCell wCell)
    {Kenergy : ℝ} {boundaryEnergy : ℝ≥0∞}
    (henergy : eVolumeAverage U (fun x =>
        ENNReal.ofReal (coefficientEnergyDensity aPhysical u.grad x)) ≤
      ENNReal.ofReal Kenergy * boundaryEnergy) :
    physicalCellSolutionEnergyRow system aCell wCell ≤
      ENNReal.ofReal Kenergy * boundaryEnergy := by
  rw [physicalCellSolutionEnergyRow_eq_physicalEnergyAverage
    hd system hU aPhysical u aCell wCell hfamily]
  exact henergy

end

end RowSupply
end HighContrast
end HCPolySupport
