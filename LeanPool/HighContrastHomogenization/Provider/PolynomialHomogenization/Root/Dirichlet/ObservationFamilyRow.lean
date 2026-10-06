/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.GaugeWeakSolutionAndCellFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ObservationCoefficientTransport

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.ObservationFamilyRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The composed row 6

Module the `aObs` premise/`hObs` pair: an observation coefficient family, one per
ruled cell, agreeing a.e. on the observation cube with the gauge coefficient
translated to that cell's centre.

The producer is the `exists_observationCoeffFamily_and_forcedEquation`
(`HCPoly.Provider.Regularity.ObservationCoefficientTransport`), at
`center := ruledObservationCenter system i` and
`m := (ruledObservationCube system i).scale`.  Its domain premise
`openCubeAtScale center m ⊆ U` is the composition
`translateSet_observationCube_subset_interiorBuffer` ∘ `interiorBuffer_subset`,
the same pair `CommonResidualObservationParent` uses; the two cube spellings are
reconciled by `openCubeAtScale_eq_translateSet` and
`openCubeAtScale_zero_eq_openCubeSet_originCube`.

The weak-solution premise is row 4′ of module that module, and the source witness is
`exists_gaugeReducedSource`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-- **Row 6 — `aObs`, `hObs`.**  One observation coefficient family per ruled
cell, in exact spelling. -/
theorem exists_frozenWitnessObservationFamily [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {a : CoeffSpace d}
    {Uhat : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem Uhat rho Rad)
    {aHat : CoeffField d}
    (haHat : aHat = affineCoefficient (matSqrt (symmPart abar))
      (isUnit_det_matSqrt hS)
      (fun z ↦ scaledCoeff epsilon a z - skewPart abar))
    (uHat : H1Function Uhat)
    (hWeak : IsWeakSolutionOn aHat Uhat uHat.grad) :
    ∃ aObs : system.CellIndex → CoeffFamily d, ∀ i,
      ((aObs i).coeffOn (ruledObservationCube system i)).toCoeffField
          =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
        fun y ↦ affineCoefficient (matSqrt (symmPart abar))
          (isUnit_det_matSqrt hS)
          (fun z ↦ scaledCoeff epsilon a z - skewPart abar)
          (y + ruledObservationCenter system i) := by
  subst haHat
  obtain ⟨aSource, haSource, haeSource⟩ :=
    exists_gaugeReducedSource hS hepsilon a
  have hex : ∀ i : system.CellIndex, ∃ aObs : CoeffFamily d,
      ((aObs.coeffOn (ruledObservationCube system i)).toCoeffField
          =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
        fun y ↦ affineCoefficient (matSqrt (symmPart abar))
          (isUnit_det_matSqrt hS)
          (fun z ↦ scaledCoeff epsilon a z - skewPart abar)
          (y + ruledObservationCenter system i)) := by
    intro i
    have hsub : openCubeAtScale (ruledObservationCenter system i)
        ((ruledObservationCube system i).scale) ⊆ Uhat := by
      rw [openCubeAtScale_eq_translateSet,
        openCubeAtScale_zero_eq_openCubeSet_originCube]
      exact (translateSet_observationCube_subset_interiorBuffer system i).trans
        (system.interiorBuffer_subset i)
    obtain ⟨aObs, -, hae, -, -, -⟩ :=
      exists_observationCoeffFamily_and_forcedEquation aSource haSource
        (affineCoefficient (matSqrt (symmPart abar)) (isUnit_det_matSqrt hS)
          (fun z ↦ scaledCoeff epsilon a z - skewPart abar))
        haeSource uHat hWeak (ruledObservationCenter system i)
        ((ruledObservationCube system i).scale) hsub
    exact ⟨aObs, hae⟩
  choose aObs hObs using hex
  exact ⟨aObs, hObs⟩

end

end RowSupply
end HighContrast
end HCPolySupport
