/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.LocalHomogenizationErrorTranslation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.DescendantHomogenizationErrorInfinityTwo
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CenteredIndicatorExtensionBasic
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledObservationComparisonPricing

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.PhysicalCellResponseRealization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical-cell realization of observation response bounds

The observation and cell coefficient families may be constructed
independently.  Their local identifications with one physical coefficient,
the centered-child relation, and translation covariance identify the cell
response with the centered descendant response.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem centeredCell_mem_observationDescendants
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    originCube d (system.scale i) ∈
      descendantsAtScale (ruledObservationCube system i) (system.scale i) := by
  change originCube d (system.scale i) ∈
    descendantsAtScale (originCube d (system.scale i + 1)) (system.scale i)
  rw [descendantsAtScale_eq_descendantsAtDepth
    (originCube d (system.scale i + 1)) (by simp [originCube])]
  simpa [originCube, descendantsAtDepth_one] using
      originCube_mem_childCubes_succ d (system.scale i)

private theorem cubeTranslationVector_eq_ruledObservationCenter
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    cubeTranslationVector (system.index i) (originCube d (system.scale i)) =
      ruledObservationCenter system i := by
  funext j
  simp only [cubeTranslationVector, ruledObservationCenter,
    standardCellCenter, cubeScaleFactor_originCube]
  ring

/-- Local identifications of the independently constructed observation and
cell families give the exact translated centered-child response identity. -/
theorem physicalCellHomogenizationError_eq_centeredChild
    {U : Set (Vec d)} {rho Rad b : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (aObs aCell : system.CellIndex → Book.Ch02.TriadicCoeffFamily d)
    (f : system.CellIndex → CoeffField d)
    (hObs : ∀ i,
      ((aObs i).coeffOn (ruledObservationCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
          translateCoeffField (ruledObservationCenter system i) (f i))
    (hCell : ∀ i,
      ((aCell i).coeffOn (whitneyCellCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (whitneyCellCube system i))] f i)
    (i : system.CellIndex) :
    Book.Ch02.HomogenizationErrorOnCube
        (whitneyCellCube system i) b .infinity (.finite 2) (aCell i)
          (identityConstantCoeffMatrix d).matrix =
      Book.Ch02.HomogenizationErrorOnCube
        (originCube d (system.scale i)) b .infinity (.finite 2) (aObs i)
          (identityConstantCoeffMatrix d).matrix := by
  have hdesc := centeredCell_mem_observationDescendants system i
  have hObsChild := coeffOn_descendant_ae_eq_of_root_ae_eq
    (aObs i) (k := system.scale i)
      (by simp [ruledObservationCube, originCube]) hdesc (hObs i)
  have hObsChild' :
      ((aObs i).coeffOn (originCube d (system.scale i))).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d (system.scale i)))]
          translateCoeffField
            (cubeTranslationVector (system.index i)
              (originCube d (system.scale i))) (f i) := by
    rw [cubeTranslationVector_eq_ruledObservationCenter system i]
    exact hObsChild
  simpa only [whitneyCellCube] using
    (homogenizationErrorOnCube_translate_of_physical_ae
      (system.index i) (originCube d (system.scale i))
      (aCell i) (aObs i) (f i) (hCell i) hObsChild'
      b .infinity (.finite 2) (identityConstantCoeffMatrix d).matrix)

/-- A response bound on every observation cube yields the exact physical-cell
premise after the one-generation all-depth loss. -/
theorem physicalCellHomogenizationError_le_of_observationBound
    [NeZero d] {U : Set (Vec d)} {rho Rad b : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hb : 0 < b)
    (aObs aCell : system.CellIndex → Book.Ch02.TriadicCoeffFamily d)
    (f : system.CellIndex → CoeffField d)
    (responseBound : system.CellIndex → ℝ)
    (hObs : ∀ i,
      ((aObs i).coeffOn (ruledObservationCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
          translateCoeffField (ruledObservationCenter system i) (f i))
    (hCell : ∀ i,
      ((aCell i).coeffOn (whitneyCellCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (whitneyCellCube system i))] f i)
    (hResponse : ∀ i,
      Book.Ch02.HomogenizationErrorOnCube
          (ruledObservationCube system i) b .infinity (.finite 2) (aObs i)
            (identityConstantCoeffMatrix d).matrix ≤ responseBound i) :
    ∀ i,
      Book.Ch02.HomogenizationErrorOnCube
          (whitneyCellCube system i) b .infinity (.finite 2) (aCell i)
            (identityConstantCoeffMatrix d).matrix ≤
        Real.rpow (3 : ℝ) b * responseBound i := by
  intro i
  rw [physicalCellHomogenizationError_eq_centeredChild
    system aObs aCell f hObs hCell i]
  have hdesc := centeredCell_mem_observationDescendants system i
  have hchild :=
    homogenizationErrorOnCube_infinity_two_le_of_mem_descendantsAtScale
      (aObs i) (identityConstantCoeffMatrix d).matrix hb hdesc
  have hfactor :
      Real.rpow (3 : ℝ)
          (b * (Int.toNat
            ((ruledObservationCube system i).scale - system.scale i) : ℝ)) =
        Real.rpow (3 : ℝ) b := by
    change Real.rpow (3 : ℝ)
      (b * (Int.toNat ((system.scale i + 1) - system.scale i) : ℝ)) =
        Real.rpow (3 : ℝ) b
    norm_num
  rw [hfactor] at hchild
  exact hchild.trans (mul_le_mul_of_nonneg_left (hResponse i)
    (Real.rpow_nonneg (by norm_num) _))

end

end RowSupply
end HighContrast
end HCPolySupport
