/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreDefinitions
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceConstantMatrix
public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseGeometry
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneySquareWeights
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity
public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.DualityPositiveBridge.CoordinateStandard
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.OverlapCoordinateBridge
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ExactOverlapEuclideanComparison
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeEuclideanHsFullNormConstantMatrix
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CommonQuantitativeAffineScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedOuterSpatialResponsePowerTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedPhysicalDirichletEuclideanHs
public import LeanPool.HighContrastHomogenization.Support.Besov.Negative.ExactAggregationBridge
public import LeanPool.HighContrastHomogenization.Support.Besov.PositiveOverlapBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.NegativeBesovLocalize
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ExactOverlapEuclideanFullComparison
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedHarmonicReplacement
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.AEEq
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.Response
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseFluxResponse.RHSCorrections
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincare.QTwo
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorWeightedGradientBridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeEnergyRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteSequenceBounds
public import LeanPool.HighContrastHomogenization.Provider.Regularity.SmallTailIteration

/-!
# High-contrast homogenization: Provider.Regularity.RoundedFiniteEnergyENNRealBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# ENNReal realization of the finite centered energy row

The Step-4 recurrence is real-valued, while the root weighted norm is
`ENNReal`-valued.  This file identifies the exact cube restrictions and lifts
the finite inequality without changing either carrier.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The weighted norm on an inner centered cube is exactly the `ENNReal`
realization of the finite centered energy row. -/
theorem weightedGradNorm_eq_ofReal_finiteCenteredCubeSolutionEnergy
    {d : ℕ} (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (h : ℤ) (hhm : h ≤ m) :
    weightedGradNorm (a.coeffOn (originCube d h)).toCoeffField
        (openCubeSet (originCube d h)) u.toH1.grad =
      ENNReal.ofReal (finiteCenteredCubeSolutionEnergy a m u h) := by
  let uH := finiteCubeSolutionRestriction a hhm u
  calc
    weightedGradNorm (a.coeffOn (originCube d h)).toCoeffField
        (openCubeSet (originCube d h)) u.toH1.grad =
        weightedGradNorm (a.coeffOn (originCube d h)).toCoeffField
          (openCubeSet (originCube d h)) uH.toH1.grad := by rfl
    _ = ENNReal.ofReal
        (Book.Ch03.h1EnergyNormOnCube (originCube d h) a uH.toH1) :=
      weightedGradNorm_eq_ofReal_h1EnergyNormOnCube
        (originCube d h) a uH.toH1
    _ = ENNReal.ofReal (finiteCenteredCubeSolutionEnergy a m u h) := by
      rw [finiteCenteredCubeSolutionEnergy_eq_of_le a m u h hhm]

end

end HighContrast
end HCPolySupport
