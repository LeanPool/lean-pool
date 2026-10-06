/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH10
public import LeanPool.HighContrastHomogenization.Analytic.AffineNegSobolevNorm
public import LeanPool.HighContrastHomogenization.Analytic.H1a0ToH10
public import LeanPool.HighContrastHomogenization.Provider.Initialization.IdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledLocalizationAssembly
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.FluxComparisonLocalization
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.CenteredCubeFractionalCZFullNorm
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.L2RowAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalEquation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderIdentityCubeDualRegularity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.CutoffProduct
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Basic
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.AECongruence
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.DefinitionsAPI

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.CenteredIndicatorExtensionBasic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The centered one-step indicator extension

The child test is extended by zero to its centered parent and multiplied by
the parent-to-child volume ratio.  This module proves the exact pairing
identity and the local square-integrability part of the parent test carrier.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {s : ℝ}

/-- The centered scale-`m` cube is the middle child of the centered
scale-`m+1` cube. -/
theorem originCube_mem_childCubes_succ (d : ℕ) (m : ℤ) :
    originCube d m ∈ childCubes (originCube d (m + 1)) := by
  simpa [originCube] using! middleChild_mem_childCubes (originCube d (m + 1))

end

end RowSupply
end HighContrast
end HCPolySupport
