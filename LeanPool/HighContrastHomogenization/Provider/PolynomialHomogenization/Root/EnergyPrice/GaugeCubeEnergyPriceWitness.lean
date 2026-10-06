/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.LawFreeCubeEnergyPrice
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.BufferToCell.PositiveBesovContinuousComparison
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.DirichletCapstoneBoundary
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeEnergyRestriction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.EnergyPrice.GaugeCubeEnergyPriceWitness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The capstone energy predicate, inhabited on a cube with a law-free constant

`GaugePhysicalEnergyPriceAtWitness U aPhysical u Kenergy boundaryEnergy` is the
open analytic hypothesis of the Dirichlet capstone.  This file inhabits it,
byte-for-byte, at a *triadic cube* witness with

  `Kenergy = gaugeCubeEnergyPrice C d s (cubeScaleFactor Q)`,

an explicit function of the dimension, the fractional order, and the cube's
side length only — no law, no sample, no ellipticity constant.

The three inputs are: the upstream dimension-only Dirichlet energy package
(`energyConsequencesRHSTheory`), the coarse-ellipticity window of
`HCPoly.Provider.PolynomialHomogenization.Root.EnergyPrice.LawFreeCubeEnergyPrice`
(a single scalar hypothesis `𝓔 ≤ 1`), and
the positive-Besov/Euclidean-fractional comparison.
-/

namespace HCPolySupport
namespace HighContrast
namespace EnergyPrice

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The un-squared law-free bound -/

/-! ## The `ENNReal` energy average on a cube -/

/-- The extended-real coefficient-energy average on a cube is the square of the
`ENNReal` realization of the public cube energy norm. -/
theorem eVolumeAverage_coefficientEnergyDensity_eq
    (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    eVolumeAverage (openCubeSet Q) (fun z ↦
        ENNReal.ofReal
          (coefficientEnergyDensity ((a.coeffOn Q).toCoeffField) u.grad z)) =
      ENNReal.ofReal (h1EnergyNormOnCube Q a u) ^ (2 : ℕ) := by
  have hW : weightedGradNorm ((a.coeffOn Q).toCoeffField) (openCubeSet Q) u.grad =
      (eVolumeAverage (openCubeSet Q) (fun z ↦
        ENNReal.ofReal
          (coefficientEnergyDensity ((a.coeffOn Q).toCoeffField) u.grad z))) ^
        (1 / 2 : ℝ) := rfl
  have hE := weightedGradNorm_eq_ofReal_h1EnergyNormOnCube Q a u
  rw [hW] at hE
  rw [← hE, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-! ## The law-free capstone price at a cube witness -/

end

end EnergyPrice
end HighContrast
end HCPolySupport
