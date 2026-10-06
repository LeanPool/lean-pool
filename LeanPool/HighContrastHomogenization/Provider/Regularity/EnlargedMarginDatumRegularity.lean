/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledTriadicWhitneyCarrier
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyCellInitialAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyWhitneySystem
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleCubeRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicInteriorHessian
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.DualityPositivePairing
public import LeanPool.HighContrastHomogenization.Support.Besov.Poincare.Projection
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ObservationCoefficientTransport

/-!
# High-contrast homogenization: Provider.Regularity.EnlargedMarginDatumRegularity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Observation-datum regularity from enlarged Whitney margins

The ninefold admissibility buffer places both the closure of the observation
cube and that cube itself inside the strict inner half of the next centered
triadic cube.  This supplies the geometric hypotheses of the constant-
coefficient datum regularity theorem after translating a selected cell to the
origin.
-/

namespace HCPolySupport
namespace HighContrast
open Book Book.Ch03 MeasureTheory Set
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The center used to view an enlarged-margin cell from the origin. -/
@[expose]
def enlargedMarginObservationCenter
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : Vec d :=
  standardCellCenter (system.scale i) (system.index i)

/-- The ambient cube furnished by ninefold admissibility is one scale larger
than the observation cube. -/
@[expose]
def enlargedMarginAmbientCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : TriadicCube d :=
  originCube d (system.scale i + 2)

/-- The enlarged admissibility buffer is the translated ambient cube. -/
theorem interiorBuffer_eq_translateSet_ambientCube
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) :
    system.interiorBuffer i =
      translateSet (enlargedMarginObservationCenter system i)
        (openCubeSet (enlargedMarginAmbientCube system i)) := by
  unfold EnlargedMarginRuledTriadicWhitneySystem.interiorBuffer
    enlargedMarginWhitneyInteriorBuffer enlargedMarginObservationCenter
    enlargedMarginAmbientCube
  rw [openCubeAtScale_eq_translateSet,
    openCubeAtScale_zero_eq_openCubeSet_originCube]

end

end HighContrast
end HCPolySupport
