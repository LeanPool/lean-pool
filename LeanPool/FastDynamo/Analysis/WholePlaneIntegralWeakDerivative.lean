/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneH1Core
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Integral weak derivatives in whole-plane H1, and the unit disk

This file states the test-function formulation of a whole-plane weak derivative
(`HasWholePlaneIntegralWeakDerivative`), proves that it is exactly the corresponding equality of
tempered distributions, and builds a whole-plane `H1` element from such identities
(`wholePlaneH1OfIntegralWeakDerivatives`).  It also fixes the closed unit disk, the unit circle
and the surface measure on the circle used by the discontinuous mode of
`lem:jump-horizontal-mode`.  No Gauss--Green theorem or trace operator for the disk is assumed.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set
open scoped LineDeriv SchwartzMap

section IntegralWeakDerivative

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The test-function formulation of the `j`-th whole-plane weak derivative.

The sign is built into the distributional line derivative: it evaluates the original
distribution on the negative derivative of the test function. -/
def HasWholePlaneIntegralWeakDerivative
    (f df : WholePlaneL2 F) (j : Fin 2) : Prop :=
  ∀ φ : SchwartzMap WholePlane ℂ,
    ∫ x : WholePlane,
        ((- ∂_{wholePlaneBasis j} φ) x) • (f x : F) ∂volume =
      ∫ x : WholePlane, φ x • (df x : F) ∂volume

/-- An integral weak-derivative identity is exactly the corresponding equality of tempered
distributions. -/
theorem wholePlane_distributionDerivative_of_integralIdentity
    [CompleteSpace F]
    {f df : WholePlaneL2 F} {j : Fin 2}
    (h : HasWholePlaneIntegralWeakDerivative f df j) :
    ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered F f) =
      wholePlaneL2ToTempered F df := by
  ext φ
  simpa only [TemperedDistribution.lineDerivOp_apply_apply,
    wholePlaneL2ToTempered_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply] using h φ

/-- Construct the repository's whole-plane `H1` graph element directly from integral weak
derivative identities. -/
def wholePlaneH1OfIntegralWeakDerivatives
    [CompleteSpace F]
    (f : WholePlaneL2 F) (df : Fin 2 → WholePlaneL2 F)
    (hdf : ∀ j : Fin 2, HasWholePlaneIntegralWeakDerivative f (df j) j) :
    WholePlaneH1 F :=
  wholePlaneH1OfWeakDerivatives F f df fun j ↦
    wholePlane_distributionDerivative_of_integralIdentity (hdf j)

/-! ## Unit-circle specialization -/

/-- The closed unit disk used to separate the interior and exterior mode formulas. -/
def wholePlaneUnitDisk : Set WholePlane := Metric.closedBall 0 1

/-- The closed unit disk of the transverse plane is measurable, being closed. -/
theorem measurableSet_wholePlaneUnitDisk : MeasurableSet wholePlaneUnitDisk :=
  Metric.isClosed_closedBall.measurableSet

/-- The unit circle, as the subtype supporting Mathlib's sphere measure. -/
abbrev WholePlaneUnitCircle := Metric.sphere (0 : WholePlane) 1

/-- Surface measure on the unit circle, obtained from planar Lebesgue measure by Mathlib's
canonical polar-coordinate construction. -/
def wholePlaneUnitCircleMeasure : Measure WholePlaneUnitCircle :=
  (volume : Measure WholePlane).toSphere

end IntegralWeakDerivative

end
end FastDynamo
