/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.ContinuousKH1Interpolation
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKBridge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.CenteredCubeH1Interpolation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fractional interpolation for centered-cube H1 vector fields

The scale-normalized coordinate gradient sum is invariant under pullback to
the centered unit cube.  Combining this transport with continuous
interpolation gives a quantitative Hs bound without a boundary condition.
-/

namespace HCPolySupport

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-- The represented field of a coordinatewise centered-cube H1 function,
with its Euclidean L2 certificate. -/
@[expose]
noncomputable def CubeVectorH1Function.centeredEuclideanL2Field
    {d : ℕ} {m : ℤ} (G : CubeVectorH1Function (originCube d m)) :
    CenteredCubeEuclideanL2Field d m where
  toField := G.toField
  euclideanMemL2 := by
    rw [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    rw [memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply,
      CubeVectorH1Function.toField] using
      (G.coord i).memL2_normalizedCubeMeasure

end

end HCPolySupport
