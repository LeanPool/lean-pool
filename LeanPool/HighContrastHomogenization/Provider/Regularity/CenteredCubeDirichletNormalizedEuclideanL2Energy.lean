/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.FluxComparisonBridges
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeScaleTransport

/-!
# High-contrast homogenization: Provider.Regularity.CenteredCubeDirichletNormalizedEuclideanL2Energy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized Euclidean L2 energy for the identity Dirichlet problem

The sharp identity-coefficient energy endpoint is expressed here in the
normalized Euclidean `L²` norm on every physical centered cube.  The constant
remains exactly one, with no dimension or cube-volume loss.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {m : ℤ}

@[expose]
public noncomputable def centeredCubeEuclideanL2FieldAsCubeTwo
    (F : CenteredCubeEuclideanL2Field d m) :
    CubeEuclideanL2LpField (originCube d m) FiniteLpExponent.two where
  toField := F
  euclideanMemLp := by
    simpa only [FiniteLpExponent.two_exponent, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
        F.euclideanMemL2
  euclideanMemL2 := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
        F.euclideanMemL2

/-- The identity Dirichlet solution map is nonexpansive in the physical
normalized Euclidean `L²` norm. -/
theorem centeredCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_le
    [NeZero d] (h : CenteredCubeEuclideanL2Field d m)
    (w : H10Function (openCubeSet (originCube d m)))
    (hproblem : CubeDirichletDivergenceProblem (originCube d m) w h) :
    (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (centeredCubeGradientEuclideanL2Field w) ≤
      (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h := by
  let hTwo : CubeEuclideanL2LpField (originCube d m) FiniteLpExponent.two :=
    centeredCubeEuclideanL2FieldAsCubeTwo h
  have hproblemTwo :
      CubeDirichletDivergenceProblem (originCube d m) w hTwo.toField := by
    simpa only [hTwo, centeredCubeEuclideanL2FieldAsCubeTwo] using hproblem
  have hsolution :
      IsCenteredCubeH10ScalarDivergenceSolution m 1 w hTwo.toLpTwo :=
    _root_.HCPolySupport.Book.Ch03.ABK26.CubeEuclideanL2LpField.to_centeredH10DivergenceSolution
      m hTwo w hproblemTwo
  have hbound :=
    CubeCalderonZygmund.centeredCubeH10ScalarDivergence_cz_two
      m 1 hTwo w (by norm_num) hsolution
  change (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      w.toH1Function.grad ≤
    (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) h.toField
  simpa only [FiniteLpExponent.two_exponent, ENNReal.ofReal_one, inv_one,
    one_mul, hTwo, centeredCubeEuclideanL2FieldAsCubeTwo] using hbound

end

end HighContrast
end HCPolySupport
