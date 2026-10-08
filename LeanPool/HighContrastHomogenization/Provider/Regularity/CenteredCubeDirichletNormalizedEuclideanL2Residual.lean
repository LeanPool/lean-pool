/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeDirichletEuclideanHsDifference
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeDirichletNormalizedEuclideanL2Energy

/-!
# High-contrast homogenization:
Provider.Regularity.CenteredCubeDirichletNormalizedEuclideanL2Residual

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized Euclidean L2 residual stability for the identity Dirichlet problem

The physical normalized Euclidean `L²` endpoint is stable under subtraction:
the difference of two identity Dirichlet solution gradients is controlled by
the difference of their data with constant one.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {m : ℤ}

private theorem centeredCubeEuclideanL2Field_memLp_normalizedCubeMeasure
    (F : CenteredCubeEuclideanL2Field d m) :
    MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d m)) := by
  rw [← cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  change MemLp F (2 : ℝ≥0∞) (centeredCubeDomain d m).normalizedVolume
  apply MemLp.of_eval
  intro i
  have hF := F.euclideanMemL2
  rw [memLp_piLp_iff] at hF
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF i

/-- Two identity Dirichlet solutions are nonexpansive on differences in the
physical normalized Euclidean `L²` norm. -/
theorem centeredCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_sub_le
    (h k : CenteredCubeEuclideanL2Field d m)
    (w v : H10Function (openCubeSet (originCube d m)))
    (hw : CubeDirichletDivergenceProblem (originCube d m) w h)
    (hv : CubeDirichletDivergenceProblem (originCube d m) v k) :
    (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (fun x ↦ w.toH1Function.grad x - v.toH1Function.grad x) ≤
      (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (fun x ↦ h x - k x) := by
  have hsubProblem : CubeDirichletDivergenceProblem (originCube d m)
      (w - v) (centeredCubeEuclideanL2FieldSub h k) := by
    simpa only [centeredCubeEuclideanL2FieldSub_apply] using!
      (cubeDirichletDivergenceProblem_sub
        (centeredCubeEuclideanL2Field_memLp_normalizedCubeMeasure h)
        (centeredCubeEuclideanL2Field_memLp_normalizedCubeMeasure k) hw hv)
  have hbound :=
    centeredCubeDirichletDivergence_normalizedEuclideanLpENorm_grad_le
      (centeredCubeEuclideanL2FieldSub h k) (w - v) hsubProblem
  have hgrad :
      (centeredCubeGradientEuclideanL2Field (w - v)).toField =
        fun x ↦ w.toH1Function.grad x - v.toH1Function.grad x := by
    funext x
    change (w.toH1Function - v.toH1Function).grad x =
      w.toH1Function.grad x - v.toH1Function.grad x
    exact congrFun (H1Function.sub_grad w.toH1Function v.toH1Function) x
  have hdatum :
      (centeredCubeEuclideanL2FieldSub h k).toField =
        fun x ↦ h x - k x := by
    funext x
    exact centeredCubeEuclideanL2FieldSub_apply h k x
  change (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (centeredCubeGradientEuclideanL2Field (w - v)).toField ≤
    (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (centeredCubeEuclideanL2FieldSub h k).toField at hbound
  rw [hgrad, hdatum] at hbound
  exact hbound

end

end HighContrast
end HCPolySupport
