/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianCoordinateGradient
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianCoordinateKilling

/-! # Actual Christoffel formula for the Levi-Civita connection

The coordinate frame comes from actual tangent trivializations. Its brackets
vanish by the proved constant chart pullback. The actual Koszul formula then
computes the connection directly from first derivatives of the true metric.
-/
@[expose] public section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology
namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- Actual coordinate-constant frame fields commute at their chart center. -/
theorem mlieBracket_chartFrames (x : M) (u v : E) :
    mlieBracket I (chartFrame (I := I) x u) (chartFrame (I := I) x v) x=0 := by
  rw [mlieBracket_chartFrame]
  have hd : fderiv ℝ (chartCoordinateField (I := I) x (chartFrame (I := I) x u))
      (extChartAt I x x) = fderiv ℝ (fun _ : E => u) (extChartAt I x x) :=
    (chartCoordinateField_frame_eventuallyEq (I := I) x u).fderiv_eq
  rw [hd]
  simp [chartFrame,chartFrameCLM]

/-- The exact Christoffel coefficient identity derived from the actual
Levi-Civita connection and original Riemannian metric. -/
theorem leviCivita_chartFrame_inner (x : M) (u v w : E) :
    2*inner ℝ
      (CovariantDerivative.leviCivitaConnection I M (chartFrame (I := I) x v) x
        (chartFrame (I := I) x u x)) (chartFrame (I := I) x w x) =
      (fderiv ℝ (chartMetric (I := I) x) (extChartAt I x x) u) v w +
      (fderiv ℝ (chartMetric (I := I) x) (extChartAt I x x) v) w u -
      (fderiv ℝ (chartMetric (I := I) x) (extChartAt I x x) w) u v := by
  have hu := (contMDiffAt_chartFrame (I := I) x u).mdifferentiableAt one_ne_zero
  have hv := (contMDiffAt_chartFrame (I := I) x v).mdifferentiableAt one_ne_zero
  have hw := (contMDiffAt_chartFrame (I := I) x w).mdifferentiableAt one_ne_zero
  have hh := CovariantDerivative.leviCivitaConnection_apply_inner (I := I) hu hv hw
  have hdu := fderiv_chartMetric_direction x (chartFrame (I := I) x u) v w
  have hdv := fderiv_chartMetric_direction x (chartFrame (I := I) x v) w u
  have hdw := fderiv_chartMetric_direction x (chartFrame (I := I) x w) u v
  simp only [chartCoordinateField_self,chartFrame_self] at hdu hdv hdw
  simp only [mlieBracket_chartFrames,inner_zero_right,sub_zero,add_zero] at hh
  simp only [chartFrame_self] at hh ⊢
  rw [← hdu,← hdv,← hdw] at hh
  linarith

end CutoffRigidity
