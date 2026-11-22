/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartFrames

/-! # Actual metric coefficients in actual manifold coordinates
The coefficient bilinear form is the original Riemannian inner product applied
to the actual inverse tangent trivialization. Its C¹ regularity follows from
actual smooth sections and the actual smooth bundle metric.
-/

@[expose] public section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The original metric in the genuine chart frame; no flat metric is
substituted for the Riemannian metric. -/
noncomputable def chartMetric (x₀ : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let y := (extChartAt I x₀).symm z
  (innerSL ℝ (E := TangentSpace I y)).bilinearComp
    (chartFrameCLM (I := I) x₀ y) (chartFrameCLM (I := I) x₀ y)

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [BoundarylessManifold I M] in
theorem chartMetric_apply (x₀ : M) (z u v : E) :
    chartMetric (I := I) x₀ z u v =
      inner ℝ (chartFrame (I := I) x₀ u ((extChartAt I x₀).symm z))
        (chartFrame (I := I) x₀ v ((extChartAt I x₀).symm z)) := rfl

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [BoundarylessManifold I M] in
/-- At its chart center, the coefficient form is the original inner product
of the actual coordinate frame vectors at that point. -/
theorem chartMetric_center_apply (x₀ : M) (u v : E) :
    chartMetric (I := I) x₀ (extChartAt I x₀ x₀) u v =
      inner ℝ (chartFrame (I := I) x₀ u x₀) (chartFrame (I := I) x₀ v x₀) := by
  rw [chartMetric_apply]
  exact congrArg (fun y : M ↦ inner ℝ (chartFrame (I := I) x₀ u y)
    (chartFrame (I := I) x₀ v y)) (extChartAt_to_inv (I := I) x₀)

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
/-- The actual scalar Gram functions of chart-constant sections are C¹. -/
theorem contMDiffAt_chartFrame_inner (x₀ : M) (u v : E) :
    ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ inner ℝ (chartFrame (I := I) x₀ u y) (chartFrame (I := I) x₀ v y)) x₀ :=
  ContMDiffAt.inner_bundle (E := TangentSpace I)
    (contMDiffAt_chartFrame (I := I) x₀ u) (contMDiffAt_chartFrame (I := I) x₀ v)

/-- The original Riemannian metric has genuinely C¹ bilinear coefficients
near the chart center, proved by actual bundle and manifold calculus. -/
theorem contDiffAt_chartMetric (x₀ : M) :
    ContDiffAt ℝ 1 (chartMetric (I := I) x₀) (extChartAt I x₀ x₀) := by
  have htarget : (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀) :=
    mem_of_superset (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)))) interior_subset
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I x₀).symm
      (extChartAt I x₀ x₀) := (contMDiffOn_extChartAt_symm x₀).contMDiffAt htarget
  rw [← contDiffWithinAt_univ]
  apply contDiffWithinAt_clm_apply.mpr
  intro u
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have hinner := (contMDiffAt_chartFrame_inner (I := I) x₀ u v).comp_of_eq hsymm
    (extChartAt_to_inv x₀)
  have hreal := hinner.contDiffAt.contDiffWithinAt (s := univ)
  simpa only [Function.comp_def, chartMetric_apply] using hreal

end CutoffRigidity
