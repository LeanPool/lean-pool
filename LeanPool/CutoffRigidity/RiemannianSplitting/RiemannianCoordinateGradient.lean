/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianMetricSharp
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldScalarChartDerivative

/-! # Coordinate gradient from the actual inverse metric

The coordinate expression is constructed from the actual chart differential
and inverse metric. Its C¹ regularity follows from source C² regularity and
true inverse-metric regularity. At the chart center it equals the genuine
Riesz gradient, rather than a supplied vector-field representative.
-/
@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology
namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]

/-- The gradient in the local frame, obtained by inverting the chart metric. -/
noncomputable def coordinateRiemannianGradient (f : M → ℝ) (x : M) (z : E) : E :=
  (chartMetric (I := I) x z).inverse (fderiv ℝ (f ∘ (extChartAt I x).symm) z)

/-- Actual C¹ coordinate coefficients, with no regularity premise on a
putative gradient vector field. -/
theorem contDiffAt_coordinateRiemannianGradient {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) :
    ContDiffAt ℝ 1 (coordinateRiemannianGradient (I := I) f x) (extChartAt I x x) := by
  have htarget : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    mem_of_superset (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x)))) interior_subset
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I x).symm (extChartAt I x x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt htarget
  have hfc : ContDiffAt ℝ 2 (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    ((hf x).comp_of_eq hsymm (extChartAt_to_inv x)).contDiffAt
  exact (contDiffAt_chartMetric_inverse (I := I) x).clm_apply
    (hfc.fderiv_right (by norm_num))

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x] in
/-- Identification with the intrinsic Riesz gradient at the chart center. -/
theorem coordinateRiemannianGradient_center {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    coordinateRiemannianGradient (I := I) f x (extChartAt I x x) = manifoldGradient I f x := by
  apply (chartMetric_isInvertible (I := I) x).inverse_apply_eq.mpr
  ext v
  let coordinates : E := manifoldGradient I f x
  change _ = chartMetric (I := I) x (extChartAt I x x) coordinates v
  have center : chartFrame (I := I) x coordinates x = manifoldGradient I f x :=
    chartFrame_self _ _
  rw [chartMetric_center_apply (I := I) x coordinates v, center, inner_manifoldGradient]
  simpa only [chartCoordinateField_self, chartFrame_self] using
    fderiv_chartScalar_direction x hf (chartFrame (I := I) x v)

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The scalar derivative in an arbitrary point of the actual chart is the
intrinsic differential applied to the actual chart frame. -/
theorem fderiv_chartScalar_frame (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I x₀).symm z)) (v : E) :
    fderiv ℝ (f ∘ (extChartAt I x₀).symm) z v =
      mvfderiv I f ((extChartAt I x₀).symm z)
        (chartFrame (I := I) x₀ v ((extChartAt I x₀).symm z)) := by
  let e := extChartAt I x₀
  let y := e.symm z
  have hy : y ∈ (chartAt H x₀).source := by
    simpa only [y,e,extChartAt_source] using e.map_target hz
  have hround : e y=z := e.right_inv hz
  have hRange : range I ∈ 𝓝 z := by
    rw [← hround]
    have ht := (I.isInteriorPoint_iff_of_mem_atlas (by norm_num : (2 : ℕ∞ω) ≠ 0)
      (chart_mem_atlas H x₀) hy).mp
        (BoundarylessManifold.isInteriorPoint (I := I) (x := y))
    have hi : e y ∈ interior (range I) :=
      OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ ht
    exact mem_of_superset (isOpen_interior.mem_nhds hi) interior_subset
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I e.symm z :=
    (mdifferentiableWithinAt_extChartAt_symm hz).mdifferentiableAt hRange
  have hframe : chartFrame (I := I) x₀ v y = mfderiv 𝓘(ℝ, E) I e.symm z v := by
    unfold chartFrame chartFrameCLM
    rw [TangentBundle.symmL_trivializationAt hy,hround,mfderivWithin_of_mem_nhds hRange]
    rfl
  rw [hframe]
  have derivative := mvfderiv_comp_apply z hf hsymm v
  rw [mvfderiv_eq_fderiv] at derivative
  exact derivative

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [FiniteDimensional ℝ E]
  [BoundarylessManifold I M]
  [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The chart frame applied to the actual chart vector coordinates recovers
the original tangent vector. -/
theorem chartFrame_chartCoordinateField (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) (X : (x : M) → TangentSpace I x) :
    chartFrame (I := I) x₀ (chartCoordinateField (I := I) x₀ X z)
      ((extChartAt I x₀).symm z) = X ((extChartAt I x₀).symm z) := by
  let e := extChartAt I x₀
  have hy : e.symm z ∈ (chartAt H x₀).source := by
    simpa only [e,extChartAt_source] using e.map_target hz
  unfold chartFrame chartFrameCLM chartCoordinateField
  rw [TangentBundle.symmL_trivializationAt hy,e.right_inv hz]
  change (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) z)
    ((mfderivWithin 𝓘(ℝ, E) I e.symm (range I) z).inverse (X (e.symm z))) = _
  exact ((isInvertible_mfderivWithin_extChartAt_symm (I := I) hz).inverse_apply_eq.mp rfl).symm

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x]
  [BoundarylessManifold I M] in
theorem chartMetric_isInvertible_of_mem_target (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    (chartMetric (I := I) x₀ z).IsInvertible := by
  apply metricMap_isInvertible
  intro v hv
  rw [chartMetric_apply]
  apply real_inner_self_pos.mpr
  intro hh
  apply hv
  have hy : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    simpa only [extChartAt_source] using (extChartAt I x₀).map_target hz
  let t := trivializationAt E (TangentSpace I) x₀
  have hyt : (extChartAt I x₀).symm z ∈ t.baseSet := by simpa [t] using hy
  have he := congrArg (t.continuousLinearMapAt ℝ ((extChartAt I x₀).symm z)) hh
  change t.continuousLinearMapAt ℝ ((extChartAt I x₀).symm z)
    (t.symmL ℝ ((extChartAt I x₀).symm z) v) = _ at he
  rw [t.continuousLinearMapAt_symmL hyt,map_zero] at he
  exact he

omit [IsContMDiffRiemannianBundle I 1 E fun x : M ↦ TangentSpace I x] in
/-- The C¹ coordinate coefficients are the coordinates of the actual Riesz
gradient throughout the chart, not just at its center. -/
theorem coordinateRiemannianGradient_eq_chartCoordinateField (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I x₀).symm z)) :
    coordinateRiemannianGradient (I := I) f x₀ z =
      chartCoordinateField (I := I) x₀ (manifoldGradient I f) z := by
  apply (chartMetric_isInvertible_of_mem_target (I := I) x₀ hz).inverse_apply_eq.mpr
  ext v
  rw [chartMetric_apply,chartFrame_chartCoordinateField x₀ hz,inner_manifoldGradient]
  exact fderiv_chartScalar_frame x₀ hz hf v

/-- Source C² regularity of a scalar function and C¹ regularity of the metric
produce C¹ regularity of its actual intrinsic gradient section. -/
theorem contMDiff_manifoldGradient {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) :
    ContMDiff I I.tangent 1 (T% (manifoldGradient I f)) := by
  intro x
  rw [contMDiffAt_section_iff]
  have hc := (contDiffAt_coordinateRiemannianGradient (I := I) hf x).contMDiffAt.comp x
    (contMDiffAt_extChartAt (I := I) (x := x) (n := 1))
  apply hc.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds H x] with y hy
  let e := extChartAt I x
  have hys : y ∈ e.source := by simpa only [e,extChartAt_source] using hy
  have hz : e y ∈ e.target := e.map_source hys
  have hfy : MDifferentiableAt I 𝓘(ℝ, ℝ) f (e.symm (e y)) := by
    simpa only [e.left_inv hys] using (hf y).mdifferentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hcoord := coordinateRiemannianGradient_eq_chartCoordinateField (I := I) x hz hfy
  have hframe := chartFrame_chartCoordinateField (I := I) x hz (manifoldGradient I f)
  rw [← hcoord,e.left_inv hys] at hframe
  let t := trivializationAt E (TangentSpace I) x
  have hyt : y ∈ t.baseSet := by simpa [t] using hy
  have he := congrArg (t.continuousLinearMapAt ℝ y) hframe
  change t.continuousLinearMapAt ℝ y
    (t.symmL ℝ y (coordinateRiemannianGradient (I := I) f x (e y))) = _ at he
  rw [t.continuousLinearMapAt_symmL hyt] at he
  change (trivializationAt E (TangentSpace I) x ⟨y,manifoldGradient I f y⟩).2 = _
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hyt]
  exact he.symm

end CutoffRigidity
