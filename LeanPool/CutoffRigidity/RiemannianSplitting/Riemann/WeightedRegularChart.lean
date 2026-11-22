/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianCoordinateGradient
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldScalarChartDerivative

/-! # G0 (part 1): smooth chart frames, metric coefficients and Riesz gradient

Order-`∞` versions of the chart-frame / chart-metric / coordinate-gradient arguments of
`RiemannianChartFrames`, `RiemannianChartMetric`, `RiemannianCoordinateGradient`
(which are hard-wired to orders `1` and `2`).
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutCur.WReg


variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

open CutoffRigidity

/-- Coordinates of a section in the actual chart trivialization at `x₀`. -/
noncomputable def coord (x₀ : M) (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (y : M) : F :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀ ⟨y, Y y⟩).2

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mem_baseSet_of_mem_source {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) :
    y ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).baseSet := by simpa using hy

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartFrame_coord {x₀ y : M} (hy : y ∈ (chartAt F x₀).source)
    (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) :
    chartFrame (I := 𝓘(ℝ, F)) x₀ (coord x₀ Y y) y = Y y := by
  have hyt := mem_baseSet_of_mem_source (F := F) hy
  unfold chartFrame chartFrameCLM coord
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hyt]
  exact (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).symmL_continuousLinearMapAt hyt (Y y)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem coord_chartFrame {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u : F) :
    coord x₀ (chartFrame (I := 𝓘(ℝ, F)) x₀ u) y = u := by
  have hyt := mem_baseSet_of_mem_source (F := F) hy
  unfold coord
  change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀ ⟨y, chartFrame (I := 𝓘(ℝ, F)) x₀ u y⟩).2 = _
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hyt]
  exact (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL hyt u

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem contMDiffAt_coord {x₀ y : M} (hy : y ∈ (chartAt F x₀).source)
    {Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    (hY : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% Y) y) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (coord x₀ Y) y :=
  ((trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).contMDiffAt_section_iff
    (mem_baseSet_of_mem_source (F := F) hy)).mp hY

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem contMDiffAt_section_of_coord {x₀ y : M} (hy : y ∈ (chartAt F x₀).source)
    {W : M → F} (hW : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ W y) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞
      (T% (fun y' => chartFrame (I := 𝓘(ℝ, F)) x₀ (W y') y')) y := by
  rw [(trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).contMDiffAt_section_iff
    (mem_baseSet_of_mem_source (F := F) hy)]
  apply hW.congr_of_eventuallyEq
  filter_upwards [(chartAt F x₀).open_source.mem_nhds hy] with y' hy'
  have hyt := mem_baseSet_of_mem_source (F := F) hy'
  change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀
    ⟨y', chartFrame (I := 𝓘(ℝ, F)) x₀ (W y') y'⟩).2 = W y'
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hyt]
  exact (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL hyt (W y')

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem contMDiffAt_chartFrame' {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u : F) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% (chartFrame (I := 𝓘(ℝ, F)) x₀ u)) y :=
  contMDiffAt_section_of_coord hy (contMDiffAt_const (c := u))

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem extChartAt_target_mem_nhds (x₀ : M) :
    (extChartAt 𝓘(ℝ, F) x₀).target ∈ 𝓝 (extChartAt 𝓘(ℝ, F) x₀ x₀) :=
  mem_of_superset (isOpen_interior.mem_nhds ((𝓘(ℝ, F).isInteriorPoint_iff).mp
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, F)) (x := x₀)))) interior_subset

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem contMDiffAt_extChartAt_symm (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (extChartAt 𝓘(ℝ, F) x₀).symm z := by
  have : (extChartAt 𝓘(ℝ, F) x₀).target ∈ 𝓝 z := (isOpen_extChartAt_target x₀).mem_nhds hz
  exact (contMDiffOn_extChartAt_symm x₀).contMDiffAt this

omit [FiniteDimensional ℝ F] in
theorem contMDiffAt_chartFrame_inner {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u v : F) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      (fun y' => inner ℝ (chartFrame (I := 𝓘(ℝ, F)) x₀ u y')
        (chartFrame (I := 𝓘(ℝ, F)) x₀ v y')) y :=
  ContMDiffAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F))
    (contMDiffAt_chartFrame' hy u) (contMDiffAt_chartFrame' hy v)

theorem contDiffAt_chartMetric (x₀ : M) :
    ContDiffAt ℝ ∞ (chartMetric (I := 𝓘(ℝ, F)) x₀) (extChartAt 𝓘(ℝ, F) x₀ x₀) := by
  have hsymm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (extChartAt 𝓘(ℝ, F) x₀).symm
      (extChartAt 𝓘(ℝ, F) x₀ x₀) :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt (extChartAt_target_mem_nhds x₀)
  rw [← contDiffWithinAt_univ]
  apply contDiffWithinAt_clm_apply.mpr
  intro u
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have hinner := (contMDiffAt_chartFrame_inner (x₀ := x₀) (y := x₀) (mem_chart_source F x₀)
    u v).comp_of_eq hsymm (extChartAt_to_inv x₀)
  have hreal := hinner.contDiffAt.contDiffWithinAt (s := univ)
  simpa only [Function.comp_def, chartMetric_apply] using hreal

theorem contDiffAt_chartMetric_inverse (x₀ : M) :
    ContDiffAt ℝ ∞ (fun z => (chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse)
      (extChartAt 𝓘(ℝ, F) x₀ x₀) :=
  (chartMetric_isInvertible (I := 𝓘(ℝ, F)) x₀).contDiffAt_map_inverse.comp _
    (contDiffAt_chartMetric x₀)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem contDiffAt_comp_extChartAt_symm {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f)
    (x₀ : M) : ContDiffAt ℝ ∞ (f ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) (extChartAt 𝓘(ℝ, F) x₀ x₀) :=
  ((hf x₀).comp_of_eq ((contMDiffOn_extChartAt_symm x₀).contMDiffAt
    (extChartAt_target_mem_nhds x₀)) (extChartAt_to_inv x₀)).contDiffAt

theorem contDiffAt_coordinateRiemannianGradient {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ContDiffAt ℝ ∞ (coordinateRiemannianGradient (I := 𝓘(ℝ, F)) f x)
      (extChartAt 𝓘(ℝ, F) x x) :=
  (contDiffAt_chartMetric_inverse x).clm_apply
    ((contDiffAt_comp_extChartAt_symm hf x).fderiv_right (m := ∞) (by simp))

/-- **(G0.1)** The Riesz gradient of a smooth function is a smooth section. -/
theorem contMDiff_manifoldGradient_top {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞
      (T% (manifoldGradient (𝓘(ℝ, F)) f)) := by
  intro x
  rw [contMDiffAt_section_iff]
  have hc := (contDiffAt_coordinateRiemannianGradient hf x).contMDiffAt.comp x
    (contMDiffAt_extChartAt (I := 𝓘(ℝ, F)) (x := x) (n := ∞))
  apply hc.congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds F x] with y hy
  let e := extChartAt 𝓘(ℝ, F) x
  have hys : y ∈ e.source := by simpa only [e, extChartAt_source] using hy
  have hz : e y ∈ e.target := e.map_source hys
  have hfy : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f (e.symm (e y)) := by
    simpa only [e.left_inv hys] using (hf y).mdifferentiableAt (by simp)
  have hcoord := coordinateRiemannianGradient_eq_chartCoordinateField (I := 𝓘(ℝ, F)) x hz hfy
  have hframe := chartFrame_chartCoordinateField (I := 𝓘(ℝ, F)) x hz
    (manifoldGradient (𝓘(ℝ, F)) f)
  rw [← hcoord, e.left_inv hys] at hframe
  let t := trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
  have hyt : y ∈ t.baseSet := by simpa [t] using hy
  have he := congrArg (t.continuousLinearMapAt ℝ y) hframe
  change t.continuousLinearMapAt ℝ y
    (t.symmL ℝ y (coordinateRiemannianGradient (I := 𝓘(ℝ, F)) f x (e y))) = _ at he
  rw [t.continuousLinearMapAt_symmL hyt] at he
  change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x ⟨y, manifoldGradient (𝓘(ℝ, F)) f y⟩).2 = _
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hyt]
  exact he.symm

theorem contMDiff_mgrad {f : M → ℝ} (hf : MSmooth F f) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% (mgrad F f)) :=
  contMDiff_manifoldGradient_top hf

/-- **(G0.2)** `Γ(f,g)` is smooth for smooth `f,g`. -/
theorem msmooth_carre {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) :
    MSmooth F (carre F f g) :=
  ContMDiff.inner_bundle (E := TangentSpace 𝓘(ℝ, F)) (contMDiff_mgrad hf) (contMDiff_mgrad hg)

end CutCur.WReg
