/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.LocallyConstant.Basic

/-! # Zero intrinsic differential implies constancy
The argument is carried out in actual manifold charts on convex model balls,
then connectedness propagates the resulting locally constant function.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [BoundarylessManifold I M]

/-- A differentiable scalar function with zero actual intrinsic differential is
locally constant. No global chart or product structure is assumed. -/
theorem isLocallyConstant_of_mvfderiv_eq_zero
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hzero : ∀ x, mvfderiv I f x = 0) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro x
  let e := extChartAt I x
  have htarget : interior e.target ∈ 𝓝 (e x) :=
    isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp htarget
  have hd (y : E) (hy : y ∈ Metric.ball (e x) r) :
      HasFDerivAt (f ∘ e.symm) (0 : E →L[ℝ] ℝ) y := by
    have hyinter := hball hy
    have hysource : y ∈ e.target := interior_subset hyinter
    have hrange : range I ∈ 𝓝 y := mem_of_superset
      (isOpen_interior.mem_nhds hyinter)
      (interior_subset.trans (extChartAt_target_subset_range x))
    have he : MDifferentiableAt 𝓘(ℝ, E) I e.symm y :=
      (mdifferentiableWithinAt_extChartAt_symm hysource).mdifferentiableAt hrange
    have hfx : HasMFDerivAt I 𝓘(ℝ, ℝ) f (e.symm y) 0 := by
      convert! (hf (e.symm y)).hasMFDerivAt using 1
      ext v
      exact (congrArg (fun L ↦ L v) (hzero (e.symm y))).symm
    convert! (hfx.comp y he.hasMFDerivAt).hasFDerivAt using 1
  have heq (y : E) (hy : y ∈ Metric.ball (e x) r) :
      f (e.symm y) = f (e.symm (e x)) := by
    apply (convex_ball (e x) r).is_const_of_fderivWithin_eq_zero
      (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hd z hz).hasFDerivWithinAt.fderivWithin
        (Metric.isOpen_ball.uniqueDiffOn z hz)) hy (Metric.mem_ball_self hr)
  filter_upwards [(continuousAt_extChartAt x).preimage_mem_nhds
    (Metric.ball_mem_nhds (e x) hr), extChartAt_source_mem_nhds (I := I) x] with y hy hys
  simpa [e.left_inv hys, e.left_inv (mem_extChartAt_source (I := I) x)] using heq (e y) hy

/-- On a connected manifold, zero intrinsic differential forces global constancy. -/
theorem eq_of_mvfderiv_eq_zero [PreconnectedSpace M]
    {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (hzero : ∀ x, mvfderiv I f x = 0) (x y : M) : f x = f y :=
  (isLocallyConstant_of_mvfderiv_eq_zero hf hzero).apply_eq_of_preconnectedSpace x y

end CutoffRigidity
