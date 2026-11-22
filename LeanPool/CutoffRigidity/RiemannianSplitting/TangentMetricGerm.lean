/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianChartMetric

/-! # Actual tangent metric pairings depend only on the germ of the map
The base-point equality and the actual manifold derivative equality are both
used; no identification of metrics at different manifold points is assumed.
-/

@[expose] public section
open Bundle Filter
open scoped Manifold Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The original point-dependent metric, with model-vector arguments used only
as a technical representation of the tangent fiber at the specified point. -/
noncomputable def tangentMetricPair (x : M) (u v : E) : ℝ :=
  inner ℝ ((tangentSpaceCastModel I x).symm u) ((tangentSpaceCastModel I x).symm v)

omit [IsManifold I 1 M] in
/-- Actual manifold maps agreeing near a point have exactly the same actual
tangent metric pairing at that point. The two image points are proved equal. -/
theorem inner_mfderiv_eq_of_eventuallyEq {f g : M → M} {x : M}
    (h : f =ᶠ[𝓝 x] g) (u v : TangentSpace I x) :
    inner ℝ ((mfderiv I I f x) u) ((mfderiv I I f x) v) =
      inner ℝ ((mfderiv I I g x) u) ((mfderiv I I g x) v) := by
  have hx : f x = g x := h.eq_of_nhds
  have hdu : (tangentSpaceCastModel I (f x)) ((mfderiv I I f x) u) =
      (tangentSpaceCastModel I (g x)) ((mfderiv I I g x) u) := by
    have hh := congrArg (fun L ↦ L u) (h.mfderiv_eq (I := I) (I' := I))
    have hc := congrArg (tangentSpaceCastModel I (f x)) hh
    convert! hc using 1
  have hdv : (tangentSpaceCastModel I (f x)) ((mfderiv I I f x) v) =
      (tangentSpaceCastModel I (g x)) ((mfderiv I I g x) v) := by
    have hh := congrArg (fun L ↦ L v) (h.mfderiv_eq (I := I) (I' := I))
    have hc := congrArg (tangentSpaceCastModel I (f x)) hh
    convert! hc using 1
  have heq₁ := congrArg (fun y : M ↦ tangentMetricPair (I := I) y
    ((tangentSpaceCastModel I (f x)) ((mfderiv I I f x) u))
    ((tangentSpaceCastModel I (f x)) ((mfderiv I I f x) v))) hx
  have heq₂ := congrArg₂ (tangentMetricPair (I := I) (g x)) hdu hdv
  have heq := heq₁.trans heq₂
  simpa only [tangentMetricPair, ContinuousLinearEquiv.symm_apply_apply] using heq

end CutoffRigidity
