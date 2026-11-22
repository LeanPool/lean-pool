/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface
import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-! # Riemannian distance in charts, with sharp local constants
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal Topology


namespace CutCur

section ChartLip

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

include F

/-- The trivialization of the tangent bundle at `p`, inverse map at the point `y`. -/
noncomputable abbrev symmAt (p y : M) : F →L[ℝ] TangentSpace 𝓘(ℝ, F) y :=
  (trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p).symmL ℝ y

omit [FiniteDimensional ℝ F] in
theorem eventually_symmAt_norm (p : M) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 p, y ∈ (chartAt F p).source ∧
      (∀ w, ‖symmAt F p y w‖ ≤ r * ‖symmAt F p p w‖) ∧
      (∀ w, ‖symmAt F p p w‖ ≤ r * ‖symmAt F p y w‖) := by
  let : IsContinuousRiemannianBundle F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := 𝓘(ℝ, F)) (n := ∞)
  filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt F
      (fun x : M => TangentSpace 𝓘(ℝ, F) x) p hr,
    eventually_norm_symmL_trivializationAt_self_comp_lt F
      (fun x : M => TangentSpace 𝓘(ℝ, F) x) p hr, chart_source_mem_nhds F p] with y h1 h2 h3
  refine ⟨h3, fun w => ?_, fun w => ?_⟩
  · have hp : p ∈ (trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' p
    set T := trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p
    have e : T.continuousLinearMapAt ℝ p (T.symmL ℝ p w) = w :=
      Trivialization.continuousLinearMapAt_symmL _ hp w
    have key := ContinuousLinearMap.le_opNorm ((T.symmL ℝ y) ∘L (T.continuousLinearMapAt ℝ p))
      (T.symmL ℝ p w)
    rw [ContinuousLinearMap.comp_apply, e] at key
    exact key.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))
  · have hy : y ∈ (trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p).baseSet := by
      simpa using h3
    set T := trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p
    have e : T.continuousLinearMapAt ℝ y (T.symmL ℝ y w) = w :=
      Trivialization.continuousLinearMapAt_symmL _ hy w
    have key := ContinuousLinearMap.le_opNorm ((T.symmL ℝ p) ∘L (T.continuousLinearMapAt ℝ y))
      (T.symmL ℝ y w)
    rw [ContinuousLinearMap.comp_apply, e] at key
    exact key.trans (mul_le_mul_of_nonneg_right h2.le (norm_nonneg _))

variable [IsRiemannianManifold 𝓘(ℝ, F) M]

omit [FiniteDimensional ℝ F]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
/-- Sharp local Lipschitz bound of the inverse extended chart, for the Riemannian distance. -/
theorem edist_extChartAt_symm_le (p : M) {r R : ℝ} (_hr : 0 ≤ r)
    (hRt : Metric.ball (extChartAt 𝓘(ℝ, F) p p) R ⊆ (extChartAt 𝓘(ℝ, F) p).target)
    (hgood : ∀ ζ ∈ Metric.ball (extChartAt 𝓘(ℝ, F) p p) R, ∀ w,
      ‖symmAt F p ((extChartAt 𝓘(ℝ, F) p).symm ζ) w‖ ≤ r * ‖symmAt F p p w‖)
    {b b' : F} (hb : b ∈ Metric.ball (extChartAt 𝓘(ℝ, F) p p) R)
    (hb' : b' ∈ Metric.ball (extChartAt 𝓘(ℝ, F) p p) R) :
    edist ((extChartAt 𝓘(ℝ, F) p).symm b) ((extChartAt 𝓘(ℝ, F) p).symm b') ≤
      ENNReal.ofReal (r * ‖symmAt F p p (b' - b)‖) := by
  let chart := extChartAt 𝓘(ℝ, F) p
  have on_segment : segment ℝ b b' ⊆ Metric.ball (chart p) R :=
    (convex_ball _ _).segment_subset hb hb'
  have in_target : segment ℝ b b' ⊆ chart.target := on_segment.trans hRt
  refine TauCeti.IsRiemannianManifold.edist_le_of_norm_mfderiv_le
    (I := 𝓘(ℝ, F)) (f := chart.symm) ?_ ?_
  · intro z hz
    exact ((contMDiffOn_extChartAt_symm p) z (in_target hz)).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (in_target hz))
  · intro z hz
    have in_source : chart.symm z ∈ (chartAt F p).source := by
      simpa only [chart, extChartAt_source] using chart.map_target (in_target hz)
    have derivative : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) chart.symm z =
        symmAt F p (chart.symm z) := by
      rw [symmAt, TangentBundle.symmL_trivializationAt in_source]
      rw [show extChartAt 𝓘(ℝ, F) p (chart.symm z) = z from chart.right_inv (in_target hz)]
      rw [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ]
    rw [derivative]
    exact hgood z (on_segment hz) (b' - b)

end ChartLip

end CutCur
