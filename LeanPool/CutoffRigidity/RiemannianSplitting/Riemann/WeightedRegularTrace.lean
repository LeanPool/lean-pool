/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedRegularKoszul
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianDifferentialOperators

/-! # G0 (part 3): trace formulas in a chart frame

For `z` in the chart target, the Laplacian `tr ∇Y` and the Hessian norm `tr (∇Y)^*(∇Y)` of the
Levi-Civita derivative at `e.symm z` are `tr (G⁻¹ K)` and `tr (G⁻¹ P)` in terms of the chart metric
`G = chartMetric x₀ z` and the coefficients `K = hessCoeff Y x₀ z`.
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

/-- The continuous inverse of the chart frame at `y`. -/
noncomputable def chartFrameInv (x₀ y : M) : TangentSpace 𝓘(ℝ, F) y →L[ℝ] F :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt ℝ y

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartFrame_chartFrameInv {x₀ y : M} (hy : y ∈ (chartAt F x₀).source)
    (v : TangentSpace 𝓘(ℝ, F) y) :
    chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y (chartFrameInv x₀ y v) = v :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).symmL_continuousLinearMapAt
    (mem_baseSet_of_mem_source (F := F) hy) v

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartFrameInv_chartFrame {x₀ y : M} (hy : y ∈ (chartAt F x₀).source) (u : F) :
    chartFrameInv x₀ y (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y u) = u :=
  (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x₀).continuousLinearMapAt_symmL
    (mem_baseSet_of_mem_source (F := F) hy) u

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mem_source_of_mem_target {x₀ : M} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    (extChartAt 𝓘(ℝ, F) x₀).symm z ∈ (chartAt F x₀).source := by
  simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, F) x₀).map_target hz

/-- Coordinate expression `G⁻¹ K` of the Levi-Civita derivative of `Y`. -/
noncomputable def hessOp (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x₀ : M) (z : F) : F →L[ℝ] F :=
  (chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse ∘L hessCoeff Y x₀ z

/-- Coordinate expression of the Gram form of the Levi-Civita derivative. -/
noncomputable def hessGram (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x₀ : M) (z : F) :
    F →L[ℝ] F →L[ℝ] ℝ :=
  (chartMetric (I := 𝓘(ℝ, F)) x₀ z).bilinearComp (hessOp Y x₀ z) (hessOp Y x₀ z)

theorem trace_conj_aux {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : F →ₗ[ℝ] V) (S : V →ₗ[ℝ] F) (hTS : T ∘ₗ S = LinearMap.id) (A : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ F (S ∘ₗ A ∘ₗ T) = LinearMap.trace ℝ V A := by
  have := LinearMap.trace_comp_comm' (R := ℝ) (A ∘ₗ T) S
  rw [LinearMap.comp_assoc] at this
  rw [this, hTS]
  simp

theorem chartFrameInv_comp_hessOp_eq {x₀ : M} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) :
    chartFrameInv x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z) ∘L
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y
          ((extChartAt 𝓘(ℝ, F) x₀).symm z)) ∘L
        chartFrameCLM (I := 𝓘(ℝ, F)) x₀ ((extChartAt 𝓘(ℝ, F) x₀).symm z) = hessOp Y x₀ z := by
  have hy := mem_source_of_mem_target (x₀ := x₀) hz
  ext u
  symm
  apply (chartMetric_isInvertible_of_mem_target (I := 𝓘(ℝ, F)) x₀ hz).inverse_apply_eq.mpr
  ext w
  rw [chartMetric_apply]
  change hessCoeff Y x₀ z u w = _
  rw [hessCoeff_apply]
  simp only [ContinuousLinearMap.comp_apply]
  change _ = inner ℝ (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _ (chartFrameInv x₀ _ (_ ))) _
  rw [chartFrame_chartFrameInv hy]
  rfl

theorem trace_levi_eq {x₀ : M} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) :
    LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) ((extChartAt 𝓘(ℝ, F) x₀).symm z))
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y
          ((extChartAt 𝓘(ℝ, F) x₀).symm z)).toLinearMap =
      LinearMap.trace ℝ F (hessOp Y x₀ z).toLinearMap := by
  have hy := mem_source_of_mem_target (x₀ := x₀) hz
  rw [← chartFrameInv_comp_hessOp_eq hz Y]
  exact (trace_conj_aux (chartFrameCLM (I := 𝓘(ℝ, F)) x₀ _).toLinearMap
    (chartFrameInv x₀ _).toLinearMap (by ext v; exact chartFrame_chartFrameInv hy v) _).symm

theorem hessNormSq_eq {x₀ : M} {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (f : M → ℝ) :
    manifoldHessianNormSq 𝓘(ℝ, F) f ((extChartAt 𝓘(ℝ, F) x₀).symm z) =
      LinearMap.trace ℝ F ((chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse ∘L
        hessGram (manifoldGradient 𝓘(ℝ, F) f) x₀ z).toLinearMap := by
  let y := (extChartAt 𝓘(ℝ, F) x₀).symm z
  let frame := chartFrameCLM (I := 𝓘(ℝ, F)) x₀ y
  let inverse := chartFrameInv (F := F) x₀ y
  let gradient := manifoldGradient 𝓘(ℝ, F) f
  let derivative := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M gradient y
  let metric := chartMetric (I := 𝓘(ℝ, F)) x₀ z
  have hy := mem_source_of_mem_target (x₀ := x₀) hz
  have roundTrip (v : TangentSpace 𝓘(ℝ, F) y) : frame (inverse v) = v :=
    chartFrame_chartFrameInv hy v
  have htrace := trace_conj_aux frame.toLinearMap inverse.toLinearMap
    (by ext v; exact roundTrip v) (derivative.adjoint.comp derivative).toLinearMap
  rw [manifoldHessianNormSq_eq_trace_adjoint]
  change LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) y)
    (derivative.adjoint.comp derivative).toLinearMap = _
  rw [← htrace]
  congr 1
  suffices h : inverse ∘L (derivative.adjoint.comp derivative) ∘L frame =
      metric.inverse ∘L hessGram gradient x₀ z from
    congrArg ContinuousLinearMap.toLinearMap h
  have hcoord := chartFrameInv_comp_hessOp_eq hz gradient
  have hcoord_apply (u : F) : hessOp gradient x₀ z u = inverse (derivative (frame u)) :=
    (ContinuousLinearMap.ext_iff.mp hcoord u).symm
  ext u
  symm
  apply (chartMetric_isInvertible_of_mem_target (I := 𝓘(ℝ, F)) x₀ hz).inverse_apply_eq.mpr
  ext w
  change metric (hessOp gradient x₀ z u) (hessOp gradient x₀ z w) =
    metric (inverse (derivative.adjoint (derivative (frame u)))) w
  rw [hcoord_apply, hcoord_apply]
  have hmetric (a b : F) : metric a b = inner ℝ (frame a) (frame b) :=
    chartMetric_apply (I := 𝓘(ℝ, F)) x₀ z a b
  rw [hmetric, hmetric, roundTrip, roundTrip, roundTrip, ContinuousLinearMap.adjoint_inner_left]

end CutCur.WReg
