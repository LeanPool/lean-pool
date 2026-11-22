/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedRegularTrace

/-! # G0: regularity of the Challenge operators on smooth functions

`theorem CutCur.weightedRegular`: for smooth `V`, `Γ(f,g)` and `𝓛 f` are smooth and `‖Hess f‖²`
is smooth (hence continuous) for smooth `f, g`.
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

/-- The trace as a continuous linear form on `F →L F`. -/
noncomputable def trCLM (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] : (F →L[ℝ] F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace ℝ F).comp (ContinuousLinearMap.coeLM ℝ))

theorem trCLM_apply (L : F →L[ℝ] F) : trCLM F L = LinearMap.trace ℝ F L.toLinearMap := rfl

theorem contDiffAt_hessOp {Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    (hY : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% Y)) (x₀ : M) :
    ContDiffAt ℝ ∞ (hessOp Y x₀) (extChartAt 𝓘(ℝ, F) x₀ x₀) :=
  (contDiffAt_chartMetric_inverse x₀).clm_comp (contDiffAt_hessCoeff hY x₀)

theorem contDiffAt_hessGram {Y : (y : M) → TangentSpace 𝓘(ℝ, F) y}
    (hY : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% Y)) (x₀ : M) :
    ContDiffAt ℝ ∞ (hessGram Y x₀) (extChartAt 𝓘(ℝ, F) x₀ x₀) := by
  rw [← contDiffWithinAt_univ]
  apply contDiffWithinAt_clm_apply.mpr
  intro u
  apply contDiffWithinAt_clm_apply.mpr
  intro w
  rw [contDiffWithinAt_univ]
  have hG := contDiffAt_chartMetric (F := F) x₀
  have hO := contDiffAt_hessOp hY x₀
  have h1 : ContDiffAt ℝ ∞ (fun z => hessOp Y x₀ z u) (extChartAt 𝓘(ℝ, F) x₀ x₀) :=
    hO.clm_apply contDiffAt_const
  have h2 : ContDiffAt ℝ ∞ (fun z => hessOp Y x₀ z w) (extChartAt 𝓘(ℝ, F) x₀ x₀) :=
    hO.clm_apply contDiffAt_const
  have h3 : ContDiffAt ℝ ∞ (fun z => chartMetric (I := 𝓘(ℝ, F)) x₀ z (hessOp Y x₀ z u))
      (extChartAt 𝓘(ℝ, F) x₀ x₀) := hG.clm_apply h1
  have h4 : ContDiffAt ℝ ∞
      (fun z => chartMetric (I := 𝓘(ℝ, F)) x₀ z (hessOp Y x₀ z u) (hessOp Y x₀ z w))
      (extChartAt 𝓘(ℝ, F) x₀ x₀) := h3.clm_apply h2
  exact h4

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem contMDiffAt_of_coord {φ : M → ℝ} {Φ : F → ℝ} (x₀ : M)
    (hΦ : ContDiffAt ℝ ∞ Φ (extChartAt 𝓘(ℝ, F) x₀ x₀))
    (h : ∀ y ∈ (chartAt F x₀).source, φ y = Φ (extChartAt 𝓘(ℝ, F) x₀ y)) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ φ x₀ := by
  apply (hΦ.contMDiffAt.comp x₀
    (contMDiffAt_extChartAt (I := 𝓘(ℝ, F)) (x := x₀) (n := ∞))).congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds F x₀] with y hy
  exact h y hy

theorem trace_levi_eq' {x₀ y : M} {z : F} (h : (extChartAt 𝓘(ℝ, F) x₀).symm z = y)
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (Y : (y : M) → TangentSpace 𝓘(ℝ, F) y) :
    LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) y)
        (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Y y).toLinearMap =
      LinearMap.trace ℝ F (hessOp Y x₀ z).toLinearMap := by
  subst h; exact trace_levi_eq hz Y

theorem hessNormSq_eq' {x₀ y : M} {z : F} (h : (extChartAt 𝓘(ℝ, F) x₀).symm z = y)
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) (f : M → ℝ) :
    manifoldHessianNormSq 𝓘(ℝ, F) f y =
      LinearMap.trace ℝ F ((chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse ∘L
        hessGram (manifoldGradient 𝓘(ℝ, F) f) x₀ z).toLinearMap := by
  subst h; exact hessNormSq_eq hz f

/-- **(G0.3)** `Δ f` is smooth for smooth `f`. -/
theorem msmooth_mlaplacian {f : M → ℝ} (hf : MSmooth F f) : MSmooth F (mlaplacian F f) := by
  intro x₀
  have hY := contMDiff_mgrad hf
  apply contMDiffAt_of_coord x₀ (Φ := fun z => trCLM F (hessOp (manifoldGradient 𝓘(ℝ, F) f) x₀ z))
  · exact (trCLM F).contDiff.contDiffAt.comp _ (contDiffAt_hessOp hY x₀)
  · intro y hy
    have hys : y ∈ (extChartAt 𝓘(ℝ, F) x₀).source := by simpa only [extChartAt_source] using hy
    have hz := (extChartAt 𝓘(ℝ, F) x₀).map_source hys
    change manifoldLaplacian 𝓘(ℝ, F) f y = _
    rw [manifoldLaplacian_eq_trace, trace_levi_eq' ((extChartAt 𝓘(ℝ, F) x₀).left_inv hys) hz]
    rfl

/-- **(G0.4)** `‖Hess f‖²` is smooth (hence continuous) for smooth `f`. -/
theorem msmooth_mHessNormSq {f : M → ℝ} (hf : MSmooth F f) : MSmooth F (mHessNormSq F f) := by
  intro x₀
  have hY := contMDiff_mgrad hf
  apply contMDiffAt_of_coord x₀ (Φ := fun z => trCLM F
    ((chartMetric (I := 𝓘(ℝ, F)) x₀ z).inverse ∘L
        hessGram (manifoldGradient 𝓘(ℝ, F) f) x₀ z))
  · exact (trCLM F).contDiff.contDiffAt.comp _
      ((contDiffAt_chartMetric_inverse x₀).clm_comp (contDiffAt_hessGram hY x₀))
  · intro y hy
    have hys : y ∈ (extChartAt 𝓘(ℝ, F) x₀).source := by simpa only [extChartAt_source] using hy
    have hz := (extChartAt 𝓘(ℝ, F) x₀).map_source hys
    change manifoldHessianNormSq 𝓘(ℝ, F) f y = _
    rw [hessNormSq_eq' ((extChartAt 𝓘(ℝ, F) x₀).left_inv hys) hz]
    rfl

end CutCur.WReg

namespace CutCur

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- **(G0)** Regularity of the Challenge operators on smooth functions. -/
theorem weightedRegular (V : M → ℝ) (hV : MSmooth F V) : WeightedRegular F V :=
  ⟨fun _ _ hf hg => WReg.msmooth_carre hf hg,
   fun _ hf => (WReg.msmooth_mlaplacian hf).sub (WReg.msmooth_carre hV hf),
   fun _ hf => (WReg.msmooth_mHessNormSq hf).continuous⟩

end CutCur
