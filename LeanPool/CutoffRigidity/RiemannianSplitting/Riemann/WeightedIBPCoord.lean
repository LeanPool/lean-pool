/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPLocal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Coordinate expressions of `Γ` and `𝓛`

In the chart `chartAt F x₀`, with `Yc = chartCoordinateField x₀ (∇ v)` and
`ρ = e^{-V∘φ⁻¹} · D`:
`Γ(u,v) = d(u∘φ⁻¹)(Yc)` and `ρ · 𝓛v = d ρ (Yc) + ρ · tr (d Yc) = tr d(ρ Yc)`.
-/

@[expose] public section
open Bundle Set Filter VectorField
open scoped Manifold ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace CutoffRigidity

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) 2 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- Coordinate formula for the carré du champ. -/
theorem inner_manifoldGradient_chart (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) {u v : M → ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) u ((extChartAt 𝓘(ℝ, F) x₀).symm z)) :
    inner ℝ (manifoldGradient 𝓘(ℝ, F) u ((extChartAt 𝓘(ℝ, F) x₀).symm z))
        (manifoldGradient 𝓘(ℝ, F) v ((extChartAt 𝓘(ℝ, F) x₀).symm z)) =
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) z
        (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ (manifoldGradient 𝓘(ℝ, F) v) z) := by
  have h := chartFrame_chartCoordinateField (I := 𝓘(ℝ, F)) x₀ hz (manifoldGradient 𝓘(ℝ, F) v)
  rw [← h, inner_manifoldGradient]
  exact (fderiv_chartScalar_frame x₀ hz hu _).symm

/-- The weight `ρ = e^{-V∘φ⁻¹} · D` in the chart `φ = extChartAt x₀`. -/
noncomputable def chartWeight (x₀ : M) (V : M → ℝ) (w : F) : ℝ :=
  Real.exp (-V ((extChartAt 𝓘(ℝ, F) x₀).symm w)) *
    chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀ w

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem contMDiffAt_symm_two (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) 2 (extChartAt 𝓘(ℝ, F) x₀).symm z :=
  (contMDiffOn_extChartAt_symm x₀).contMDiffAt (extChartAt_target_nhds hz)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem contDiffAt_comp_symm (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 f) :
    ContDiffAt ℝ 2 (f ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) z :=
  ((hf _).comp z (contMDiffAt_symm_two x₀ hz)).contDiffAt

theorem chartWeight_hasFDerivAt (x₀ : M) {z : F} (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target)
    {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 V) :
    ContDiffAt ℝ 1 (chartWeight x₀ V) z := by
  have h1 : ContDiffAt ℝ 1 (V ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) z :=
    (contDiffAt_comp_symm x₀ hz hV).of_le (by norm_num)
  have h2 := (contDiffAt_chartRiemannianVolumeDensity_target x₀ hz)
  exact h1.neg.exp.mul h2

/-- `ρ · 𝓛v = d ρ (Yc) + ρ · tr d Yc` in the chart. -/
theorem chartWeight_mul_generator (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) {V v : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 V) (hv : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 v) :
    chartWeight x₀ V z * manifoldLangevinOperator 𝓘(ℝ, F) V v ((extChartAt 𝓘(ℝ, F) x₀).symm z) =
      fderiv ℝ (chartWeight x₀ V) z
          (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ (manifoldGradient 𝓘(ℝ, F) v) z) +
        chartWeight x₀ V z * LinearMap.trace ℝ F
          (fderiv ℝ (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ (manifoldGradient 𝓘(ℝ, F) v))
              z).toLinearMap := by
  set y := (extChartAt 𝓘(ℝ, F) x₀).symm z with hy
  set Yc := chartCoordinateField (I := 𝓘(ℝ, F)) x₀ (manifoldGradient 𝓘(ℝ, F) v) with hYc
  have hgrad : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent (T% (manifoldGradient 𝓘(ℝ, F) v)) y :=
    ((contMDiff_manifoldGradient (I := 𝓘(ℝ, F)) hv) y).mdifferentiableAt one_ne_zero
  have hVm : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) V y := (hV y).mdifferentiableAt (by norm_num)
  have hL := chartRiemannianVolumeDensity_mul_trace x₀ hz hgrad
  have hcar := inner_manifoldGradient_chart (v := v) x₀ hz hVm
  have hVd : HasFDerivAt (V ∘ (extChartAt 𝓘(ℝ, F) x₀).symm)
      (fderiv ℝ (V ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) z) z :=
    ((contDiffAt_comp_symm x₀ hz hV).differentiableAt (by norm_num)).hasFDerivAt
  have hDd := ((contDiffAt_chartRiemannianVolumeDensity_target x₀ hz).differentiableAt
    one_ne_zero).hasFDerivAt
  have hW := (hVd.neg.exp).mul hDd
  have hfd : fderiv ℝ (chartWeight x₀ V) z = _ := hW.fderiv
  rw [hfd]
  have hlap : manifoldLangevinOperator 𝓘(ℝ, F) V v y = LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, F) y)
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (manifoldGradient 𝓘(ℝ, F) v)
          y).toLinearMap
        - fderiv ℝ (V ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) z (Yc z) := by
    rw [manifoldLangevinOperator, manifoldLaplacian_eq_trace, hcar]
  rw [hlap]
  simp only [chartWeight, add_apply, smul_apply, neg_apply, smul_eq_mul]
  have e1 : (-V ∘ (extChartAt 𝓘(ℝ, F) x₀).symm) z = -V y := rfl
  rw [e1]
  linear_combination (Real.exp (-V y)) * hL

/-- The coordinate expression of the gradient of a `C²` function is `C¹` on the chart target. -/
theorem contDiffAt_chartCoordinateField_grad (x₀ : M) {z : F}
    (hz : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target) {v : M → ℝ}
    (hv : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 v) :
    ContDiffAt ℝ 1 (chartCoordinateField (I := 𝓘(ℝ, F)) x₀ (manifoldGradient 𝓘(ℝ, F) v)) z := by
  have h1 : ContDiffAt ℝ 1 (fun w => (chartMetric (I := 𝓘(ℝ, F)) x₀ w).inverse) z :=
    (chartMetric_isInvertible_of_mem_target (I := 𝓘(ℝ, F)) x₀ hz).contDiffAt_map_inverse.comp z
      (contDiffAt_chartMetric_target x₀ hz)
  have h2 : ContDiffAt ℝ 1 (fderiv ℝ (v ∘ (extChartAt 𝓘(ℝ, F) x₀).symm)) z :=
    (contDiffAt_comp_symm x₀ hz hv).fderiv_right (by norm_num)
  have h := h1.clm_apply h2
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_target_nhds hz] with w hw
  exact (coordinateRiemannianGradient_eq_chartCoordinateField (I := 𝓘(ℝ, F)) x₀ hw
    ((hv _).mdifferentiableAt (by norm_num))).symm

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- A function eventually zero has vanishing Riesz gradient. -/
theorem manifoldGradient_eq_zero_of_eventuallyEq {u : M → ℝ} {x : M}
    (hu : u =ᶠ[𝓝 x] fun _ => 0) : manifoldGradient 𝓘(ℝ, F) u x = 0 := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_manifoldGradient, inner_zero_left]
  have h0 : u x = 0 := hu.self_of_nhds
  have : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) u x = 0 := by
    rw [hu.mfderiv_eq]
    exact mfderiv_const (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, ℝ)) (c := (0 : ℝ))
  simp [mvfderiv, this]

theorem continuous_inner_manifoldGradient {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 u) (hv : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 2 v) :
    Continuous (fun x => inner ℝ (manifoldGradient 𝓘(ℝ, F) u x) (manifoldGradient 𝓘(ℝ, F) v x)) :=
        by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 1
      (fun x => inner ℝ (manifoldGradient 𝓘(ℝ, F) u x) (manifoldGradient 𝓘(ℝ, F) v x)) x :=
    ContMDiffAt.inner_bundle (E := TangentSpace 𝓘(ℝ, F))
    (contMDiff_manifoldGradient (I := 𝓘(ℝ, F)) hu x)
    (contMDiff_manifoldGradient (I := 𝓘(ℝ, F)) hv x)
  exact this.continuousAt

end CutoffRigidity
