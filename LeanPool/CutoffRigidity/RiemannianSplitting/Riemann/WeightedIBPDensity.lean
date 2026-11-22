/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPLocal

/-! # The Challenge chart volume density

`CutCur.chartVolumeDensity F x₀` agrees on the chart target with the project's
`chartRiemannianVolumeDensity`; hence it is continuous and positive there.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartVolumeDensity_eq_riemannian (x₀ : M) {z : F} (hz : z ∈ (chartAt F x₀).target) :
    chartVolumeDensity F x₀ z =
      CutoffRigidity.chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀ z := by
  have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  rw [CutoffRigidity.chartRiemannianVolumeDensity_eq_sqrt]
  unfold chartVolumeDensity CutoffRigidity.chartRiemannianGram
  congr 2
  funext i j
  have := CutoffRigidity.chartFrame_eq_mfderiv (F := F) x₀ hz'
  simp only [CutoffRigidity.chartMetric_apply, this]
  rfl

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem chartVolumeDensity_pos (x₀ : M) {z : F} (hz : z ∈ (chartAt F x₀).target) :
    0 < chartVolumeDensity F x₀ z := by
  rw [chartVolumeDensity_eq_riemannian F x₀ hz]
  exact CutoffRigidity.chartRiemannianVolumeDensity_pos x₀
    (by rw [CutoffRigidity.extChartAt_target_eq]; exact hz)

theorem continuousOn_chartVolumeDensity (x₀ : M) :
    ContinuousOn (chartVolumeDensity F x₀) (chartAt F x₀).target := by
  have hD : ContinuousOn (CutoffRigidity.chartRiemannianVolumeDensity (I := 𝓘(ℝ, F)) x₀)
      (chartAt F x₀).target := by
    intro z hz
    have hz' : z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := by
      rw [CutoffRigidity.extChartAt_target_eq]; exact hz
    exact (CutoffRigidity.contDiffAt_chartRiemannianVolumeDensity_target x₀
      hz').continuousAt.continuousWithinAt
  exact hD.congr fun z hz => chartVolumeDensity_eq_riemannian F x₀ hz

end CutCur
