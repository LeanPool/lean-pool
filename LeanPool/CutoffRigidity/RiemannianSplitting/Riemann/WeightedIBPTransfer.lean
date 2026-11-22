/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Geometry.Manifold.ChartedSpace

/-! # Transfer of integrals through a chart carrying a density -/

@[expose] public section
open MeasureTheory Set
open scoped Topology


namespace CutoffRigidity

variable {H : Type*} [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] [OpensMeasurableSpace H]
  {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace H M]

omit [SecondCountableTopology H] in
/-- If `μ` pushed forward by the chart has density `r` w.r.t. `ν` on the target, integrals of
functions vanishing off the source are computed in the chart. -/
theorem integral_eq_chart_integral (x₀ : M) {μ : Measure M} {ν : Measure H} {r : H → ℝ}
    (hμ : (μ.restrict (chartAt H x₀).source).map (chartAt H x₀) =
      (ν.restrict (chartAt H x₀).target).withDensity fun z => ENNReal.ofReal (r z))
    (hr : ContinuousOn r (chartAt H x₀).target) (hr0 : ∀ z ∈ (chartAt H x₀).target, 0 ≤ r z)
    {g : M → ℝ} (hgs : ContinuousOn (g ∘ (chartAt H x₀).symm) (chartAt H x₀).target)
    (hg0 : ∀ x, x ∉ (chartAt H x₀).source → g x = 0) :
    ∫ x, g x ∂μ = ∫ z in (chartAt H x₀).target, r z * g ((chartAt H x₀).symm z) ∂ν := by
  set φ := chartAt H x₀ with hφ
  have hSmeas : MeasurableSet φ.source := φ.open_source.measurableSet
  have hTmeas : MeasurableSet φ.target := φ.open_target.measurableSet
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := φ.source) (fun x hx => hg0 x hx)]
  have hφm : AEMeasurable φ (μ.restrict φ.source) :=
    φ.continuousOn.aemeasurable hSmeas
  have hmeas : AEStronglyMeasurable (g ∘ φ.symm)
      ((μ.restrict φ.source).map φ) := by
    rw [hμ]
    exact AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
      (hgs.aestronglyMeasurable hTmeas)
  calc ∫ x in φ.source, g x ∂μ
      = ∫ x, (g ∘ φ.symm) (φ x) ∂μ.restrict φ.source := by
        refine setIntegral_congr_fun hSmeas fun x hx => ?_
        simp [φ.left_inv hx]
    _ = ∫ z, (g ∘ φ.symm) z ∂(μ.restrict φ.source).map φ :=
        (integral_map hφm hmeas).symm
    _ = ∫ z, (g ∘ φ.symm) z ∂(ν.restrict φ.target).withDensity fun z => ENNReal.ofReal (r z) := by
        rw [hμ]
    _ = ∫ z, (ENNReal.ofReal (r z)).toReal • (g ∘ φ.symm) z ∂ν.restrict φ.target := by
        refine integral_withDensity_eq_integral_toReal_smul₀ ?_ ?_ _
        · exact ENNReal.measurable_ofReal.comp_aemeasurable (hr.aemeasurable hTmeas)
        · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    _ = ∫ z in φ.target, r z * g (φ.symm z) ∂ν := by
        refine setIntegral_congr_fun hTmeas fun z hz => ?_
        simp [ENNReal.toReal_ofReal (hr0 z hz)]

end CutoffRigidity
