/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Actual manifold integral curves of continuous fields are C¹
The coordinate derivative is the actual tangent-bundle trivialization of the
field along the curve. Its continuity supplies C¹ regularity, rather than an
additional smooth-trajectory hypothesis.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology


namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The actual manifold ODE with a continuous tangent field has C¹ solutions. -/
theorem IsMIntegralCurveAt.contMDiffAt_one
    {X : (x : M) → TangentSpace I x} (hX : Continuous (T% X))
    {γ : ℝ → M} {t₀ : ℝ} (hγ : IsMIntegralCurveAt γ X t₀) :
    ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t₀ := by
  have hsrc : ∀ᶠ t in 𝓝 t₀, γ t ∈ (chartAt H (γ t₀)).source :=
    hγ.continuousAt.preimage_mem_nhds (chart_source_mem_nhds H (γ t₀))
  obtain ⟨r, hr, hgood⟩ := Metric.eventually_nhds_iff_ball.mp
    (hγ.and (hγ.eventually_hasDerivAt.and hsrc))
  let s := Metric.ball t₀ r
  have ht₀ : t₀ ∈ s := Metric.mem_ball_self hr
  have hsγ : IsMIntegralCurveOn γ X s := fun t ht ↦
    (hgood t ht).1.hasMFDerivWithinAt
  let e := trivializationAt E (TangentSpace I) (γ t₀)
  let velocity : ℝ → E := fun t ↦ (e (T% X (γ t))).2
  have hvelocity : ContinuousOn velocity s := by
    apply ContinuousOn.snd
    apply e.continuousOn.comp (hX.comp_continuousOn hsγ.continuousOn)
    intro t ht
    simpa [e, TangentBundle.trivializationAt_baseSet] using (hgood t ht).2.2
  have hderiv : ∀ t ∈ s, HasDerivAt ((extChartAt I (γ t₀)) ∘ γ) (velocity t) t := by
    intro t ht
    convert! (hgood t ht).2.1 using 1
  have hc : ContDiffOn ℝ 1 ((extChartAt I (γ t₀)) ∘ γ) s := by
    apply (contDiffOn_one_iff_derivWithin Metric.isOpen_ball.uniqueDiffOn).mpr
    refine ⟨fun t ht ↦ (hderiv t ht).differentiableAt.differentiableWithinAt, ?_⟩
    apply hvelocity.congr
    intro t ht
    exact (hderiv t ht).hasDerivWithinAt.derivWithin
      (Metric.isOpen_ball.uniqueDiffOn t ht)
  rw [contMDiffAt_iff_target]
  refine ⟨hγ.continuousAt, ?_⟩
  rw [contMDiffAt_iff_contDiffAt]
  exact hc.contDiffAt (Metric.isOpen_ball.mem_nhds ht₀)

/-- On an open time domain the actual integral curve is C¹ everywhere. -/
theorem IsMIntegralCurveOn.contMDiffOn_one
    {X : (x : M) → TangentSpace I x} (hX : Continuous (T% X))
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsMIntegralCurveOn γ X s) (hs : IsOpen s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s := by
  intro t ht
  exact (IsMIntegralCurveAt.contMDiffAt_one hX
    (hγ.isMIntegralCurveAt (hs.mem_nhds ht))).contMDiffWithinAt

end CutoffRigidity
