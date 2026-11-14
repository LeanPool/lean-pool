/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# ParametricIntegralC1

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Differentiating compact parametric integrals

This file supplies the fixed-compact-set calculus bridge used to construct
scalar primitives for divergence-form forcing. Mathlib provides differentiation
under the integral and continuity of compact parametric integrals separately;
the theorem below packages them into a `C¹` result on `Vec d`.
-/

open Filter MeasureTheory Metric Set

namespace DivergenceFormProcess

/-- A jointly continuous family of scalar functions with a jointly continuous
Fréchet derivative can be integrated over a compact real set without losing
`C¹` regularity in the `Vec d` parameter. -/
theorem contDiff_one_setIntegral_of_continuous_hasFDerivAt
    {d : ℕ} {K : Set ℝ} (hK : IsCompact K)
    {F : HCPolySupport.Vec d → ℝ → ℝ}
    {F' : HCPolySupport.Vec d → ℝ →
      HCPolySupport.Vec d →L[ℝ] ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hdiff : ∀ x t, HasFDerivAt (fun y ↦ F y t) (F' x t) x) :
    ContDiff ℝ 1 (fun x ↦ ∫ t in K, F x t) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun x ↦ ∫ t in K, F' x t, ?_, ?_⟩
  · exact continuous_parametric_integral_of_continuous hF' hK
  · intro x
    have hclosedCompact : IsCompact (closedBall x 1) := isCompact_closedBall x 1
    have hprodCompact : IsCompact (closedBall x 1 ×ˢ K) := hclosedCompact.prod hK
    obtain ⟨C, hC⟩ := hprodCompact.bddAbove_image hF'.norm.continuousOn
    have hFmeas : ∀ᶠ y in nhds x,
        AEStronglyMeasurable (F y) (volume.restrict K) := by
      filter_upwards with y
      exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hFint : Integrable (F x) (volume.restrict K) := by
      exact (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
    have hF'meas : AEStronglyMeasurable (F' x) (volume.restrict K) :=
      (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hbound : ∀ᵐ t ∂volume.restrict K, ∀ y ∈ ball x 1, ‖F' y t‖ ≤ C := by
      rw [ae_restrict_iff' hK.measurableSet]
      filter_upwards with t ht
      intro y hy
      have hyt : (y, t) ∈ closedBall x 1 ×ˢ K :=
        ⟨mem_closedBall.2 hy.le, ht⟩
      exact hC ⟨(y, t), hyt, rfl⟩
    have hCint : Integrable (fun _ : ℝ ↦ C) (volume.restrict K) :=
      MeasureTheory.integrableOn_const (hs := hK.measure_ne_top)
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := F) (F' := F') (x₀ := x) (bound := fun _ ↦ C)
      (s := ball x 1) (hs := Metric.ball_mem_nhds x zero_lt_one)
      hFmeas hFint hF'meas hbound hCint
      (Filter.Eventually.of_forall fun t y _ ↦ hdiff y t)

end DivergenceFormProcess
