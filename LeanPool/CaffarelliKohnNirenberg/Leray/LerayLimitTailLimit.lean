/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Leray Limit Tail Limit

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- A uniform bound on an exhaustion passes to a measurable limit when the
bound is lower semicontinuous on each member of that exhaustion. -/
theorem lerayLimit_lintegral_bound_of_compactExhaustion
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure α} (S : Set α) (K : ℕ → Set α)
    (hK : AECover (μ.restrict S) atTop K)
    (F : ℕ → α → E) (G : α → E)
    (B : ℝ≥0∞)
    (hFbound : ∀ m n,
      (∫⁻ x in K m, ‖F n x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ≤ B)
    (htransfer : ∀ m,
      (∀ n, (∫⁻ x in K m, ‖F n x‖ₑ ^ (2 : ℝ)
        ∂(μ.restrict S)) ≤ B) →
      (∫⁻ x in K m, ‖G x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ≤ B)
    (hG : AEMeasurable G (μ.restrict S)) :
    (∫⁻ x in S, ‖G x‖ₑ ^ (2 : ℝ) ∂μ) ≤ B := by
  have hdensity : AEMeasurable (fun x : α => ‖G x‖ₑ ^ (2 : ℝ))
      (μ.restrict S) := hG.enorm.pow_const _
  have hconverge : Tendsto
      (fun m => ∫⁻ x in K m, ‖G x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S))
      atTop
      (𝓝 (∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S))) :=
    hK.lintegral_tendsto_of_nat hdensity
  have hbound : ∀ m,
      (∫⁻ x in K m, ‖G x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ≤ B := by
    intro m
    exact htransfer m (hFbound m)
  have hglobal :
      (∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ≤ B :=
    le_of_tendsto hconverge (Eventually.of_forall hbound)
  simpa only [Measure.restrict_apply_univ] using hglobal

end CKN.Leray

end
