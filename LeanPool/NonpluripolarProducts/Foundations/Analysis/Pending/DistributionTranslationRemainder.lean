/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionTranslationJets

/-!
# Uniform Taylor remainders for translated kernels

The derivative of a smooth function is uniformly continuous on a compact
thickening of a compact set.  The mean-value inequality then gives a first
order Taylor estimate whose radius is independent of the base point in that
compact set.  This is the analytic core needed to control every fixed-support
test-function seminorm of a translated kernel.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Filter Asymptotics
open scoped ContDiff Distributions Topology Pointwise

namespace SGPT.Foundations.Analysis.Pending

/-- A `C²` map has a first-order Taylor remainder that is uniformly little-o
on a compact set of base points.  The conclusion is written in the
epsilon-delta form needed for taking finitely many sup-seminorms later. -/
theorem exists_uniform_taylor_remainder_bound_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 2 f) {C : Set E} (hC : IsCompact C) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ C, ∀ h : E, ‖h‖ < δ →
      ‖f (x + h) - f x - fderiv ℝ f x h‖ ≤ ε * ‖h‖ := by
  intro ε hε
  have hcompact : IsCompact (Metric.cthickening 1 C) := hC.cthickening
  have hdf : Continuous (fderiv ℝ f) :=
    (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have huc : UniformContinuousOn (fderiv ℝ f) (Metric.cthickening 1 C) :=
    hcompact.uniformContinuousOn_of_continuous hdf.continuousOn
  obtain ⟨δ₀, hδ₀, hδ₀bound⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) ε hε
  refine ⟨min 1 δ₀, lt_min one_pos hδ₀, ?_⟩
  intro x hx h hh
  have hδ₁ : ‖h‖ < 1 := hh.trans_le (min_le_left _ _)
  have hδ : ‖h‖ < δ₀ := hh.trans_le (min_le_right _ _)
  have hxthick : x ∈ Metric.cthickening 1 C :=
    Metric.self_subset_cthickening C hx
  have hsegment : ∀ y ∈ segment ℝ x (x + h),
      y ∈ Metric.cthickening 1 C := by
    intro y hy
    apply Metric.mem_cthickening_of_dist_le y x 1 C hx
    have hyball : y ∈ Metric.closedBall x (dist x (x + h)) :=
      segment_subset_closedBall_left x (x + h) hy
    exact hyball.trans (by simpa [dist_eq_norm] using hδ₁.le)
  have hderivBound : ∀ y ∈ segment ℝ x (x + h),
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ ε := by
    intro y hy
    have hydist : dist y x < δ₀ := by
      have hyball : y ∈ Metric.closedBall x (dist x (x + h)) :=
        segment_subset_closedBall_left x (x + h) hy
      exact hyball.trans_lt (by simpa [dist_eq_norm] using hδ)
    have := hδ₀bound y (hsegment y hy) x hxthick hydist
    simpa [dist_eq_norm] using this.le
  have hmv := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f x) (C := ε)
    (fun _y _hy => (hf.differentiable (by norm_num)).differentiableAt) hderivBound
    (left_mem_segment ℝ x (x + h)) (right_mem_segment ℝ x (x + h))
  simpa only [add_sub_cancel_left] using hmv

/-- Uniform Taylor control for the `m`-th spatial derivative of a translated
smooth kernel.  The increment of the kernel argument is `-h`, hence the sign
in the linear term. -/
theorem exists_uniform_iteratedFDeriv_translation_remainder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (K : Compacts E) (z : E) (m : ℕ) :
    ∀ ε > 0, ∃ δ > 0, ∀ y ∈ (K : Set E), ∀ h : E, ‖h‖ < δ →
      ‖iteratedFDeriv ℝ m κ (y - (z + h)) -
          iteratedFDeriv ℝ m κ (y - z) -
          fderiv ℝ (iteratedFDeriv ℝ m κ) (y - z) (-h)‖ ≤
        ε * ‖h‖ := by
  have hFm : ContDiff ℝ 2 (iteratedFDeriv ℝ m κ) :=
    hκ.iteratedFDeriv_right
      (by
        change ((↑(2 + m) : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hcompact : IsCompact ((fun y : E => y - z) '' (K : Set E)) :=
    K.isCompact.image (continuous_id.sub continuous_const)
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_uniform_taylor_remainder_bound_on_compact
      (iteratedFDeriv ℝ m κ) hFm hcompact ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy h hh
  have hb := hbound (y - z) ⟨y, hy, rfl⟩ (-h) (by simpa using hh)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hb

end SGPT.Foundations.Analysis.Pending
