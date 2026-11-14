/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Analysis.WeakHarmonicRegularization
/-!
# Decay of compactly supported mollifications

Real scalar convolution is commutative.

Convolution with a normalized compact bump preserves decay at infinity.
-/
public section
open Filter MeasureTheory ContinuousLinearMap Set Metric
open scoped Topology Convolution
namespace LiebThirring
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
/-- Real scalar convolution is commutative. -/
lemma convolution_real_comm (f g : E → ℝ) : f ⋆[lsmul ℝ ℝ, μ] g = g ⋆[lsmul ℝ ℝ, μ] f := by
  exact convolution_symm (lsmul ℝ ℝ) (by
    ext
    exact mul_comm _ _)

/-- Convolution with a normalized compact bump preserves decay at infinity. -/
lemma tendsto_normed_bump_convolution_cocompact {w : E → ℝ}
    (hw : Continuous w) (hd : Tendsto w (cocompact E) (𝓝 0)) (b : ContDiffBump (0 : E)) :
    Tendsto (b.normed μ ⋆[lsmul ℝ ℝ, μ] w) (cocompact E) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ y in cocompact E, dist (w y) 0 < ε / 2 :=
    (Metric.tendsto_nhds.mp hd) (ε / 2) (half_pos hε)
  obtain ⟨K, hK, hKe⟩ := mem_cocompact.mp he
  obtain ⟨A, hKA⟩ := hK.isBounded.subset_closedBall (0 : E)
  have hlarge : ∀ᶠ x : E in cocompact E, A + b.rOut < ‖x‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop (A + b.rOut))
  filter_upwards [hlarge] with x hx
  have hnear : ∀ y ∈ ball x b.rOut, dist (w y) 0 ≤ ε / 2 := by
    intro y hy
    refine le_of_lt (hKe ?_)
    intro hyK
    have hyA : ‖y‖ ≤ A := mem_closedBall_zero_iff.mp (hKA hyK)
    have hxy : ‖x‖ ≤ dist y x + ‖y‖ := by
      simpa only [dist_eq_norm, norm_sub_rev] using norm_le_norm_sub_add x y
    linarith only [hyA, hxy, mem_ball.mp hy, hx]
  have hle := dist_convolution_le (μ := μ) (f := b.normed μ) (g := w) (x₀ := x)
    (half_pos hε).le b.support_normed_eq.subset b.nonneg_normed b.integral_normed
      hw.aestronglyMeasurable hnear
  exact hle.trans_lt (half_lt_self hε)
end LiebThirring
end
