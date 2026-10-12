/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Analysis.FundamentalSolutionRegularization

/-!
# Dominated convergence to the singular Coulomb kernel

The negative half-power of a squared norm is the real inverse norm.

The regularized kernel is bounded by the inverse norm away from the pole.
-/

public section

open MeasureTheory Filter InnerProductSpace Laplacian
open scoped Topology

namespace LiebThirring

/-- The negative half-power of a squared norm is the real inverse norm. -/
theorem norm_sq_rpow_neg_half (x : Position) :
    (‖x‖ ^ 2) ^ (-(1 / 2 : ℝ)) = ‖x‖⁻¹ := by
  rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

/-- The regularized kernel is bounded by the inverse norm away from the pole. -/
theorem regularizedCoulombKernel_le_inv_norm (ε : ℝ) {x : Position} (hx : x ≠ 0) :
    regularizedCoulombKernel ε x ≤ ‖x‖⁻¹ := by
  unfold regularizedCoulombKernel
  rw [← norm_sq_rpow_neg_half x]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)

/-- The regularized kernel tends pointwise to the inverse norm away from its pole. -/
theorem tendsto_regularizedCoulombKernel {x : Position} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => regularizedCoulombKernel ε x) (𝓝[>] 0) (𝓝 ‖x‖⁻¹) := by
  have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) (𝓝[>] 0) (𝓝 (‖x‖ ^ 2)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (tendsto_const_nhds (x := ‖x‖ ^ 2)).add (hi.pow 2)
  have ht := hs.rpow_const (p := -(1 / 2 : ℝ))
    (Or.inl (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)))
  rw [norm_sq_rpow_neg_half] at ht
  exact ht

/-- Dominated convergence for the regularized test-function pairing in the fundamental solution. -/
theorem tendsto_integral_regularizedCoulombKernel_sub_mul_laplacian
    {f : Position → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (y : Position) :
    Tendsto (fun ε : ℝ => ∫ x, regularizedCoulombKernel ε (x - y) * Δ f x)
      (𝓝[>] 0) (𝓝 (∫ x, ‖x - y‖⁻¹ * Δ f x)) := by
  have hpole : ∀ᵐ x : Position, x ≠ y := (volume : Measure Position).ae_ne y
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖‖x - y‖⁻¹ * Δ f x‖)
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hcont : Continuous (fun x : Position => regularizedCoulombKernel ε (x - y)) :=
      (contDiff_regularizedCoulombKernel hε).continuous.comp (continuous_id.sub continuous_const)
    exact (hcont.mul (continuous_laplacian_position hf)).aestronglyMeasurable
  · filter_upwards with ε
    filter_upwards [hpole] with x hx
    have hpos : 0 ≤ regularizedCoulombKernel ε (x - y) :=
      Real.rpow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _
    simp only [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg hpos, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (regularizedCoulombKernel_le_inv_norm ε (sub_ne_zero.mpr hx)) (abs_nonneg _)
  · exact (integrable_inv_norm_sub_mul_laplacian hf hfc y).norm
  · filter_upwards [hpole] with x hx
    exact (tendsto_regularizedCoulombKernel (sub_ne_zero.mpr hx)).mul tendsto_const_nhds

end LiebThirring

end
