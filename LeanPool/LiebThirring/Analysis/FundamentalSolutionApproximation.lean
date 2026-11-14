/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Analysis.FundamentalSolutionRadial

/-!
# Approximate identity from the regularized Coulomb density

Scaling of the fundamental solution's regularization density in physical dimension three.

The density pairing can be evaluated after dilating about its pole.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace LiebThirring

/-- Scaling of the fundamental solution's regularization density in physical dimension three. -/
theorem coulombApproximationDensity_smul {ε : ℝ} (hε : 0 < ε) (x : Position) :
    coulombApproximationDensity ε (ε • x) =
      (ε ^ 3)⁻¹ * coulombApproximationDensity 1 x := by
  unfold coulombApproximationDensity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hs : (ε * ‖x‖) ^ 2 + ε ^ 2 = ε ^ 2 * (‖x‖ ^ 2 + 1) := by ring
  rw [hs, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (ε ^ 2) ^ (-(5 / 2 : ℝ)) = (ε ^ 5)⁻¹ := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
    norm_num
  rw [hp]
  norm_num only [one_pow, mul_one]
  field_simp [hε.ne']

/-- The density pairing can be evaluated after dilating about its pole. -/
theorem integral_coulombApproximationDensity_sub_mul {ε : ℝ} (hε : 0 < ε)
    (f : Position → ℝ) (y : Position) :
    (∫ x, coulombApproximationDensity ε (x - y) * f x) =
      ∫ x, coulombApproximationDensity 1 x * f (y + ε • x) := by
  have ht : (∫ x, coulombApproximationDensity ε (x - y) * f x) =
      ∫ x, coulombApproximationDensity ε x * f (y + x) := by
    have h := integral_add_right_eq_self y (μ := (volume : Measure Position))
      (f := fun x => coulombApproximationDensity ε (x - y) * f x)
    calc
      _ = ∫ x, coulombApproximationDensity ε x * f (x + y) := by
        simpa only [add_sub_cancel_right] using h.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [add_comm x y]
  rw [ht]
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure Position)
    (fun x => coulombApproximationDensity ε x * f (y + x)) ε (hR := hε.le)
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at h
  simp_rw [coulombApproximationDensity_smul hε] at h
  rw [show (fun x => (ε ^ 3)⁻¹ * coulombApproximationDensity 1 x * f (y + ε • x)) =
      (fun x => (ε ^ 3)⁻¹ * (coulombApproximationDensity 1 x * f (y + ε • x))) by
        funext x; ring, integral_const_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) h).symm

/-- The regularized density converges to a point mass of weight `4π`. -/
theorem tendsto_integral_coulombApproximationDensity_sub_mul
    {f : Position → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (y : Position) :
    Tendsto (fun ε : ℝ => ∫ x, coulombApproximationDensity ε (x - y) * f x)
      (𝓝[>] 0) (𝓝 (4 * Real.pi * f y)) := by
  obtain ⟨M, hM⟩ := (hfc.isCompact_range hf).isBounded.exists_norm_le
  have hbound (x : Position) : ‖f x‖ ≤ M := hM (f x) (mem_range_self x)
  have ht : Tendsto (fun ε : ℝ =>
      ∫ x, coulombApproximationDensity 1 x * f (y + ε • x)) (𝓝[>] 0)
      (𝓝 (∫ x, coulombApproximationDensity 1 x * f y)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x => coulombApproximationDensity 1 x * M)
    · filter_upwards with ε
      have hq : Continuous (coulombApproximationDensity 1) := by
        unfold coulombApproximationDensity
        apply Continuous.mul continuous_const
        exact ((continuous_norm.pow 2).add continuous_const).rpow_const
          (fun x => Or.inl (norm_sq_add_sq_pos zero_lt_one x).ne')
      have hm : Continuous (fun x : Position => y + ε • x) :=
        continuous_const.add (continuous_id.const_smul ε)
      exact (hq.mul (hf.comp hm)).aestronglyMeasurable
    · filter_upwards with ε
      filter_upwards with x
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (coulombApproximationDensity_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (hbound _) (coulombApproximationDensity_nonneg _ _)
    · exact integrable_coulombApproximationDensity_one.mul_const M
    · filter_upwards with x
      have hi : Tendsto (fun ε : ℝ => y + ε • x) (𝓝[>] 0) (𝓝 y) := by
        have hiε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [zero_smul, add_zero] using
          (tendsto_const_nhds (x := y)).add (hiε.smul (tendsto_const_nhds (x := x)))
      exact tendsto_const_nhds.mul ((hf.tendsto y).comp hi)
  rw [integral_mul_const, integral_coulombApproximationDensity_one] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (integral_coulombApproximationDensity_sub_mul hε f y).symm

end LiebThirring

end
