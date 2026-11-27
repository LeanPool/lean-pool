/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.L2BoundedExponential
public import LeanPool.VacuumBellSeparation.FreeField.RapidityBoostFourier

/-!
# Actual bounded frequency cutoffs and their entire rapidity evolution

The cutoff only restricts the first rapidity Fourier coordinate; the two
transverse directions and the physical scaled measure are unchanged.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

/-- Rapidity frequency cutoff. -/
noncomputable def rapidityFrequencyCutoff (N : ℕ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ := by
  classical
  exact if |⟪e₁, ξ⟫_ℝ| ≤ N then 1 else 0

/-- Rapidity bounded frequency. -/
noncomputable def rapidityBoundedFrequency (N : ℕ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ := by
  classical
  exact if |⟪e₁, ξ⟫_ℝ| ≤ N then (2 * Real.pi * ⟪e₁, ξ⟫_ℝ : ℝ) * Complex.I else 0

theorem measurable_rapidityFrequencyCutoff (N : ℕ) : Measurable (rapidityFrequencyCutoff N) := by
  unfold rapidityFrequencyCutoff
  exact Measurable.ite (measurableSet_le (continuous_const.inner continuous_id).abs.measurable
    measurable_const) measurable_const measurable_const

theorem measurable_rapidityBoundedFrequency (N : ℕ) : Measurable (rapidityBoundedFrequency N) := by
  unfold rapidityBoundedFrequency
  apply Measurable.ite (measurableSet_le (continuous_const.inner continuous_id).abs.measurable
    measurable_const) _ measurable_const
  fun_prop

theorem norm_rapidityFrequencyCutoff_le (N : ℕ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖rapidityFrequencyCutoff N ξ‖ ≤ 1 := by
  classical
  unfold rapidityFrequencyCutoff
  split_ifs <;> simp

theorem norm_rapidityBoundedFrequency_le (N : ℕ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖rapidityBoundedFrequency N ξ‖ ≤ 2 * Real.pi * N := by
  classical
  unfold rapidityBoundedFrequency
  split_ifs with h
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · simp only [norm_zero]
    positivity

theorem memLp_rapidityFrequencyCutoff (N : ℕ) :
    MemLp (rapidityFrequencyCutoff N) ⊤ rapidityMeasure :=
  memLp_top_of_bound (measurable_rapidityFrequencyCutoff N).aestronglyMeasurable 1
    (Eventually.of_forall (norm_rapidityFrequencyCutoff_le N))

/-- Continuous linear map for the rapidity cutoff, of type `RapidityL2 →L[ℂ] RapidityL2`. -/
noncomputable def rapidityCutoff (N : ℕ) : RapidityL2 →L[ℂ] RapidityL2 :=
  lpMultiplication rapidityMeasure (rapidityFrequencyCutoff N) (memLp_rapidityFrequencyCutoff N)

theorem rapidityCutoff_ae (N : ℕ) (f : RapidityL2) :
    rapidityCutoff N f =ᵐ[rapidityMeasure] fun ξ => rapidityFrequencyCutoff N ξ * f ξ :=
  lpMultiplication_ae rapidityMeasure _ _ f

theorem norm_rapidityCutoff_apply_le (N : ℕ) (f : RapidityL2) : ‖rapidityCutoff N f‖ ≤ ‖f‖ := by
  have h := lpMultiplication_norm_le rapidityMeasure (rapidityFrequencyCutoff N)
    (memLp_rapidityFrequencyCutoff N) zero_le_one
    (Eventually.of_forall (norm_rapidityFrequencyCutoff_le N))
  exact ((rapidityCutoff N).le_opNorm f).trans (by
    simpa only [rapidityCutoff, one_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg f))

/-- Rapidity cutoff evolution. -/
noncomputable def rapidityCutoffEvolution (N : ℕ) (f : RapidityL2) (z : ℂ) : RapidityL2 :=
  l2BoundedExponential rapidityMeasure (rapidityBoundedFrequency N)
    (measurable_rapidityBoundedFrequency N)
    (norm_rapidityBoundedFrequency_le N) z (rapidityCutoff N f)

theorem differentiable_rapidityCutoffEvolution (N : ℕ) (f : RapidityL2) :
    Differentiable ℂ (rapidityCutoffEvolution N f) :=
  differentiable_l2BoundedExponential rapidityMeasure (rapidityBoundedFrequency N)
    (measurable_rapidityBoundedFrequency N) (by positivity)
    (norm_rapidityBoundedFrequency_le N) (rapidityCutoff N f)

theorem rapidityCutoffEvolution_ae (N : ℕ) (f : RapidityL2) (z : ℂ) :
    rapidityCutoffEvolution N f z =ᵐ[rapidityMeasure] fun ξ =>
      rapidityFrequencyCutoff N ξ *
        (Complex.exp (z * ((2 * Real.pi * ⟪e₁, ξ⟫_ℝ : ℝ) * Complex.I)) * f ξ) := by
  classical
  filter_upwards [l2BoundedExponential_ae rapidityMeasure (rapidityBoundedFrequency N)
    (measurable_rapidityBoundedFrequency N)
    (norm_rapidityBoundedFrequency_le N) z (rapidityCutoff N f), rapidityCutoff_ae N f]
    with ξ he hc
  unfold rapidityCutoffEvolution
  rw [he, hc]
  unfold rapidityFrequencyCutoff rapidityBoundedFrequency
  split_ifs <;> simp

theorem rapidityCutoffEvolution_ofReal (N : ℕ) (f : RapidityL2) (t : ℝ) :
    rapidityCutoffEvolution N f t = rapidityCutoff N (rapidityBoostMultiplier (-t) f) := by
  apply Lp.ext
  filter_upwards [rapidityCutoffEvolution_ae N f t,
    rapidityCutoff_ae N (rapidityBoostMultiplier (-t) f),
    lpMultiplication_ae rapidityMeasure (rapidityBoostPhase (-t)) (memLp_rapidityBoostPhase (-t)) f]
    with ξ he hc hb
  rw [he, hc]
  change rapidityFrequencyCutoff N ξ *
    (Complex.exp ((t : ℂ) * ((2 * Real.pi * ⟪e₁, ξ⟫_ℝ : ℝ) * Complex.I)) * f ξ) =
      rapidityFrequencyCutoff N ξ *
        (lpMultiplication rapidityMeasure (rapidityBoostPhase (-t))
          (memLp_rapidityBoostPhase (-t)) f) ξ
  rw [hb]
  congr 2
  unfold rapidityBoostPhase
  congr 1
  push_cast
  ring

theorem norm_rapidityCutoffEvolution_le (N : ℕ) (f : RapidityL2) {z : ℂ}
    (hz₀ : 0 ≤ z.im) (hzπ : z.im ≤ Real.pi) :
    ‖rapidityCutoffEvolution N f z‖ ≤ Real.exp (2 * Real.pi ^ 2 * N) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [rapidityCutoffEvolution_ae N f z] with ξ hξ
  rw [hξ]
  by_cases hk : |⟪e₁, ξ⟫_ℝ| ≤ N
  · have he : ‖Complex.exp (z * ((2 * Real.pi * ⟪e₁, ξ⟫_ℝ : ℝ) * Complex.I))‖ ≤
        Real.exp (2 * Real.pi ^ 2 * N) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hl := (abs_le.mp hk).1
      have hu := mul_le_mul_of_nonneg_left (neg_le_neg hl) hz₀
      have hv := mul_le_mul_of_nonneg_right hzπ (Nat.cast_nonneg N)
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_sub]
      nlinarith [Real.pi_pos]
    simp only [rapidityFrequencyCutoff, ite_eq_left hk, one_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
  · simp only [rapidityFrequencyCutoff, ite_eq_right hk, zero_mul, norm_zero]
    positivity

end VacuumBellSeparation
