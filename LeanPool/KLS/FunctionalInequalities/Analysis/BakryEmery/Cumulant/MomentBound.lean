/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
public import LeanPool.KLS.FunctionalInequalities.Analysis.IteratedDerivative.Log

/-!
# Cumulant norm bounds from moment bounds
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis.BakryEmery


/-- Cumulants are bounded by moments. -/
theorem norm_cumulant_le_of_moment_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) {m : ℕ} {D : ℝ}
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ m → (∫ x, ‖x‖ ^ i ∂ν) ≤ D ^ i) :
    ‖cumulant ν m‖ ≤ (m.factorial : ℝ) ^ 2 * D ^ m := by
  have hf : ContDiffOn ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂ν)
      (Metric.ball 0 r) := by
    simpa only [smul_eq_mul, mul_one] using
      weighted_integral_contDiffOn ν
        (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (norm_exp_weights hexp)
  have hpos : ∀ z ∈ Metric.ball (0 : E) r, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂ν := by
    intro z hz
    apply integral_exp_pos
    have hz' : ‖z‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    simpa only [smul_eq_mul, mul_one] using
      integrable_exp_inner_smul_of_lt ν
        (g := fun _ : E => (1 : ℝ))
        measurable_const.aestronglyMeasurable (norm_exp_weights hexp) hz'
  have hone : (∫ x : E, Real.exp ⟪(0 : E), x⟫ ∂ν) = 1 := by simp
  exact norm_iteratedFDeriv_log_comp_le_factorial_sq Metric.isOpen_ball
    (by simpa only [Metric.mem_ball, dist_self] using hr) hf hpos hone
    (fun i hi him =>
      (norm_iteratedFDeriv_laplace_zero_le ν hr hexp i).trans (hD i hi him))

end FunctionalInequalities.Analysis.BakryEmery
