/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Temperate growth from bounded high derivatives

Generic calculus support (for the polynomial growth of the derivatives of a smoothed log-density,
Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2, p. 5): on arbitrary real normed spaces, a
polynomial bound on `D^{m+1} f` gives one on `D^m f` by the mean value inequality, and a smooth
function with uniformly bounded derivatives of all orders `≥ 3` has `Function.HasTemperateGrowth`.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace FunctionalInequalities.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Mean value: a polynomial bound `‖Df(x)‖ ≤ C(1+‖x‖)^k` gives `‖f(x)‖ ≤ (C + ‖f 0‖)(1+‖x‖)^{k+1}`. -/
theorem polynomial_growth_of_fderiv {f : E → F} (hf : Differentiable ℝ f) {k : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∀ x, ‖f x‖ ≤ (C + ‖f 0‖) * (1 + ‖x‖) ^ (k + 1) := by
  intro x
  have hbound : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖x‖) ^ k := by
    intro y hy
    have hy' : ‖y‖ ≤ ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    exact
      (hD y).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) hC)
  have hdiff :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ => hf y) hbound
      (convex_closedBall (0 : E) ‖x‖) (by simp : (0 : E) ∈ Metric.closedBall (0 : E) ‖x‖)
      (by simp : x ∈ Metric.closedBall (0 : E) ‖x‖)
  simp only [sub_zero] at hdiff
  have hr : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hpow : 1 ≤ (1 + ‖x‖) ^ (k + 1) := one_le_pow₀ hr
  calc
    ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add (f x) (f 0)
    _ ≤ C * (1 + ‖x‖) ^ k * ‖x‖ + ‖f 0‖ := add_le_add hdiff (le_refl _)
    _ ≤ C * (1 + ‖x‖) ^ (k + 1) + ‖f 0‖ * (1 + ‖x‖) ^ (k + 1) := by
      apply add_le_add
      · have hcr : 0 ≤ C * (1 + ‖x‖) ^ k := mul_nonneg hC (by positivity)
        calc
          C * (1 + ‖x‖) ^ k * ‖x‖ ≤ C * (1 + ‖x‖) ^ k * (1 + ‖x‖) :=
            mul_le_mul_of_nonneg_left (by linarith : ‖x‖ ≤ 1 + ‖x‖) hcr
          _ = C * (1 + ‖x‖) ^ (k + 1) := by rw [pow_succ]; ring
      · exact le_mul_of_one_le_right (norm_nonneg _) hpow
    _ = _ := by ring

/-- Polynomial growth of `D^{m+1} f` gives polynomial growth of `D^m f` (one degree higher). -/
theorem polynomial_growth_of_next_iteratedFDeriv {f : E → F} (hf : ContDiff ℝ ∞ f)
    (m k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ x, ‖iteratedFDeriv ℝ (m + 1) f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ B * (1 + ‖x‖) ^ (k + 1) := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ m f) :=
    ContDiff.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (by simp : (m : ℕ∞) < ⊤)) hf
  refine ⟨C + ‖iteratedFDeriv ℝ m f 0‖, add_nonneg hC (norm_nonneg _), ?_⟩
  apply polynomial_growth_of_fderiv hdiff hC
  intro x
  rw [norm_fderiv_iteratedFDeriv]
  exact hD x

/-- **Temperate growth from bounded high derivatives**: a smooth `f` whose derivatives of every
order `≥ 3` are uniformly bounded has `Function.HasTemperateGrowth` (orders `2, 1, 0` get degrees
`1, 2, 3`). A bounded Hessian alone is not enough: the hypothesis is for all orders `≥ 3`. -/
theorem hasTemperateGrowth_of_bounded_high_derivatives {f : E → F}
    (hf : ContDiff ℝ ∞ f)
    (hh : ∀ n : ℕ, 3 ≤ n → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    f.HasTemperateGrowth := by
  obtain ⟨C3, hC3⟩ := hh 3 le_rfl
  let B3 : ℝ := max C3 0
  have hB3 : 0 ≤ B3 := le_max_right _ _
  have hD3 : ∀ x, ‖iteratedFDeriv ℝ (2 + 1) f x‖ ≤ B3 * (1 + ‖x‖) ^ 0 := by
    intro x
    simpa only [pow_zero, mul_one] using (hC3 x).trans (le_max_left C3 0)
  obtain ⟨B2, hB2, hD2⟩ := polynomial_growth_of_next_iteratedFDeriv hf 2 0 hB3 hD3
  obtain ⟨B1, hB1, hD1⟩ := polynomial_growth_of_next_iteratedFDeriv hf 1 1 hB2 hD2
  obtain ⟨B0, _hB0, hD0⟩ := polynomial_growth_of_next_iteratedFDeriv hf 0 2 hB1 hD1
  refine ⟨hf, ?_⟩
  intro n
  by_cases hn : 3 ≤ n
  · obtain ⟨C, hC⟩ := hh n hn
    exact ⟨0, C, by simpa only [pow_zero, mul_one] using hC⟩
  · have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact ⟨3, B0, hD0⟩
    · exact ⟨2, B1, hD1⟩
    · exact ⟨1, B2, hD2⟩

end FunctionalInequalities.Analysis
