/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Contributions.ShortIntervalCardinality
public import LeanPool.NairTenenbaum.Polynomials.PolynomialLogMass
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The total logarithmic mass with an explicit interval-length error -/

@[expose] public section

namespace NairTenenbaum

open Real Filter Polynomial

theorem exists_polynomialLogMass_length_lower_bound {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ x y : ℝ, x₀ < x → 1 ≤ y →
      (Q.natDegree : ℝ) * y * Real.log x - B * y - (Q.natDegree : ℝ) * Real.log x ≤
        polynomialLogMass Q x y := by
  obtain ⟨x₀, B, hx₀, hB, H⟩ := exists_polynomialLogMass_card_lower_bound hQ
  refine ⟨x₀, 2 * B, hx₀, by positivity, fun x y hx hy => ?_⟩
  have hx₁ := hx₀.trans hx
  have hc := shortInterval_card_bounds (by linarith : 0 ≤ x) (by linarith : 0 ≤ y)
  have HL := mul_le_mul_of_nonneg_right hc.1
    (mul_nonneg (Nat.cast_nonneg Q.natDegree) (Real.log_pos hx₁).le)
  have HB := mul_le_mul_of_nonneg_left hc.2 hB
  have HBy : B * (y + 1) ≤ 2 * B * y := by nlinarith
  nlinarith [H x y hx]

theorem eventually_log_le_positive_rpow {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ β := by
  filter_upwards [(isLittleO_log_rpow_atTop hβ).bound (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (1 : ℝ)] with x hx hx₁
  simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (Real.log_pos hx₁),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) β)] using hx

theorem exists_polynomialLogMass_linear_error {Q : ℤ[X]} (hQ : Q ≠ 0) {β : ℝ} (hβ : 0 < β) :
    ∃ x₀ B : ℝ, 1 < x₀ ∧ 0 ≤ B ∧ ∀ x y : ℝ, x₀ < x → x ^ β ≤ y →
      (Q.natDegree : ℝ) * y * Real.log x - B * y ≤ polynomialLogMass Q x y := by
  obtain ⟨x₁, B, hx₁, hB, H⟩ := exists_polynomialLogMass_length_lower_bound hQ
  obtain ⟨x₂, H₂⟩ := eventually_atTop.mp (eventually_log_le_positive_rpow hβ)
  refine ⟨max x₁ x₂, B + Q.natDegree, hx₁.trans_le (le_max_left _ _), by positivity,
    fun x y hx hy => ?_⟩
  have hx₁' := (le_max_left _ _).trans_lt hx
  have hx₁₁ := hx₁.trans hx₁'
  have hy₁ : 1 ≤ y := (Real.one_le_rpow hx₁₁.le hβ.le).trans hy
  have Hlog := (H₂ x ((le_max_right _ _).trans hx.le)).trans hy
  have HG := mul_le_mul_of_nonneg_left Hlog (Nat.cast_nonneg Q.natDegree)
  nlinarith [H x y hx₁' hy₁]

end NairTenenbaum
