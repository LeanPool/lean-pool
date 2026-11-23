/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.ContourLocal
public import LeanPool.Bruck.GrowthFacts
public import LeanPool.Bruck.MaximumData
public import LeanPool.Bruck.QuantitativeInverse

/-! # Uniform lower growth of entire solutions -/

@[expose] public section

namespace Bruck

open Filter Metric

private theorem eventually_four_log_sq_le :
    ∀ᶠ R : ℝ in atTop, 4 * (Real.log R) ^ 2 ≤ R := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (show 0 < (1 / 4 : ℝ) by norm_num)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with R hR hR₀
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id_eq, Real.norm_eq_abs,
    abs_of_nonneg hR₀] at hR
  linarith

private theorem inverse_derivative_polynomial_bounds {q : ℂ} {r ν R k : ℝ}
    (hr : 1 ≤ r) (hν : 1 / 2 ≤ ν) (hR : 1 ≤ R) (hk : 0 < k)
    (hkR : k * r ≤ R) (h4k : 4 / k ≤ R) (hνR : 2 * ν ≤ R)
    (hlo : r / (2 * ν * R) ≤ ‖q‖) (hup : ‖q‖ ≤ 2 * r / (ν * R)) :
    R⁻¹ ^ 2 ≤ ‖q‖ ∧ ‖q‖ ≤ R ^ 2 := by
  have hνpos : 0 < ν := by linarith
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  constructor
  · apply le_trans _ hlo
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = 2 * ν / R := by field_simp
      _ ≤ 1 := (div_le_one hRpos).mpr hνR
      _ ≤ r := hr
  · have hνb : 2 / ν ≤ 4 := (div_le_iff₀ hνpos).mpr (by linarith)
    have hrR : r / R ≤ 1 / k := by
      apply (div_le_iff₀ hRpos).mpr
      rw [one_div, ← div_eq_inv_mul]
      exact (le_div_iff₀ hk).mpr (by simpa [mul_comm] using hkR)
    calc
      _ ≤ 2 * r / (ν * R) := hup
      _ = (2 / ν) * (r / R) := by field_simp
      _ ≤ 4 * (1 / k) := mul_le_mul hνb hrR (by positivity) (by norm_num)
      _ = 4 / k := by ring
      _ ≤ R := h4k
      _ ≤ R ^ 2 := by nlinarith [mul_nonneg hRpos.le (sub_nonneg.mpr hR)]

/-- There are arbitrarily large radii, chosen using only `h`, at which every
entire solution satisfies the same quantitative lower bound. -/
theorem exists_uniform_maximumModulus_lower_bound {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hnon : ¬ ∀ z, h z = h 0) (bound : ℝ) :
    ∃ r : ℝ, bound ≤ r ∧ 1 ≤ r ∧ ∀ (y : ℂ → ℂ), Differentiable ℂ y →
      (∀ z, deriv y z = Complex.exp (h z) * y z + 1) →
      Real.exp (Real.exp (wvMaximumModulus h r / 2200)) ≤ wvMaximumModulus y (2 * r) := by
  obtain ⟨k, hk, hkGrowth⟩ := exists_linear_le_maximumModulus hh hnon
  have hM := maximumModulus_tendsto_atTop hh hnon
  have hE := hM.eventually (local_quantitative_growth.and (eventually_four_log_sq_le.and
    ((eventually_ge_atTop (1 : ℝ)).and (eventually_ge_atTop (4 / k)))))
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp hE
  obtain ⟨r, z, ν, hr, maximum⟩ :=
    exists_maximum_data hh hnon (max r₀ bound)
  let R := wvMaximumModulus h r
  let c : ℂ := -(R : ℂ) * Complex.I
  let D := ball c (R / 10)
  obtain ⟨hLocal, hRlog, hR1, hRk⟩ := hr₀ r ((le_max_left _ _).trans hr)
  have hz : z ≠ 0 := by
    intro hz
    have circle := maximum.point_on_circle
    rw [hz, norm_zero] at circle
    linarith [maximum.radius_lower]
  have hhZ : h z ≠ 0 := by
    intro hz
    have modulus := maximum.point_maximal
    rw [hz, norm_zero] at modulus
    linarith [maximum.modulus_lower, Real.exp_pos 1]
  obtain ⟨χ, q, hχ, hqlo, hqup⟩ := exists_quantitative_inverse
    hh hz hhZ maximum.scale_lower maximum.approximation
  rw [maximum.point_maximal, maximum.point_on_circle] at hχ hqlo hqup
  have hq (w : ℂ) (hw : w ∈ D) : q w ≠ 0 ∧ DifferentiableAt ℂ q w ∧ ‖deriv q w / q w‖ ≤ 10 / R :=
    (hχ w hw).2.2.2
  have hνR : 2 * ν ≤ R := by
    have scale : ν ≤ 2 * (Real.log R) ^ 2 := maximum.scale_upper
    change 4 * (Real.log R) ^ 2 ≤ R at hRlog
    linarith
  obtain ⟨hlo, hup⟩ :=
    inverse_derivative_polynomial_bounds maximum.radius_lower maximum.scale_lower hR1 hk
      (hkGrowth r maximum.radius_lower) hRk hνR hqlo hqup
  obtain ⟨w₀, hw₀, w₁, hw₁, hW⟩ := hLocal q hq hlo hup
  refine ⟨r, (le_max_right _ _).trans hr, maximum.radius_lower, ?_⟩
  intro y hy hode
  let Y : ℂ → ℂ := y ∘ χ
  have hY (w : ℂ) (hw : w ∈ D) : HasDerivAt Y (q w * (Complex.exp w * Y w + 1)) w := by
    have had := (hy (χ w)).hasDerivAt.comp w (hχ w hw).2.2.1
    rw [hode, (hχ w hw).2.1] at had
    simpa only [Y, Function.comp_apply, mul_comm (q w)] using had
  have hbound (w : ℂ) (hw : w ∈ D) : ‖Y w‖ ≤ wvMaximumModulus y (2 * r) :=
    wv_norm_le_maximumModulus_of_le hy (by linarith [maximum.radius_lower]) (hχ w hw).1
  exact (hW Y hY).trans (max_le (hbound w₀ hw₀) (hbound w₁ hw₁))

end Bruck
