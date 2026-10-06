/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Defs
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Series helpers

Elementary series identities and bounds shared by the proofs of A001, A004 and A005.

## Main results

* `LeanPolyLog.Series.hasSum_one_div_odd_sq`: `∑_{k ≥ 0} 1/(2k+1)² = π²/8`.
* `LeanPolyLog.Series.hasSum_eta_two`: `η(2) = ∑_{n ≥ 0} (-1)ⁿ/(n+1)² = π²/12`.
* `LeanPolyLog.Series.hasSum_catalan`: the series defining `G` converges (absolutely) to `G`.
* `LeanPolyLog.Series.hasSum_log_one_add_sq_div`: for `0 < x < 1`,
  `log(1+x²)/x = ∑_{n ≥ 0} (-1)ⁿ x^(2n+1)/(n+1)`.
* `LeanPolyLog.Series.continuous_log_one_add_sq_div` and
  `LeanPolyLog.Series.continuous_log_one_add_sq_sq_div_cube`: `log(1+x²)/x` and `log²(1+x²)/x³`
  are continuous on all of `ℝ`. At `x = 0` Lean's division gives the value `0`, which is also
  the limit, because `0 ≤ log(1+x²) ≤ x²`.
-/

open Real Filter Topology

namespace LeanPolyLog.Series

/-! ### Values of `ζ(2)`-type series -/

/-- The even terms of `ζ(2)`, indexed as `n = 2k` (the `k = 0` term is `1/0 = 0`). -/
public theorem hasSum_one_div_even_sq :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) (π ^ 2 / 24) := by
  convert hasSum_zeta_two.mul_left (1 / 4) using 1
  · funext k
    push_cast
    ring
  · ring

/-- The odd terms of `ζ(2)`, indexed as `n = 2k + 1`, are summable. -/
public theorem summable_one_div_odd_sq :
    Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by simpa using h
  exact hasSum_zeta_two.summable.comp_injective hi

/-- `∑_{k ≥ 0} 1/(2k+1)² = π²/8`, with the index cast from `ℕ` as in `f (2 * k + 1)`. -/
public theorem hasSum_one_div_odd_sq_natCast :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 8) := by
  have h := tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
    hasSum_one_div_even_sq.summable summable_one_div_odd_sq
  rw [hasSum_zeta_two.tsum_eq, hasSum_one_div_even_sq.tsum_eq] at h
  have h8 : ∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 8 := by linarith
  rw [← h8]
  exact summable_one_div_odd_sq.hasSum

/-- `∑_{k ≥ 0} 1/(2k+1)² = π²/8`. -/
public theorem hasSum_one_div_odd_sq :
    HasSum (fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 1) ^ 2) (π ^ 2 / 8) :=
  hasSum_one_div_odd_sq_natCast.congr_fun fun k => by push_cast; ring

/-- The Dirichlet eta function at `2`: `η(2) = ∑_{n ≥ 0} (-1)ⁿ/(n+1)² = π²/12`. -/
public theorem hasSum_eta_two :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 12) := by
  -- `g m = (-1)^(m+1)/m²`, whose `m = 0` term is `1/0 = 0`
  set g : ℕ → ℝ := fun m => (-1 : ℝ) ^ (m + 1) / (m : ℝ) ^ 2
  have he : HasSum (fun k : ℕ => g (2 * k)) (-(π ^ 2 / 24)) :=
    hasSum_one_div_even_sq.neg.congr_fun fun k => by simp [g, pow_succ, pow_mul]; ring
  have ho : HasSum (fun k : ℕ => g (2 * k + 1)) (π ^ 2 / 8) :=
    hasSum_one_div_odd_sq_natCast.congr_fun fun k => by simp [g, pow_succ, pow_mul]
  have hg : HasSum g (π ^ 2 / 12) := by
    convert he.even_add_odd ho using 1
    ring
  rw [← hasSum_nat_add_iff' 1] at hg
  simpa [g, pow_succ] using hg

/-- The series defining Catalan's constant converges (absolutely), with sum `G`. -/
public theorem hasSum_catalan : HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1 : ℝ) ^ 2) G := by
  have hs : Summable (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1 : ℝ) ^ 2) :=
    summable_one_div_odd_sq.alternating.congr fun k => by push_cast; ring
  exact hs.hasSum

/-! ### The function `log(1 + x²)` -/

/-- `log(1+x²) ≥ 0`. -/
public theorem log_one_add_sq_nonneg (x : ℝ) : 0 ≤ Real.log (1 + x ^ 2) :=
  Real.log_nonneg (le_add_of_nonneg_right (sq_nonneg x))

/-- `log(1+x²) ≤ x²`, from `log y ≤ y - 1`. -/
public theorem log_one_add_sq_le_sq (x : ℝ) : Real.log (1 + x ^ 2) ≤ x ^ 2 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)
  linarith

/-- The power series of `log(1+x²)/x` on `(0, 1)`: `∑_{n ≥ 0} (-1)ⁿ x^(2n+1)/(n+1)`. -/
public theorem hasSum_log_one_add_sq_div {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) * x ^ (2 * n + 1))
      (Real.log (1 + x ^ 2) / x) := by
  have habs : |-x ^ 2| < 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg x)]
    nlinarith [hx.1, hx.2]
  have h := ((Real.hasSum_pow_div_log_of_abs_lt_one habs).neg).div_const x
  rw [sub_neg_eq_add, neg_neg] at h
  refine h.congr_fun fun n => ?_
  have hx0 : x ≠ 0 := hx.1.ne'
  field_simp
  ring

/-- A function `f : ℝ → ℝ` that is continuous away from `0`, vanishes at `0` and is dominated by a
function tending to `0` at `0` is continuous. -/
public theorem continuous_of_norm_le_of_tendsto_zero {f g : ℝ → ℝ} (hf : ∀ x ≠ 0, ContinuousAt f x)
    (hf0 : f 0 = 0) (hle : ∀ x, ‖f x‖ ≤ g x) (hg : Tendsto g (𝓝 0) (𝓝 0)) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, hf0]
    exact squeeze_zero_norm hle hg
  · exact hf x hx

/-- `x ↦ log(1+x²)/x` is continuous on `ℝ` (its value at `0` is `0`). -/
public theorem continuous_log_one_add_sq_div :
    Continuous fun x : ℝ => Real.log (1 + x ^ 2) / x := by
  refine continuous_of_norm_le_of_tendsto_zero (g := fun x => |x|) (fun x hx => ?_) (by simp)
    (fun x => ?_) ?_
  · have h1 : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (log_one_add_sq_nonneg x),
      div_le_iff₀ (abs_pos.2 hx)]
    nlinarith [log_one_add_sq_le_sq x, sq_abs x, abs_nonneg x]
  · exact continuous_abs.tendsto' 0 0 abs_zero

/-- `x ↦ log²(1+x²)/x³` is continuous on `ℝ` (its value at `0` is `0`). -/
public theorem continuous_log_one_add_sq_sq_div_cube :
    Continuous fun x : ℝ => Real.log (1 + x ^ 2) ^ 2 / x ^ 3 := by
  refine continuous_of_norm_le_of_tendsto_zero (g := fun x => |x|) (fun x hx => ?_) (by simp)
    (fun x => ?_) ?_
  · have h1 : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    have h2 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
    fun_prop (disch := assumption)
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hL0 := log_one_add_sq_nonneg x
    have hx3 : 0 < |x| ^ 3 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_pow, abs_of_nonneg hL0, div_le_iff₀ hx3]
    calc Real.log (1 + x ^ 2) ^ 2 ≤ (x ^ 2) ^ 2 := pow_le_pow_left₀ hL0 (log_one_add_sq_le_sq x) 2
      _ = |x| * |x| ^ 3 := by rw [← sq_abs x]; ring
  · exact continuous_abs.tendsto' 0 0 abs_zero

end LeanPolyLog.Series
