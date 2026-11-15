/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
import Mathlib.Analysis.MeanInequalities

/-!
# The exponents `c 2` and `c 3`

The infimum defining `c p` is attained where the weighted arithmetic-geometric mean inequality is
tight. For `p = 2` this is at `x = 1 / 2`, which gives `c 2 = 5 / 3 - logb 2 3`. For `p = 3` it is
at the root `a = (√33 - 1) / 8` of `4 * a ^ 2 + a - 2`, which gives
`c 3 = 1 - log b / log 3` with `b = a ^ (-2 / 3) + a ^ (1 / 3) + a ^ (4 / 3)`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.c_two`: `c 2 = 5 / 3 - logb 2 3`.
* `ArithmeticTriangleRemovalInVectorSpaces.c_three`: the value of `c 3`.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- If the function defining `c p` attains its infimum over `Set.Ioo 0 1` at `a`, then `c p` is
`1 - logb p` of its value at `a`. -/
private lemma c_eq_one_sub_logb {p : ℕ} (hp : 2 ≤ p) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (h : ∀ x : ℝ, 0 < x → x < 1 → a ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, a ^ j ≤
      x ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, x ^ j) :
    c p = 1 - Real.logb p (a ^ (-((p : ℝ) - 1) / 3) * ∑ j ∈ range p, a ^ j) := by
  rw [← le_antisymm (rpow_one_sub_c_le hp ha₀ ha₁) (le_rpow_one_sub_c hp h),
    Real.logb_rpow (by positivity) (by exact_mod_cast (by grind : p ≠ 1))]
  ring

/-- The weighted arithmetic-geometric mean inequality with weights `2 / 3` and `1 / 3`:
`(1 / 2) ^ (-1 / 3) * (3 / 2) ≤ x ^ (-1 / 3) * (1 + x)`. -/
private lemma rpow_mul_one_add_le {x : ℝ} (hx : 0 < x) :
    (1 / 2 : ℝ) ^ (-(1 / 3) : ℝ) * (3 / 2) ≤ x ^ (-(1 / 3) : ℝ) * (1 + x) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 2 / 3) (w₂ := 1 / 3)
    (p₁ := 3 / 2) (p₂ := 3 / 2 * (x / (1 / 2))) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by norm_num)
  rw [Real.mul_rpow (by norm_num) (by positivity), ← mul_assoc, ← Real.rpow_add (by norm_num),
    (by norm_num : (2 / 3 : ℝ) + 1 / 3 = 1), Real.rpow_one,
    (by field_simp : 2 / 3 * (3 / 2 : ℝ) + 1 / 3 * (3 / 2 * (x / (1 / 2))) = 1 + x),
    Real.div_rpow hx.le (by norm_num), mul_div_assoc', div_le_iff₀ (by positivity)] at h
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg hx.le, inv_mul_eq_div, inv_mul_eq_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- The weighted arithmetic-geometric mean inequality for `1`, `x / a` and `(x / a) ^ 2` with
weights proportional to `1`, `a` and `a ^ 2`, where `4 * a ^ 2 + a - 2 = 0`:
`(x / a) ^ (2 / 3) ≤ (1 + x + x ^ 2) / (1 + a + a ^ 2)`. -/
private lemma div_rpow_two_div_three_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hw : 4 * a ^ 2 + a - 2 = 0) :
    (x / a) ^ (2 / 3 : ℝ) ≤ (1 + x + x ^ 2) / (1 + a + a ^ 2) := by
  have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / (1 + a + a ^ 2))
    (w₂ := a / (1 + a + a ^ 2)) (w₃ := a ^ 2 / (1 + a + a ^ 2)) (p₁ := 1) (p₂ := x / a)
    (p₃ := (x / a) ^ 2) (by positivity) (by positivity) (by positivity) zero_le_one
    (by positivity) (by positivity) (by field_simp)
  rw [Real.one_rpow, one_mul, ← Real.rpow_natCast_mul (by positivity),
    ← Real.rpow_add (by positivity)] at h
  convert h using 2
  · field_simp
    push_cast
    linarith
  · field_simp

/-- The weighted arithmetic-geometric mean inequality with weights proportional to `1`, `a` and
`a ^ 2`, where `4 * a ^ 2 + a - 2 = 0`:
`a ^ (-2 / 3) * (1 + a + a ^ 2) ≤ x ^ (-2 / 3) * (1 + x + x ^ 2)`. -/
private lemma rpow_mul_one_add_add_sq_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hw : 4 * a ^ 2 + a - 2 = 0) :
    a ^ (-(2 / 3) : ℝ) * (1 + a + a ^ 2) ≤ x ^ (-(2 / 3) : ℝ) * (1 + x + x ^ 2) := by
  have h := div_rpow_two_div_three_le ha hx hw
  rw [Real.div_rpow hx.le ha.le, div_le_div_iff₀ (by positivity) (by positivity)] at h
  rw [Real.rpow_neg ha.le, Real.rpow_neg hx.le, inv_mul_eq_div, inv_mul_eq_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- The exponent `c 2` is `5 / 3 - logb 2 3`. -/
theorem c_two : c 2 = 5 / 3 - Real.logb 2 3 := by
  rw [c_eq_one_sub_logb le_rfl (a := 1 / 2) (by norm_num) (by norm_num) ?_]
  · norm_num [sum_range_succ]
    rw [Real.logb_mul (by positivity) (by norm_num), Real.logb_rpow_eq_mul_logb_of_pos
      (by norm_num), Real.logb_div (by norm_num) (by norm_num), Real.logb_div (by norm_num)
      (by norm_num), Real.logb_one, Real.logb_self_eq_one (by norm_num)]
    ring
  · intro x hx₀ hx₁
    norm_num [sum_range_succ]
    exact rpow_mul_one_add_le hx₀

/-- With `a = (√33 - 1) / 8` and `b = a ^ (-2 / 3) + a ^ (1 / 3) + a ^ (4 / 3)`, the exponent
`c 3` is `1 - log b / log 3`. -/
theorem c_three {a : ℝ} (ha : a = (√33 - 1) / 8) :
    c 3 = 1 - Real.log (a ^ (-2 / 3 : ℝ) + a ^ (1 / 3 : ℝ) + a ^ (4 / 3 : ℝ)) / Real.log 3 := by
  have h33 : √33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  obtain ⟨ha₀, ha₁⟩ : 0 < a ∧ a < 1 := by
    rw [ha]
    constructor <;> nlinarith [Real.sqrt_nonneg 33]
  rw [c_eq_one_sub_logb (by norm_num) ha₀ ha₁ ?_]
  · norm_num [sum_range_succ]
    rw [Real.logb, mul_add, mul_add, mul_one, ← Real.rpow_add_one ha₀.ne',
      ← Real.rpow_add_natCast ha₀.ne']
    norm_num
  · intro x hx₀ hx₁
    norm_num [sum_range_succ]
    apply rpow_mul_one_add_add_sq_le ha₀ hx₀
    rw [ha]
    linear_combination h33 / 16

end ArithmeticTriangleRemovalInVectorSpaces
