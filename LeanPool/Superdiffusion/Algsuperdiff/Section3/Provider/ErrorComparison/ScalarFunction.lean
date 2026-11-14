/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# ScalarFunction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the scalar function `f(x) = x⁻¹ (x-1)²`

This file isolates, over abstract reals, the scalar analysis used in the proof
of the second inequality of `e.bound.Lambdas.by.Es` in ABK26.

The printed proof introduces `f(x) := x^{-1}(x-1)^2`, observes that `f` is the
eigenvalue function of the operator inequalities
`e.xminusonetimesxminusonesquared.sstar` and
`e.xminusonetimesxminusonesquared.b`, and then uses the two elementary facts

> for every `δ, ε > 0`, `f(x) ≤ δ` implies `x - 1 ≤ δ + δ^{1/2} ≤ (1+ε^{-1})δ +
> (1/4)ε`

together with the optimization in `ε` performed afterwards.

Everything here is stated for real numbers only; no matrix, cube or coefficient
data appears.

## Main results

* `invMulSubOneSq_le_add_sub_two`: the two-sided pairing `f(x) ≤ x + y - 2`
  whenever `1 ≤ x * y`, which is how the printed operator inequalities are used
  at the level of quadratic forms;
* `sub_one_le_add_sqrt_of_invMulSubOneSq_le`: `f(x) ≤ δ → x - 1 ≤ δ + δ^{1/2}`;
* `sqrt_le_inv_mul_add_quarter`: `δ^{1/2} ≤ ε⁻¹ δ + ε/4`;
* `le_one_add_of_invMulSubOneSq_le`: the combined `ε`-linearized bound
  `f(x) ≤ δ → x ≤ 1 + (1 + ε⁻¹) δ + ε/4`;
* `le_add_sqrt_two_mul_of_forall_pos`: the optimization in `ε`.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

/-- The scalar function `f(x) = x^{-1} (x-1)^2` of ABK26. -/
noncomputable def invMulSubOneSq (x : ℝ) : ℝ := x⁻¹ * (x - 1) ^ 2

/-- On the positive half-line, `f(x) = x + x^{-1} - 2`.  This is the identity
behind the printed algebraic identity closing
`e.xminusonetimesxminusonesquared.sstar`. -/
theorem invMulSubOneSq_eq_add_inv_sub_two {x : ℝ} (hx : 0 < x) :
    invMulSubOneSq x = x + x⁻¹ - 2 := by
  unfold invMulSubOneSq
  field_simp
  ring

/-- If `x, y > 0` satisfy `1 ≤ x * y`, then `f(x) ≤ x + y - 2`.

This is the scalar shadow of the printed operator inequalities: the quadratic
forms of the two normalized coarse matrices always have product at least one,
and their sum minus `2` therefore dominates `f` of either one. -/
theorem invMulSubOneSq_le_add_sub_two {x y : ℝ} (hx : 0 < x)
    (hxy : 1 ≤ x * y) : invMulSubOneSq x ≤ x + y - 2 := by
  have hinv : x⁻¹ ≤ y := by
    have hmul := mul_le_mul_of_nonneg_left hxy (inv_nonneg.2 hx.le)
    rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul] at hmul
  rw [invMulSubOneSq_eq_add_inv_sub_two hx]
  linarith

/-- The printed implication "`f(x) ≤ δ` implies `x - 1 ≤ δ + δ^{1/2}`" (ABK26).
-/
theorem sub_one_le_add_sqrt_of_invMulSubOneSq_le {x δ : ℝ} (hx : 0 < x)
    (hδ : 0 ≤ δ) (h : invMulSubOneSq x ≤ δ) : x - 1 ≤ δ + Real.sqrt δ := by
  have hr0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hrsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ
  have hkey : (x - 1) ^ 2 ≤ δ * x := by
    have hmul := mul_le_mul_of_nonneg_left h hx.le
    rwa [invMulSubOneSq, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul,
      mul_comm] at hmul
  have hprod : (x - 1 - Real.sqrt δ ^ 2 - Real.sqrt δ) * (x - 1 + Real.sqrt δ) ≤
      -(Real.sqrt δ ^ 3) := by
    rw [hrsq]
    nlinarith [hkey, hrsq]
  rcases le_or_gt (x - 1 + Real.sqrt δ) 0 with hle | hlt
  · nlinarith [hrsq, hr0]
  · nlinarith [hprod, hlt, pow_nonneg hr0 3, hrsq]

/-- The elementary Young inequality `r ≤ ε^{-1} r² + (1/4) ε`. -/
theorem le_inv_mul_sq_add_quarter (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    r ≤ ε⁻¹ * r ^ 2 + ε / 4 := by
  have hkey : ε⁻¹ * r ^ 2 + ε / 4 - r = ε⁻¹ * (r - ε / 2) ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ ε⁻¹ * (r - ε / 2) ^ 2 :=
    mul_nonneg (inv_nonneg.2 hε.le) (sq_nonneg _)
  linarith

/-- The printed inequality `δ^{1/2} ≤ ε^{-1} δ + (1/4) ε` (ABK26). -/
theorem sqrt_le_inv_mul_add_quarter {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    Real.sqrt δ ≤ ε⁻¹ * δ + ε / 4 := by
  have hrsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ
  have hkey := le_inv_mul_sq_add_quarter (Real.sqrt δ) hε
  rw [hrsq] at hkey
  exact hkey

/-- The `ε`-linearized form of the printed implication: `f(x) ≤ δ` implies
`x ≤ 1 + (1 + ε^{-1}) δ + (1/4) ε`. -/
theorem le_one_add_of_invMulSubOneSq_le {x δ ε : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ)
    (hε : 0 < ε) (h : invMulSubOneSq x ≤ δ) :
    x ≤ 1 + (1 + ε⁻¹) * δ + ε / 4 := by
  have h1 := sub_one_le_add_sqrt_of_invMulSubOneSq_le hx hδ h
  have h2 := sqrt_le_inv_mul_add_quarter hδ hε
  nlinarith [h1, h2]

/-- The optimization in `ε` performed on ABK26: if `x ≤ K + 2 ε^{-1} A² + (1/4)
ε` for every `ε > 0`, then `x ≤ K + 2^{1/2} A`. -/
theorem le_add_sqrt_two_mul_of_forall_pos {x K A : ℝ} (hA : 0 ≤ A)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ K + 2 * ε⁻¹ * A ^ 2 + ε / 4) :
    x ≤ K + Real.sqrt 2 * A := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hxK : x ≤ K := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hx := h (4 * ε) (by linarith)
      rw [← hA0] at hx
      simpa using hx
    have : Real.sqrt 2 * A = 0 := by rw [← hA0]; ring
    linarith
  · have hr : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hrsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hεpos : (0 : ℝ) < 2 * Real.sqrt 2 * A := by positivity
    have hx := h _ hεpos
    have heq : 2 * (2 * Real.sqrt 2 * A)⁻¹ * A ^ 2 + 2 * Real.sqrt 2 * A / 4 =
        Real.sqrt 2 * A := by
      field_simp
      nlinarith [hrsq, hApos]
    linarith

end Algsuperdiff.Section3.Provider.ErrorComparison
