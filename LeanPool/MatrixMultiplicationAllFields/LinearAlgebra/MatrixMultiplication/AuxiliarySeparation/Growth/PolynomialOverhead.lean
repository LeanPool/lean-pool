/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Removing polynomial overhead from exponential inequalities

The interpolation argument in Section 4 bounds tensor powers with an extra
linear factor. Such a factor does not change their exponential growth rate.
The statements below include eventual inequalities and constant factors, so
the same argument also removes fixed counting losses in entropy limits.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- An eventual linear prefactor cannot increase an exponential growth rate. -/
theorem le_of_eventually_pow_le_linear_mul_pow {a b K C : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ ((j : ℝ) * K + C) * a ^ j) :
    b ≤ a := by
  by_contra hba
  have hab : a < b := lt_of_not_ge hba
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hr₀ : 0 ≤ a / b := div_nonneg ha hb.le
  have hr₁ : a / b < 1 := (div_lt_one hb).2 hab
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hr₀ hr₁).mul_const K
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).const_mul C
  have hlim : Tendsto (fun j : ℕ => ((j : ℝ) * K + C) * (a / b) ^ j)
      atTop (𝓝 0) := by
    convert hlinear.add hconstant using 1 <;> try simp
    funext j
    ring
  have hbound : ∀ᶠ j : ℕ in atTop,
      1 ≤ ((j : ℝ) * K + C) * (a / b) ^ j := by
    filter_upwards [h] with j hj
    have hdiv := (div_le_div_iff_of_pos_right (pow_pos hb j)).2 hj
    simpa only [div_self (pow_ne_zero j hb.ne'), mul_div_assoc, div_pow] using hdiv
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim hbound
  linarith

/-- Removing the linear interpolation overhead from inequalities for all powers. -/
theorem le_of_pow_le_linear_mul_pow {a b K : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ ((j : ℝ) * K + 1) * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_linear_mul_pow ha (Eventually.of_forall h)

/-- Fixed multiplicative losses disappear on taking exponential growth rates. -/
theorem le_of_eventually_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ C * a ^ j) : b ≤ a := by
  apply le_of_eventually_pow_le_linear_mul_pow (K := 0) (C := C) ha
  simpa only [mul_zero, zero_add] using h

/-- An all-powers form of constant-factor removal. -/
theorem le_of_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ C * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_const_mul_pow ha (Eventually.of_forall h)

/-- In particular, the fixed factor five in the type-counting bound is harmless. -/
theorem le_of_pow_le_five_mul_pow {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ 5 * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_const_mul_pow ha (Eventually.of_forall h)

/-- A fixed counting loss does not contribute to a normalized logarithmic
growth rate. The exponent may run through any sequence tending to infinity,
including the multiples of a common denominator used for rational types. -/
theorem exp_le_of_tendsto_log_div {u : ℕ → ℝ} {n : ℕ → ℕ} {b C L : ℝ}
    (hb : 0 < b) (hC : 0 < C) (hn : Tendsto n atTop atTop)
    (hu : ∀ᶠ k in atTop, 0 < u k)
    (hlim : Tendsto (fun k => Real.log (u k) / (n k : ℝ)) atTop (𝓝 L))
    (hbound : ∀ᶠ k in atTop, u k ≤ C * b ^ n k) :
    Real.exp L ≤ b := by
  have hconstant : Tendsto (fun k => Real.log C / (n k : ℝ) + Real.log b)
      atTop (𝓝 (Real.log b)) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).comp hn).add_const
      (Real.log b)
  have hnormalized : ∀ᶠ k in atTop,
      Real.log (u k) / (n k : ℝ) ≤ Real.log C / (n k : ℝ) + Real.log b := by
    filter_upwards [hu, hbound, hn.eventually (eventually_gt_atTop 0)] with k huk hk hnk
    have hnpos : (0 : ℝ) < n k := by exact_mod_cast hnk
    have hlog := Real.log_le_log huk hk
    rw [Real.log_mul hC.ne' (pow_ne_zero _ hb.ne'), Real.log_pow] at hlog
    calc
      Real.log (u k) / (n k : ℝ) ≤
          (Real.log C + (n k : ℝ) * Real.log b) / (n k : ℝ) :=
        (div_le_div_iff_of_pos_right hnpos).2 hlog
      _ = Real.log C / (n k : ℝ) + Real.log b := by
        field_simp
  have hL : L ≤ Real.log b := le_of_tendsto_of_tendsto hlim hconstant hnormalized
  simpa only [Real.exp_log hb] using Real.exp_le_exp.mpr hL

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
