/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Monotone multiplicative functions on the positive natural numbers

The scalar classification used in Section 3.1: positivity, multiplicativity,
and monotonicity force a function on positive natural numbers to be a real
power. No property of the function at zero is required.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

/-- Multiplicativity and positivity determine the value at one. -/
theorem positiveMultiplicative_one
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) :
    f 1 = 1 := by
  have hm := hmul 1 1 (by omega) (by omega)
  have hp := hpos 1 (by omega)
  norm_num at hm
  nlinarith

/-- A positive multiplicative function preserves natural powers. -/
theorem positiveMultiplicative_pow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : f (n ^ k) = f n ^ k := by
  induction k with
  | zero => simpa using positiveMultiplicative_one hpos hmul
  | succ k ih =>
      rw [pow_succ, hmul (n ^ k) n (pow_pos hn k) hn, ih, pow_succ]

/-- Monotonicity transfers comparisons of natural powers to the values. -/
theorem positiveMultiplicative_pow_le_pow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {j k : ℕ}
    (h : m ^ j ≤ n ^ k) : f m ^ j ≤ f n ^ k := by
  rw [← positiveMultiplicative_pow hpos hmul hm,
    ← positiveMultiplicative_pow hpos hmul hn]
  exact hmono (pow_pos hm j) (pow_pos hn k) h

/-- The same comparison after taking logarithms. -/
theorem positiveMultiplicative_log_pow_le
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {j k : ℕ}
    (h : m ^ j ≤ n ^ k) :
    (j : ℝ) * Real.log (f m) ≤ (k : ℝ) * Real.log (f n) := by
  have hv := positiveMultiplicative_pow_le_pow hpos hmul hmono hm hn h
  simpa only [Real.log_pow] using
    Real.log_le_log (pow_pos (hpos m hm) j) hv

/-- Bounds from neighboring powers of two have a fixed logarithmic error,
independent of the exponent `k`. -/
theorem positiveMultiplicative_log_error_bounds
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k : ℝ) * (Real.log (f n) * Real.log 2 -
      Real.log (n : ℝ) * Real.log (f 2)) ≤ Real.log (f 2) * Real.log 2 ∧
    (k : ℝ) * (Real.log (n : ℝ) * Real.log (f 2) -
      Real.log (f n) * Real.log 2) ≤ Real.log (f 2) * Real.log 2 := by
  have hf2 : 0 ≤ Real.log (f 2) := by
    apply Real.log_nonneg
    have hm := hmono (show (1 : ℕ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℕ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
    rwa [positiveMultiplicative_one hpos hmul] at hm
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨m, hlow, hupp⟩ :=
    exists_nat_pow_near (show 1 ≤ n ^ k from Nat.one_le_iff_ne_zero.mpr (by positivity))
      (show 1 < (2 : ℕ) by omega)
  have hflow := positiveMultiplicative_log_pow_le hpos hmul hmono
    (show 0 < (2 : ℕ) by omega) hn hlow
  have hfupp := positiveMultiplicative_log_pow_le hpos hmul hmono hn
    (show 0 < (2 : ℕ) by omega) hupp.le
  have hlow' : (2 : ℝ) ^ m ≤ (n : ℝ) ^ k := by exact_mod_cast hlow
  have hupp' : (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hupp.le
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) m) hlow'
  have hnupp := Real.log_le_log (pow_pos hnp k) hupp'
  simp only [Real.log_pow, Nat.cast_add, Nat.cast_one] at hflow hfupp hnlow hnupp
  have h₁ := mul_le_mul_of_nonneg_right hfupp hlog2
  have h₂ := mul_le_mul_of_nonneg_right hnlow hf2
  have h₃ := mul_le_mul_of_nonneg_right hnupp hf2
  have h₄ := mul_le_mul_of_nonneg_right hflow hlog2
  constructor <;> nlinarith

/-- If every natural multiple of both differences has a common upper bound,
the two real numbers coincide. -/
theorem eq_of_nat_mul_sub_bounded {x y C : ℝ}
    (hxy : ∀ k : ℕ, (k : ℝ) * (x - y) ≤ C)
    (hyx : ∀ k : ℕ, (k : ℝ) * (y - x) ≤ C) : x = y := by
  apply le_antisymm
  · by_contra h
    have hd : 0 < x - y := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (x - y))
    have hk' : C < (k : ℝ) * (x - y) := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hxy k)) hk'
  · by_contra h
    have hd : 0 < y - x := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / (y - x))
    have hk' : C < (k : ℝ) * (y - x) := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hyx k)) hk'

/-- The logarithmic exponent is the same at every positive natural number. -/
theorem positiveMultiplicative_log_eq
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    Real.log (f n) = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by
  have heq : Real.log (f n) * Real.log 2 =
      Real.log (n : ℝ) * Real.log (f 2) :=
    eq_of_nat_mul_sub_bounded
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).1)
      (fun k => (positiveMultiplicative_log_error_bounds hpos hmul hmono hn k).2)
  calc
    Real.log (f n) = (Real.log (n : ℝ) * Real.log (f 2)) / Real.log 2 :=
      (eq_div_iff (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne').2 heq
    _ = Real.log (n : ℝ) * (Real.log (f 2) / Real.log 2) := by ring

/-- The explicit exponent in the classification of positive monotone
multiplicative functions on the positive natural numbers. -/
theorem positiveMultiplicative_eq_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0))
    {n : ℕ} (hn : 0 < n) :
    f n = (n : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnp, ← positiveMultiplicative_log_eq hpos hmul hmono hn,
    Real.exp_log (hpos n hn)]

/-- Every positive monotone multiplicative function on the positive natural
numbers is a nonnegative real power, as used in Section 3.1. -/
theorem positiveMultiplicative_is_rpow
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hmono : MonotoneOn f (Set.Ioi 0)) :
    ∃ p : ℝ, 0 ≤ p ∧ ∀ n : ℕ, 0 < n → f n = (n : ℝ) ^ p := by
  refine ⟨Real.log (f 2) / Real.log 2, ?_, fun n hn =>
    positiveMultiplicative_eq_rpow hpos hmul hmono hn⟩
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply Real.log_nonneg
  have hm := hmono (show (1 : ℕ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℕ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
  rwa [positiveMultiplicative_one hpos hmul] at hm

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
