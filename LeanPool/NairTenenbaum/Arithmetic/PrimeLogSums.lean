/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.Chebyshev

/-! # Elementary weighted prime sums

Chebyshev's bound and partial summation control the logarithmically weighted
prime sums required in the smooth-tail estimate. No prime number theorem is used.
-/

@[expose] public section

namespace NairTenenbaum

open Real Finset MeasureTheory intervalIntegral

/-- The logarithmic weight supported on primes. -/
noncomputable def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- The partial sum of the prime logarithmic weights. -/
noncomputable def primeLogSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p / p

theorem primeLogWeight_sum (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

/-- An explicit partial-summation identity. -/
theorem primeLogSum_eq {x : ℝ} (hx : 2 ≤ x) :
    primeLogSum x = Chebyshev.theta x / x + ∫ t in (2 : ℝ)..x, Chebyshev.theta t / t ^ 2 := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc 2 x) : HasDerivAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) t := by
    convert hasDerivAt_inv (show t ≠ 0 by linarith [ht.1]) using 1
  have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 2 x) :=
    ((continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (by
      change t ≠ 0; linarith [ht.1]))).neg
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc 2 x) :=
    hc.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have H := sum_mul_eq_sub_integral_mul₁ primeLogWeight
    (by simp [primeLogWeight]) (by simp [primeLogWeight]) x
    (fun t ht => (hd t ht).differentiableAt) hi
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ)⁻¹ * primeLogWeight n) = primeLogSum x := by
    simp only [primeLogSum, primeLogWeight, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  rw [hsum, primeLogWeight_sum] at H
  simp_rw [primeLogWeight_sum] at H
  rw [setIntegral_congr_fun measurableSet_Ioc
    (g := fun t => -(Chebyshev.theta t / t ^ 2))
    (fun t ht => by rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv]; ring),
    MeasureTheory.integral_neg, ← intervalIntegral.integral_of_le hx] at H
  simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using H

/-- The weighted prime sum is `O(log x)` with an elementary explicit bound. -/
theorem primeLogSum_le {x : ℝ} (hx : 2 ≤ x) :
    primeLogSum x ≤ Real.log 4 * (1 + Real.log x) := by
  have hx₀ : 0 < x := by linarith
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    exact (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (by
      change t ≠ 0; linarith [ht.1]))
  have hi : IntervalIntegrable (fun t => Chebyshev.theta t / t ^ 2) volume 2 x := by
    simpa only [div_eq_mul_inv, mul_comm] using
      Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hc
  have hc' : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    exact continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hi' : IntervalIntegrable (fun t : ℝ => Real.log 4 * t⁻¹) volume 2 x :=
    hc'.intervalIntegrable.const_mul _
  have hb : (∫ t in (2 : ℝ)..x, Chebyshev.theta t / t ^ 2) ≤
      Real.log 4 * Real.log (x / 2) := by
    rw [← integral_inv_of_pos (by
      norm_num : (0 : ℝ) < 2) hx₀, ← intervalIntegral.integral_const_mul]
    apply integral_mono_on hx hi hi'
    intro t ht
    have ht₀ : 0 < t := by linarith [ht.1]
    calc
      _ ≤ (Real.log 4 * t) / t ^ 2 :=
        div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x ht₀.le) (sq_nonneg t)
      _ = _ := by field_simp
  have ht : Chebyshev.theta x / x ≤ Real.log 4 :=
    (div_le_iff₀ hx₀).mpr (Chebyshev.theta_le_log4_mul_x hx₀.le)
  rw [primeLogSum_eq hx]
  have hl₄ : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl₂ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Real.log_div hx₀.ne' (by norm_num)] at hb
  nlinarith

theorem exp_sub_one_le_mul_exp (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_nonneg t)
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

/-- First-prime-power increment bound used by the exponential moment. -/
theorem prime_rpow_gap_sum_le {x β K : ℝ} (hx : 2 ≤ x) (hβ : 0 ≤ β)
    (hK : β * Real.log x ≤ K) :
    (∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime, ((p : ℝ) ^ β - 1) / p) ≤
      β * Real.exp K * (Real.log 4 * (1 + Real.log x)) := by
  have hx₀ : 0 ≤ x := by linarith
  calc
    _ ≤ ∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
        (β * Real.exp K) * (Real.log p / p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpx, hpp⟩ := Finset.mem_filter.mp hp
      have hp₀ : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
      have hpx' : (p : ℝ) ≤ x := (Nat.le_floor_iff hx₀).mp (Finset.mem_Icc.mp hpx).2
      have hlp : 0 ≤ Real.log p := Real.log_nonneg hp₁
      have hlog : Real.log p * β ≤ K :=
        (mul_le_mul_of_nonneg_right (Real.log_le_log hp₀ hpx') hβ).trans (by
          simpa [mul_comm] using hK)
      have hgap : (p : ℝ) ^ β - 1 ≤ (Real.log p * β) * Real.exp K := by
        rw [Real.rpow_def_of_pos hp₀]
        exact (exp_sub_one_le_mul_exp _).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlog) (mul_nonneg hlp hβ))
      calc
        _ ≤ ((Real.log p * β) * Real.exp K) / p :=
          div_le_div_of_nonneg_right hgap hp₀.le
        _ = _ := by ring
    _ = (β * Real.exp K) * primeLogSum x := by rw [← Finset.mul_sum]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeLogSum_le hx) (mul_nonneg hβ (Real.exp_nonneg K))

/-- Choosing `β=κ/log x` bounds the prime increments uniformly in the cutoff. -/
theorem prime_rpow_gap_sum_uniform {x κ : ℝ} (hx : 2 ≤ x) (hκ : 0 ≤ κ) :
    (∑ p ∈ (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime,
      ((p : ℝ) ^ (κ / Real.log x) - 1) / p) ≤
      κ * Real.exp κ * Real.log 4 * (1 + (Real.log 2)⁻¹) := by
  have hx₁ : 1 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx₁
  have hl₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hi : (Real.log x)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hl₂ hlog
  refine (prime_rpow_gap_sum_le hx (div_nonneg hκ hlx.le) (by
    rw [div_mul_cancel₀ _ hlx.ne'])).trans ?_
  calc
    _ = (κ * Real.exp κ * Real.log 4) * (1 + (Real.log x)⁻¹) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (mul_nonneg hκ (Real.exp_nonneg κ)) (Real.log_nonneg (by norm_num)))

end NairTenenbaum
