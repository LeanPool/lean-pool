/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeLogIntervals
public import LeanPool.NairTenenbaum.Hooley.HooleyMomentComparison

/-! # Sampling Hooley windows at prime logarithms

The local integral comparison and the bounded prime mass on logarithmic
intervals control the sampled moments, uniformly in the translation and
the finite set of primes. This is the elementary input to the mixed-term
bound in the weighted mean argument.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real MeasureTheory

/-- A finite collection of local integral majorants can be summed when
their weighted overlap is bounded. -/
theorem finite_sampling_le_integral {ι : Type*} (S : Finset ι)
    (w t : ι → ℝ) {f : ℝ → ℝ} (hf : Integrable f) (hf₀ : ∀ v, 0 ≤ f v)
    {A C : ℝ} (hA : 0 ≤ A) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hlocal : ∀ i ∈ S, f (t i) ≤ A * ∫ v in Set.Ioc (t i - 1) (t i + 1), f v)
    (hoverlap : ∀ v, (∑ i ∈ S.filter (fun i => v ∈ Set.Ioc (t i - 1) (t i + 1)), w i) ≤ C) :
    (∑ i ∈ S, w i * f (t i)) ≤ A * C * ∫ v, f v := by
  classical
  let F (i : ι) (v : ℝ) := w i * (Set.Ioc (t i - 1) (t i + 1)).indicator f v
  have hi (i : ι) : Integrable (F i) := (hf.indicator measurableSet_Ioc).const_mul (w i)
  have hsum : (∑ i ∈ S, w i * ∫ v in Set.Ioc (t i - 1) (t i + 1), f v) =
      ∫ v, ∑ i ∈ S, F i v := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    apply sum_congr rfl
    intro i hiS
    change _ = ∫ v, w i * (Set.Ioc (t i - 1) (t i + 1)).indicator f v
    rw [integral_const_mul, integral_indicator measurableSet_Ioc]
  have hpoint (v : ℝ) : (∑ i ∈ S, F i v) ≤ C * f v := by
    have Heq : (∑ i ∈ S, F i v) =
        (∑ i ∈ S.filter (fun i => v ∈ Set.Ioc (t i - 1) (t i + 1)), w i) * f v := by
      rw [sum_filter, sum_mul]
      apply sum_congr rfl
      intro i hiS
      by_cases h : v ∈ Set.Ioc (t i - 1) (t i + 1) <;> simp [F, h]
    rw [Heq]
    exact mul_le_mul_of_nonneg_right (hoverlap v) (hf₀ v)
  calc
    _ ≤ ∑ i ∈ S, w i * (A * ∫ v in Set.Ioc (t i - 1) (t i + 1), f v) :=
      sum_le_sum fun i hiS => mul_le_mul_of_nonneg_left (hlocal i hiS) (hw i hiS)
    _ = A * (∑ i ∈ S, w i * ∫ v in Set.Ioc (t i - 1) (t i + 1), f v) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hiS
      ring
    _ = A * ∫ v, ∑ i ∈ S, F i v := by rw [hsum]
    _ ≤ A * ∫ v, C * f v := mul_le_mul_of_nonneg_left
      (integral_mono (integrable_finsetSum _ (fun i _ => hi i)) (hf.const_mul C) hpoint) hA
    _ = _ := by rw [integral_const_mul]; ring

theorem prime_log_overlap_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (u v : ℝ) :
    (∑ p ∈ S.filter (fun p : ℕ => v ∈ Set.Ioc (u - Real.log p - 1) (u - Real.log p + 1)),
      Real.log p / p) ≤ Real.log 4 * Real.exp 2 := by
  apply le_trans _ (prime_log_mass_log_interval S hS (u - v - 1))
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpS, hpv⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hpS, by obtain ⟨h₁, h₂⟩ := hpv; constructor <;> linarith⟩
  · intro p hp _
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hS p (mem_filter.mp hp).1).one_le))
      (Nat.cast_nonneg _)

/-- Uniform prime sampling of every positive integral moment. -/
theorem prime_sampled_hooleyWindow_pow_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (n : ℕ) {q : ℕ} (hq : 0 < q) (u : ℝ) :
    (∑ p ∈ S, (Real.log p / p) * hooleyWindow n (u - Real.log p) ^ q) ≤
      (2 : ℝ) ^ (q - 1) * (Real.log 4 * Real.exp 2) * hooleyMoment q n := by
  apply finite_sampling_le_integral S (fun p => Real.log p / p) (fun p => u - Real.log p)
    (integrable_hooleyWindow_pow n hq) (fun v => pow_nonneg (hooleyWindow_nonneg n v) q)
    (by positivity)
  · intro p hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hS p hp).one_le)) (Nat.cast_nonneg _)
  · intro p hp
    simpa only [intervalIntegral.integral_of_le (by
      linarith : u - Real.log p - 1 ≤ u - Real.log p + 1)]
      using hooleyWindow_pow_le_localIntegral n hq (u - Real.log p)
  · intro v
    exact prime_log_overlap_bound S hS u v

end NairTenenbaum
