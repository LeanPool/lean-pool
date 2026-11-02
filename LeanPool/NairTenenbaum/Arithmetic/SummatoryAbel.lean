/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.ConvolutionMean
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.NumberTheory.AbelSummation

/-! # Partial summation for real arithmetic summatory functions -/

@[expose] public section

namespace NairTenenbaum

open Finset MeasureTheory intervalIntegral

theorem arithmeticSummatory_eq_sum_Icc_zero {a : ℕ → ℝ} (ha : a 0 = 0) (x : ℝ) :
    arithmeticSummatory a x = ∑ n ∈ Icc 0 ⌊x⌋₊, a n := by
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), ha, zero_add, ← Icc_succ_left_eq_Ioc]
  rfl

theorem arithmeticSummatory_mono {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    Monotone (arithmeticSummatory a) := by
  intro x y hxy
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.floor_mono hxy))
    (fun n _ _ => ha n)

theorem arithmeticSummatory_mul_eq_sub_integral {a : ℕ → ℝ} (ha : a 0 = 0)
    {f g : ℝ → ℝ} {x : ℝ} (hx : 1 ≤ x)
    (hd : ∀ t ∈ Set.Icc 1 x, HasDerivAt f (g t) t)
    (hc : ContinuousOn g (Set.Icc 1 x)) :
    arithmeticSummatory (fun n => f n * a n) x =
      f x * arithmeticSummatory a x - ∫ t in (1 : ℝ)..x, g t * arithmeticSummatory a t := by
  have hi : IntegrableOn (deriv f) (Set.Icc 1 x) :=
    hc.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have H := sum_mul_eq_sub_integral_mul₀ a ha x (fun t ht => (hd t ht).differentiableAt) hi
  rw [← arithmeticSummatory_eq_sum_Icc_zero (by simp [ha]),
    ← arithmeticSummatory_eq_sum_Icc_zero ha] at H
  simp_rw [← arithmeticSummatory_eq_sum_Icc_zero ha] at H
  rw [setIntegral_congr_fun measurableSet_Ioc
    (g := fun t => g t * arithmeticSummatory a t)
    (fun t ht => by rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv]),
    ← intervalIntegral.integral_of_le hx] at H
  exact H

end NairTenenbaum
