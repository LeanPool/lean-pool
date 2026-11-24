/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ProductWeights

/-! Mean and variance bounds for sums on finite product distributions. -/

@[expose] public section

namespace Shellsort
open scoped BigOperators

/-- Popoviciu's variance bound for an explicit finite probability law. -/
theorem centeredSecond_le_range {α : Type*} [Fintype α]
    (w f : α → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (a b : ℝ) (hf : ∀ x, a ≤ f x ∧ f x ≤ b) :
    centeredSecond w f ≤ (b - a) ^ 2 / 4 := by
  have hp : 0 ≤ ∑ x, w x * (f x - a) * (b - f x) := by
    exact Finset.sum_nonneg (fun x _ =>
      mul_nonneg (mul_nonneg (hw0 x) (sub_nonneg.mpr (hf x).1))
        (sub_nonneg.mpr (hf x).2))
  have hid : (∑ x, w x * (f x - a) * (b - f x)) =
      (a + b) * mean w f - secondMoment w f - a * b := by
    calc
      _ = ∑ x, ((a + b) * (w x * f x) - w x * (f x) ^ 2 - a * b * w x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, mul_one,
          mean, secondMoment]
  rw [hid] at hp
  rw [centeredSecond_identity w f hw1]
  nlinarith [sq_nonneg (mean w f - (a + b) / 2)]

theorem productWeight_mean_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w f : ∀ i, β i → ℝ) (hw : ∀ i, ∑ y, w i y = 1) :
    mean (productWeight w) (fun x => ∑ i, f i (x i)) =
      ∑ i, mean (w i) (f i) := by
  rw [mean_sum]
  exact Finset.sum_congr rfl (fun i _ => productWeight_mean_coordinate w f hw i)

/-- The variance of a sum under a genuine product law, including unequal
coordinate types and an empty family. No independence assumption is hidden. -/
theorem productWeight_variance_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w f : ∀ i, β i → ℝ) (hw : ∀ i, ∑ y, w i y = 1) :
    centeredSecond (productWeight w) (fun x => ∑ i, f i (x i)) =
      ∑ i, centeredSecond (w i) (f i) := by
  let c := fun i y => f i y - mean (w i) (f i)
  have hc : ∀ i, mean (w i) (c i) = 0 := by
    intro i
    simp only [c, mean_sub, mean_const (w i) (hw i), sub_self]
  have hcov : ∀ i j, mean (productWeight w) (fun x => c i (x i) * c j (x j)) =
      if i = j then centeredSecond (w i) (f i) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      have h := productWeight_mean_coordinate w (fun i y => (c i y) ^ 2) hw i
      simpa only [pow_two, c, mean, centeredSecond] using h
    · rw [productWeight_mean_coordinate_mul w c c hw i j hij, hc i, hc j]
      simp only [ite_eq_right hij, mul_zero]
  have hm := productWeight_mean_sum w f hw
  change mean (productWeight w)
    (fun x => ((∑ i, f i (x i)) - mean (productWeight w) (fun z => ∑ i, f i (z i))) ^ 2) = _
  rw [hm]
  calc
    _ = mean (productWeight w) (fun x => ∑ i, ∑ j, c i (x i) * c j (x j)) := by
      congr 1
      funext x
      rw [← Finset.sum_mul_sum]
      simp only [c, Finset.sum_sub_distrib, pow_two]
    _ = _ := by
      rw [mean_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mean_sum]
      simp only [hcov, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem centeredSecond_add_const {α : Type*} [Fintype α]
    (w f : α → ℝ) (hw : ∑ x, w x = 1) (c : ℝ) :
    centeredSecond w (fun x => c + f x) = centeredSecond w f := by
  unfold centeredSecond
  rw [mean_add, mean_const w hw]
  congr 1
  funext x
  ring

theorem productWeight_variance_le_ranges {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w f : ∀ i, β i → ℝ)
    (hw0 : ∀ i y, 0 ≤ w i y) (hw1 : ∀ i, ∑ y, w i y = 1)
    (a b : ι → ℝ) (hf : ∀ i y, a i ≤ f i y ∧ f i y ≤ b i) (c : ℝ) :
    centeredSecond (productWeight w) (fun x => c + ∑ i, f i (x i)) ≤
      ∑ i, (b i - a i) ^ 2 / 4 := by
  rw [centeredSecond_add_const _ _ (productWeight_sum w hw1), productWeight_variance_sum w f hw1]
  exact Finset.sum_le_sum (fun i _ => centeredSecond_le_range
    (w i) (f i) (hw0 i) (hw1 i) (a i) (b i) (hf i))

end Shellsort
