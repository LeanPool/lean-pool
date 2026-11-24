/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.FiniteMoments
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Explicit finite product laws. Independence below is proved from the weights,
not supplied as a probabilistic hypothesis about a later sorting state. -/
@[expose] public section

namespace Shellsort
open scoped BigOperators

def productWeight {ι : Type*} [Fintype ι] {β : ι → Type*}
    (w : ∀ i, β i → ℝ) (x : ∀ i, β i) : ℝ := ∏ i, w i (x i)

theorem productWeight_nonneg {ι : Type*} [Fintype ι] {β : ι → Type*}
    (w : ∀ i, β i → ℝ) (hw : ∀ i x, 0 ≤ w i x) (x : ∀ i, β i) :
    0 ≤ productWeight w x := by
  exact Finset.prod_nonneg (fun i _ => hw i (x i))

theorem productWeight_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (hw : ∀ i, ∑ y, w i y = 1) :
    ∑ x, productWeight w x = 1 := by
  simp only [productWeight, ← Fintype.prod_sum, hw, Finset.prod_const_one]

theorem productWeight_mean_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w f : ∀ i, β i → ℝ) :
    mean (productWeight w) (fun x => ∏ i, f i (x i)) = ∏ i, mean (w i) (f i) := by
  simp only [mean, productWeight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i y => w i y * f i y)).symm

theorem mean_const {α : Type*} [Fintype α] (w : α → ℝ)
    (hw : ∑ x, w x = 1) (c : ℝ) : mean w (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, hw]

theorem mean_add {α : Type*} [Fintype α] (w f g : α → ℝ) :
    mean w (fun x => f x + g x) = mean w f + mean w g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub {α : Type*} [Fintype α] (w f g : α → ℝ) :
    mean w (fun x => f x - g x) = mean w f - mean w g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (w : α → ℝ) (f : ι → α → ℝ) :
    mean w (fun x => ∑ i, f i x) = ∑ i, mean w (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem productWeight_mean_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w f : ∀ i, β i → ℝ) (hw : ∀ i, ∑ y, w i y = 1) (i : ι) :
    mean (productWeight w) (fun x => f i (x i)) = mean (w i) (f i) := by
  have h := productWeight_mean_product w (fun j y => if j = i then f j y else 1)
  have hm : ∀ j, mean (w j) (fun y => if j = i then f j y else 1) =
      if j = i then mean (w j) (f j) else 1 := by
    intro j
    by_cases hji : j = i
    · simp only [hji, ite_true]
    · simp only [ite_eq_right hji, mean_const (w j) (hw j) 1]
  simpa only [Fintype.prod_ite_eq', hm] using h

theorem productWeight_mean_coordinate_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w f g : ∀ i, β i → ℝ) (hw : ∀ i, ∑ y, w i y = 1)
    (i j : ι) (hij : i ≠ j) :
    mean (productWeight w) (fun x => f i (x i) * g j (x j)) =
      mean (w i) (f i) * mean (w j) (g j) := by
  let u := fun l y => (if l = i then f l y else 1) * (if l = j then g l y else 1)
  have h := productWeight_mean_product w u
  have hu : ∀ l, mean (w l) (u l) =
      (if l = i then mean (w l) (f l) else 1) *
      (if l = j then mean (w l) (g l) else 1) := by
    intro l
    by_cases hli : l = i
    · subst l
      simp [u, hij]
    · by_cases hlj : l = j
      · subst l
        simp [u, hli]
      · simp [u, hli, hlj, mean_const (w l) (hw l) 1]
  simpa only [u, Finset.prod_mul_distrib, Fintype.prod_ite_eq', hu] using h

end Shellsort
