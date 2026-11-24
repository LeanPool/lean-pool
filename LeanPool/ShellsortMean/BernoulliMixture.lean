/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.IntegerBeta
public import LeanPool.ShellsortMean.BernoulliCounts

/-!
Integrating independent Bernoulli bits gives the factorial weights of tagged
subsets. The product law is on the original finite position set. No conditional
event is divided by its probability, including at parameters zero and one.
-/
@[expose] public section

namespace Shellsort
open scoped BigOperators
open MeasureTheory

/-- The number of true bits in a family indexed by a finite type. -/
def finiteBitCount {ι : Type*} [Fintype ι] (x : ι → Bool) : ℕ :=
  ∑ i, if x i then 1 else 0

/-- The mass of a specified bit family after averaging its Bernoulli parameter uniformly. -/
noncomputable def factorialSubsetWeight {ι : Type*} [Fintype ι] (x : ι → Bool) : ℝ :=
  ((finiteBitCount x).factorial : ℝ) * (Fintype.card ι - finiteBitCount x).factorial /
    (Fintype.card ι + 1).factorial

theorem finiteBitCount_le_card {ι : Type*} [Fintype ι] (x : ι → Bool) :
    finiteBitCount x ≤ Fintype.card ι := by
  calc
    finiteBitCount x ≤ ∑ _i : ι, 1 := by
      exact Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    _ = Fintype.card ι := by simp

theorem bernoulli_product_weight_eq {ι : Type*} [Fintype ι] (t : ℝ) (x : ι → Bool) :
    productWeight (fun _i : ι => bernoulliWeight t) x =
      t ^ (finiteBitCount x) * (1 - t) ^ (Fintype.card ι - finiteBitCount x) := by
  have hcount : finiteBitCount x = (Finset.univ.filter (fun i => x i = true)).card := by
    simp [finiteBitCount]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => x i = true)
  have hnot : (Finset.univ.filter (fun i => ¬x i = true)).card =
      Fintype.card ι - finiteBitCount x := by
    rw [← hcount, Finset.card_univ] at hc
    omega
  simp only [productWeight, bernoulliWeight, Finset.prod_ite, Finset.prod_const]
  rw [← hcount, hnot]

/-- Exact integrated weight of each concrete finite bit assignment. -/
theorem bernoulli_product_integral {ι : Type*} [Fintype ι] (x : ι → Bool) :
    (∫ t : ℝ in 0..1, productWeight (fun _i : ι => bernoulliWeight t) x) =
      factorialSubsetWeight x := by
  simp_rw [bernoulli_product_weight_eq]
  rw [integer_beta_integral]
  have hsum : finiteBitCount x + (Fintype.card ι - finiteBitCount x) + 1 =
      Fintype.card ι + 1 := by have := finiteBitCount_le_card x; omega
  rw [hsum]
  rfl

theorem bernoulli_product_mean_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → Bool) → ℝ) :
    Continuous (fun t : ℝ => mean (productWeight (fun _i : ι => bernoulliWeight t)) F) := by
  unfold mean
  simp_rw [bernoulli_product_weight_eq]
  fun_prop

/-- Integrating any finite observable gives its exact factorial-subset mean. -/
theorem bernoulli_mixture_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → Bool) → ℝ) :
    (∫ t : ℝ in 0..1, mean (productWeight (fun _i : ι => bernoulliWeight t)) F) =
      mean factorialSubsetWeight F := by
  unfold mean
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [intervalIntegral.integral_mul_const, bernoulli_product_integral]
  · intro x _
    simp_rw [bernoulli_product_weight_eq]
    exact (integer_beta_intervalIntegrable (finiteBitCount x)
      (Fintype.card ι - finiteBitCount x)).mul_const (F x)

theorem factorialSubsetWeight_nonneg {ι : Type*} [Fintype ι] (x : ι → Bool) :
    0 ≤ factorialSubsetWeight x := by
  unfold factorialSubsetWeight
  positivity

theorem factorialSubsetWeight_sum {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∑ x : ι → Bool, factorialSubsetWeight x = 1 := by
  have hm := bernoulli_mixture_mean (fun _x : ι → Bool => (1 : ℝ))
  have hnorm : ∀ t : ℝ, mean (productWeight (fun _i : ι => bernoulliWeight t))
      (fun _ => 1) = 1 := by
    intro t
    exact mean_const _ (productWeight_sum _ (fun _ => bernoulliWeight_sum t)) 1
  simp_rw [hnorm] at hm
  simp only [intervalIntegral.integral_const, sub_zero, one_smul, mean, mul_one] at hm
  exact hm.symm

/-- A uniform-in-t bound transfers to the exact factorial-subset law. -/
theorem bernoulli_mixture_mean_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → Bool) → ℝ) (K : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      mean (productWeight (fun _i : ι => bernoulliWeight t)) F ≤ K) :
    mean factorialSubsetWeight F ≤ K := by
  rw [← bernoulli_mixture_mean]
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1)
    zero_le_one ((bernoulli_product_mean_continuous F).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1 : IntervalIntegrable (fun _ : ℝ => K) volume 0 1)
    (fun t ht => hbound t ht.1 ht.2)
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hi

end Shellsort
