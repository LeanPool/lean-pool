/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.FirstPassGeometry
public import LeanPool.ShellsortMean.BernoulliCounts
public import LeanPool.ShellsortMean.ProductVariance
public import LeanPool.ShellsortMean.PrefixMean

/-! Mean and variance of first-pass displacement under Bernoulli threshold bits. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

theorem bernoulli_scaled_mean (t c : ℝ) :
    mean (bernoulliWeight t) (fun b : Bool => if b then c else 0) = t * c := by
  simp [mean, bernoulliWeight]

theorem bernoulli_scaled_variance (t c : ℝ) :
    centeredSecond (bernoulliWeight t) (fun b : Bool => if b then c else 0) =
      t * (1 - t) * c ^ 2 := by
  unfold centeredSecond
  rw [bernoulli_scaled_mean]
  simp only [Fintype.sum_bool, bernoulliWeight, Bool.false_eq_true, ite_false, ite_true]
  ring

/-- First-pass tag displacement represented as a weighted sum of bits. -/
def firstPassBitDisplacement {n : ℕ} (h : ℕ) (i : Fin n) (z : Fin n → Bool) : ℝ :=
  ((i.val % h : ℕ) : ℝ) + ∑ a : Fin n, if z a then firstPassCoefficient h i a else 0

theorem firstPassBitDisplacement_mean {n : ℕ} (h : ℕ) (i : Fin n) (t : ℝ) :
    mean (bernoulliVectorWeight t n) (firstPassBitDisplacement h i) =
      ((i.val % h : ℕ) : ℝ) + t * ∑ a : Fin n, firstPassCoefficient h i a := by
  unfold firstPassBitDisplacement
  rw [mean_add, mean_const _ (bernoulliVectorWeight_sum t n)]
  unfold bernoulliVectorWeight
  rw [productWeight_mean_sum (fun _ : Fin n => bernoulliWeight t)
    (fun a (b : Bool) => if b then firstPassCoefficient h i a else 0)
    (fun _ => bernoulliWeight_sum t)]
  simp_rw [bernoulli_scaled_mean]
  rw [Finset.mul_sum]

theorem firstPassBitDisplacement_variance {n : ℕ} (h : ℕ) (i : Fin n) (t : ℝ) :
    centeredSecond (bernoulliVectorWeight t n) (firstPassBitDisplacement h i) =
      t * (1 - t) * ∑ a : Fin n, (firstPassCoefficient h i a) ^ 2 := by
  unfold firstPassBitDisplacement
  rw [centeredSecond_add_const _ _ (bernoulliVectorWeight_sum t n)]
  unfold bernoulliVectorWeight
  rw [productWeight_variance_sum (fun _ : Fin n => bernoulliWeight t)
    (fun a (b : Bool) => if b then firstPassCoefficient h i a else 0)
    (fun _ => bernoulliWeight_sum t)]
  simp_rw [bernoulli_scaled_variance]
  rw [Finset.mul_sum]

theorem firstPassBitDisplacement_mean_bound {n : ℕ} (h : ℕ) (hh : 0 < h)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    |mean (bernoulliVectorWeight t n) (firstPassBitDisplacement h i)| ≤ (h : ℝ) - 1 := by
  rw [firstPassBitDisplacement_mean]
  have hrNat : i.val % h + 1 ≤ h := Nat.mod_lt i.val hh
  have hr : ((i.val % h : ℕ) : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast hrNat
  have hr0 : (0 : ℝ) ≤ ((i.val % h : ℕ) : ℝ) := by positivity
  have hb := prefix_convex_bounds t ((i.val % h : ℕ) : ℝ)
    (((i.val % h : ℕ) : ℝ) + ∑ a : Fin n, firstPassCoefficient h i a)
    (-((h : ℝ) - 1)) ((h : ℝ) - 1) ht.1 ht.2
    (by constructor <;> linarith)
    (firstPassCoefficient_endpoint_bounds h hh i)
  apply abs_le.mpr
  constructor <;> nlinarith [hb.1, hb.2]

theorem firstPassBitDisplacement_variance_bound {n : ℕ} (h : ℕ) (hh : 0 < h)
    (i : Fin n) (t : ℝ) :
    centeredSecond (bernoulliVectorWeight t n) (firstPassBitDisplacement h i) ≤
      (n : ℝ) * h / 4 := by
  rw [firstPassBitDisplacement_variance]
  have hc0 : 0 ≤ ∑ a : Fin n, (firstPassCoefficient h i a) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ht : t * (1 - t) ≤ (1 : ℝ) / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have hm := mul_le_mul_of_nonneg_right ht hc0
  have hc := firstPassCoefficient_sq_sum_bound h hh i
  nlinarith

/-- The finite product-law estimate has its mean and variance proved from
actual position coefficients, rather than supplied as external hypotheses. -/
theorem firstPassBitDisplacement_absMean_bound {n : ℕ} (h : ℕ) (hh : 0 < h)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    mean (bernoulliVectorWeight t n) (fun z => |firstPassBitDisplacement h i z|) ≤
      (h : ℝ) - 1 + Real.sqrt ((n : ℝ) * h) / 2 := by
  have hw0 := bernoulliVectorWeight_nonneg t ht n
  have hw1 := bernoulliVectorWeight_sum t n
  have hm := firstPassBitDisplacement_mean_bound h hh i t ht
  have hv := firstPassBitDisplacement_variance_bound h hh i t
  have hhh : 1 ≤ (h : ℝ) := by exact_mod_cast hh
  have hm2 : (mean (bernoulliVectorWeight t n) (firstPassBitDisplacement h i)) ^ 2 ≤
      ((h : ℝ) - 1) ^ 2 := by
    have hs := abs_le.mp hm
    nlinarith [sq_nonneg ((h : ℝ) - 1 - mean (bernoulliVectorWeight t n)
      (firstPassBitDisplacement h i)),
      sq_nonneg ((h : ℝ) - 1 + mean (bernoulliVectorWeight t n) (firstPassBitDisplacement h i))]
  have hid := centeredSecond_identity (bernoulliVectorWeight t n)
    (firstPassBitDisplacement h i) hw1
  have hsqrt := Real.sq_sqrt (show 0 ≤ (n : ℝ) * h by positivity)
  have hcross := mul_nonneg (show 0 ≤ (h : ℝ) - 1 by linarith)
    (Real.sqrt_nonneg ((n : ℝ) * h))
  apply absMean_le_of_second _ _ hw0 hw1
  · positivity
  · nlinarith

end Shellsort
end
