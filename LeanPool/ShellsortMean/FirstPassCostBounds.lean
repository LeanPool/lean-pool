/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.GapInsertionBridge
public import Mathlib.Order.Interval.Finset.Fin

/-!
Finite bounds for the uniform mean of the actually executed first-pass
insertion right shifts. The exact long-chain/short-chain boundary correction
is retained before deriving the simpler bounds. No asymptotic premise is used.
-/
@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

theorem firstPass_long_chain_indicator_sum (h r : ℕ) (hr : r < h) :
    (∑ s : Fin h, if s.val < r then (1 : ℝ) else 0) = (r : ℝ) := by
  have he : (Finset.univ.filter (fun s : Fin h => s.val < r)) =
      Finset.Iio (⟨r, hr⟩ : Fin h) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
      Fin.lt_def]
  have hc : (Finset.univ.filter (fun s : Fin h => s.val < r)).card = r := by
    rw [he, Fin.card_Iio]
  have hcR := congrArg (fun x : ℕ => (x : ℝ)) hc
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hcR

/-- Exact mean in quotient/remainder form, including n=0 and h ≥ n. -/
theorem uniform_firstPassCost_quotient_remainder (n h : ℕ) (hh : 0 < h) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h hh : ℝ)) =
      ((h : ℝ) * (n / h : ℕ) * ((n / h : ℕ) - 1 : ℝ) +
        2 * (n % h : ℕ) * (n / h : ℕ)) / 4 := by
  rw [uniform_gapInsertionCost_chain_lengths]
  calc
    _ = ∑ s : Fin h,
        (((n / h : ℕ) : ℝ) * (((n / h : ℕ) : ℝ) - 1) / 4 +
          (if s.val < n % h then (1 : ℝ) else 0) * ((n / h : ℕ) : ℝ) / 2) := by
      apply Finset.sum_congr rfl
      intro s _
      unfold sourceTrialLength
      split_ifs <;> push_cast <;> ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
        firstPass_long_chain_indicator_sum h (n % h) (Nat.mod_lt n hh),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The exact finite boundary correction is r(h-r), where r=n mod h. -/
theorem uniform_firstPassCost_scaled_identity (n h : ℕ) (hh : 0 < h) :
    4 * (h : ℝ) *
      uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h hh : ℝ)) =
      (n : ℝ) ^ 2 - (h : ℝ) * n +
        ((n % h : ℕ) : ℝ) * ((h : ℝ) - ((n % h : ℕ) : ℝ)) := by
  rw [uniform_firstPassCost_quotient_remainder n h hh]
  have hn := congrArg (fun x : ℕ => (x : ℝ)) (Nat.mod_add_div n h)
  push_cast at hn
  nlinarith [sq_nonneg ((n / h : ℕ) : ℝ)]

/-- Uniform first-pass mean is bounded below by n²/(4h)-n/4. The right-hand
side may be negative for short arrays; the theorem still holds. -/
theorem uniform_firstPassCost_lower (n h : ℕ) (hh : 0 < h) :
    (n : ℝ) ^ 2 / (4 * (h : ℝ)) - (n : ℝ) / 4 ≤
      uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h hh : ℝ)) := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hrR : ((n % h : ℕ) : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast Nat.le_of_lt (Nat.mod_lt n hh)
  have hid := uniform_firstPassCost_scaled_identity n h hh
  have hcor : 0 ≤ ((n % h : ℕ) : ℝ) * ((h : ℝ) - ((n % h : ℕ) : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hrR)
  rw [sub_le_iff_le_add]
  apply (div_le_iff₀ (show 0 < 4 * (h : ℝ) by positivity)).mpr
  nlinarith

/-- Uniform first-pass mean is at most n²/(4h), for every positive gap. -/
theorem uniform_firstPassCost_upper (n h : ℕ) (hh : 0 < h) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h hh : ℝ)) ≤
      (n : ℝ) ^ 2 / (4 * (h : ℝ)) := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hrn : ((n % h : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.mod_le n h
  have hid := uniform_firstPassCost_scaled_identity n h hh
  apply (le_div_iff₀ (show 0 < 4 * (h : ℝ) by positivity)).mpr
  nlinarith [sq_nonneg (((n % h : ℕ) : ℝ)),
    mul_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ h) (sub_nonneg.mpr hrn)]

theorem uniform_firstPassCost_bounds (n h : ℕ) (hh : 0 < h) :
    (n : ℝ) ^ 2 / (4 * (h : ℝ)) - (n : ℝ) / 4 ≤
        uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h hh : ℝ)) ∧
      uniformAverage (fun p : RankPlacement n => (gapInsertionCost p h hh : ℝ)) ≤
        (n : ℝ) ^ 2 / (4 * (h : ℝ)) :=
  ⟨uniform_firstPassCost_lower n h hh, uniform_firstPassCost_upper n h hh⟩

end Shellsort
end
