/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Finite probability weights. No independence or Shellsort distribution is
assumed implicitly. The bridge to that distribution remains separate. -/
@[expose] public section

namespace Shellsort
open scoped BigOperators

/-- The weighted mean used for finite product laws. -/
def mean {ι : Type*} [Fintype ι] (w f : ι → ℝ) : ℝ := ∑ i, w i * f i
/-- The weighted second moment about zero. -/
def secondMoment {ι : Type*} [Fintype ι] (w f : ι → ℝ) : ℝ :=
  ∑ i, w i * (f i) ^ 2
/-- The weighted second moment about the weighted mean. -/
def centeredSecond {ι : Type*} [Fintype ι] (w f : ι → ℝ) : ℝ :=
  ∑ i, w i * (f i - mean w f) ^ 2

theorem centeredSecond_identity {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∑ i, w i = 1) :
    centeredSecond w f = secondMoment w f - (mean w f) ^ 2 := by
  unfold centeredSecond secondMoment
  calc
    (∑ i, w i * (f i - mean w f) ^ 2) =
        ∑ i, (w i * (f i) ^ 2 - 2 * mean w f * (w i * f i) +
          (mean w f) ^ 2 * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, w i * (f i) ^ 2) - (mean w f) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hw]
      change (∑ i, w i * f i ^ 2) - 2 * mean w f * mean w f +
        mean w f ^ 2 * 1 = _
      ring

theorem centeredSecond_nonneg {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ centeredSecond w f := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hw i) (sq_nonneg _)

theorem absMean_sq_le_second {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    (mean w (fun i => |f i|)) ^ 2 ≤ secondMoment w f := by
  have h := centeredSecond_nonneg w (fun i => |f i|) hw0
  rw [centeredSecond_identity w (fun i => |f i|) hw1] at h
  simpa only [secondMoment, sq_abs] using (sub_nonneg.mp h)

/-- A finite L1 estimate from a second moment; all weights are explicit. -/
theorem absMean_le_of_second {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (B : ℝ) (hB : 0 ≤ B) (hsecond : secondMoment w f ≤ B ^ 2) :
    mean w (fun i => |f i|) ≤ B := by
  have h := absMean_sq_le_second w f hw0 hw1
  nlinarith [sq_nonneg (mean w (fun i => |f i|) - B)]

/-- This is the last finite probability step of the upper proof, conditional
on the mean/variance estimates. Those estimates are not postulated as axioms. -/
theorem twoPass_moment_interface {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (h g : ℝ) (hh : 1 ≤ h) (hg : 1 ≤ g)
    (hmean : |mean w f| ≤ g - 1)
    (hvar : centeredSecond w f ≤ (h - 1) * (g - 1) ^ 2 / 4) :
    mean w (fun i => |f i|) ≤ (g - 1) * Real.sqrt (h + 3) / 2 := by
  have hgm : 0 ≤ g - 1 := by linarith
  have hsqrt : (Real.sqrt (h + 3)) ^ 2 = h + 3 := Real.sq_sqrt (by linarith)
  have hm : (mean w f) ^ 2 ≤ (g - 1) ^ 2 := by
    have hm' := abs_le.mp hmean
    nlinarith [sq_nonneg (g - 1 - mean w f), sq_nonneg (g - 1 + mean w f)]
  have hid := centeredSecond_identity w f hw1
  apply absMean_le_of_second w f hw0 hw1
  · positivity
  · nlinarith

end Shellsort
