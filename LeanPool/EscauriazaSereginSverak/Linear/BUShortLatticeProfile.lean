/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A summable integer lattice profile

A fixed reciprocal-square profile dominates half-integer Gaussians with
an explicit inverse-width factor.
-/

public section


noncomputable section

namespace ESS

/-- Reciprocal-square lattice profile, normalized at the origin. -/
@[expose] def buShortIntProfile (n : ℤ) : ℝ :=
  if n = 0 then 1 else 1 / (n : ℝ) ^ 2

/-- The reciprocal-square lattice profile is summable. -/
theorem bu_short_int_profile_summable : Summable buShortIntProfile := by
  have hbase : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hsingle : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) := by
    exact summable_of_hasFiniteSupport (by
      exact Set.Finite.subset (Set.finite_singleton 0) (by
        intro n hn
        by_cases h : n = 0
        · simp [h]
        · simp [h] at hn))
  have hsum := hbase.add hsingle
  apply hsum.congr
  intro n
  by_cases hn : n = 0
  · simp [buShortIntProfile, hn]
  · simp [buShortIntProfile, hn]

/-- The reciprocal-square lattice profile is nonnegative. -/
theorem bu_short_int_profile_nonneg (n : ℤ) : 0 ≤ buShortIntProfile n := by
  by_cases hn : n = 0
  · simp [buShortIntProfile, hn]
  · simp [buShortIntProfile, hn]
    positivity

/-- A half-integer Gaussian is bounded by a fixed summable profile
with one inverse power of its width (`lem:bu-small-time`). -/
theorem bu_short_half_gaussian_le_profile
    (a : ℝ) (ha : 0 < a) (n : ℤ) :
    Real.exp (-(a * ((n : ℝ) + 1 / 2) ^ 2)) ≤
      Real.exp (a / 4) * (1 + 2 / a) * buShortIntProfile n := by
  have hsquare : (n : ℝ) ^ 2 / 2 - 1 / 4 ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
    nlinarith only [sq_nonneg ((n : ℝ) + 1)]
  have hexp : Real.exp (-(a * ((n : ℝ) + 1 / 2) ^ 2)) ≤
      Real.exp (a / 4) * Real.exp (-(a * (n : ℝ) ^ 2 / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hsquare ha.le
    nlinarith only [hmul]
  by_cases hn : n = 0
  · subst n
    have hexp0 : Real.exp (-(a * (((0 : ℤ) : ℝ) + 1 / 2) ^ 2)) ≤
        Real.exp (a / 4) := by
      simpa using hexp
    have hfrac : 0 ≤ 2 / a := by positivity
    rw [show buShortIntProfile (0 : ℤ) = 1 by simp [buShortIntProfile]]
    nlinarith only [hexp0, Real.exp_pos (a / 4), hfrac]
  · have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hx : 0 < a * (n : ℝ) ^ 2 / 2 := by positivity
    have hExpLarge : a * (n : ℝ) ^ 2 / 2 ≤
        Real.exp (a * (n : ℝ) ^ 2 / 2) := by
      have h := Real.add_one_le_exp (a * (n : ℝ) ^ 2 / 2)
      linarith only [h]
    have hInv : Real.exp (-(a * (n : ℝ) ^ 2 / 2)) ≤
        2 / (a * (n : ℝ) ^ 2) := by
      rw [Real.exp_neg]
      have h := one_div_le_one_div_of_le hx hExpLarge
      convert h using 1 <;> ring
    have hfactor : 2 / (a * (n : ℝ) ^ 2) ≤
        (1 + 2 / a) * buShortIntProfile n := by
      simp only [buShortIntProfile, hn, ↓reduceIte]
      have hdiv : 2 / (a * (n : ℝ) ^ 2) =
          (2 / a) * (1 / (n : ℝ) ^ 2) := by ring
      rw [hdiv]
      have hP : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (by linarith only []) hP
    calc
      _ ≤ Real.exp (a / 4) * Real.exp (-(a * (n : ℝ) ^ 2 / 2)) := hexp
      _ ≤ Real.exp (a / 4) * (2 / (a * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hInv (Real.exp_nonneg _)
      _ ≤ Real.exp (a / 4) * ((1 + 2 / a) * buShortIntProfile n) :=
        mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg _)
      _ = _ := by ring

end ESS
