/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Positivity

/-! # A quantitative gap in the Hooley moment exponent

The gap is positive even at `t=1`. The explicit lower bound is quadratic
in the moment order, as needed for optimizing the final bound.
-/

@[expose] public section

namespace NairTenenbaum

open Real

/-- The exponent gap between the recursive Hooley moment estimates. -/
noncomputable def hooleyMomentExponentGap (t : ℝ) (q : ℕ) : ℝ :=
  ((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) - t / q

theorem two_rpow_le_one_add_six_sevenths {u : ℝ} (hu : 0 ≤ u) (hu₂ : u ≤ 1 / 2) :
    (2 : ℝ) ^ u ≤ 1 + (6 / 7 : ℝ) * u := by
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hs₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsbound : Real.sqrt 2 ≤ 10 / 7 := by nlinarith
  have H := rpow_one_add_le_one_add_mul_self
    (s := Real.sqrt 2 - 1) (by linarith) (p := 2 * u) (by linarith) (by linarith)
  have heq : (Real.sqrt 2) ^ (2 * u) = (2 : ℝ) ^ u := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [show 1 + (Real.sqrt 2 - 1) = Real.sqrt 2 by ring, heq] at H
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hsbound)]

theorem hooleyMomentExponentGap_lower {t : ℝ} (ht : 1 ≤ t) {q : ℕ}
    (hq : 2 < q) (hqt : 2 * t ≤ q) :
    t / (7 * (q : ℝ) * ((q : ℝ) - 1)) ≤ hooleyMomentExponentGap t q := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hq₀ : (0 : ℝ) < q := by linarith
  have hq₁ : 0 < (q : ℝ) - 1 := by linarith
  have H := two_rpow_le_one_add_six_sevenths
    (div_nonneg (by linarith : 0 ≤ t) hq₀.le)
    ((div_le_iff₀ hq₀).mpr (by linarith : t ≤ 1 / 2 * (q : ℝ)))
  have H' : 1 + t ≤ (2 : ℝ) ^ t := by
    simpa only [one_add_one_eq_two, mul_one] using one_add_mul_self_le_rpow_one_add (s := (1 : ℝ))
        (by
      norm_num) ht
  have hmul : hooleyMomentExponentGap t q * ((q : ℝ) - 1) =
      (2 : ℝ) ^ t - (2 : ℝ) ^ (t / q) - (t / q) * ((q : ℝ) - 1) := by
    unfold hooleyMomentExponentGap
    rw [sub_mul, div_mul_cancel₀ _ hq₁.ne']
  have htq : t / (q : ℝ) * q = t := div_mul_cancel₀ _ hq₀.ne'
  apply (le_of_mul_le_mul_right ?_ hq₁)
  have hcancel : t / (7 * (q : ℝ) * ((q : ℝ) - 1)) * ((q : ℝ) - 1) = (t / q) / 7 := by
    field_simp
  rw [hcancel, hmul]
  nlinarith

theorem hooleyMomentExponentGap_pos {t : ℝ} (ht : 1 ≤ t) {q : ℕ}
    (hq : 2 < q) (hqt : 2 * t ≤ q) : 0 < hooleyMomentExponentGap t q := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have ht₀ : 0 < t := by linarith
  have hq₀ : 0 < (q : ℝ) := by linarith
  have hq₁ : 0 < (q : ℝ) - 1 := by linarith
  exact lt_of_lt_of_le (by positivity : 0 < t / (7 * (q : ℝ) * ((q : ℝ) - 1)))
    (hooleyMomentExponentGap_lower ht hq hqt)

end NairTenenbaum
