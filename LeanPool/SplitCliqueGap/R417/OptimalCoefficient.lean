/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! C3: exact minimisation of the leading loss coefficient, with no numerics. -/

@[expose] public section

namespace GapExtremal.R417

/-- The scale minimizing the competing real error terms for coefficient `c`. -/
noncomputable def optimalScale (c : ℝ) : ℝ := (c ^ 2 / 4) ^ ((1 : ℝ) / 3)

/-- The minimized coefficient of the error term at the optimal scale. -/
noncomputable def criticalCoefficient (c : ℝ) : ℝ :=
  (3 / 2 : ℝ) * (4 : ℝ) ^ ((1 : ℝ) / 3) * c ^ ((1 : ℝ) / 3)

theorem optimalScale_pos {c : ℝ} (hc : 0 < c) : 0 < optimalScale c := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem optimalScale_cube {c : ℝ} (hc : 0 < c) :
    optimalScale c ^ 3 = c ^ 2 / 4 := by
  rw [optimalScale, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem optimized_energy_eq {c : ℝ} (hc : 0 < c) :
    c / optimalScale c + 2 * optimalScale c ^ 2 / c = criticalCoefficient c := by
  let a := optimalScale c
  have ha : 0 < a := optimalScale_pos hc
  have ha3 : a ^ 3 = c ^ 2 / 4 := optimalScale_cube hc
  have heq : c / a + 2 * a ^ 2 / c = 6 * a ^ 2 / c := by
    field_simp [ha.ne', hc.ne']
    nlinarith
  have hcube : (6 * a ^ 2 / c) ^ 3 = (27 / 2 : ℝ) * c := by
    have hh := congrArg (fun x : ℝ => x ^ 2) ha3
    field_simp [hc.ne']
    nlinarith
  have h4 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hc3 : (c ^ ((1 : ℝ) / 3)) ^ 3 = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num
  have hcc : criticalCoefficient c ^ 3 = (27 / 2 : ℝ) * c := by
    dsimp [criticalCoefficient]
    rw [mul_pow, mul_pow, h4, hc3]
    ring
  have hpos : 0 < criticalCoefficient c := by dsimp [criticalCoefficient]; positivity
  rw [show c / optimalScale c + 2 * optimalScale c ^ 2 / c = 6 * a ^ 2 / c from heq]
  exact (pow_left_inj₀ (by positivity) hpos.le (by norm_num : (3 : ℕ) ≠ 0)).mp
    (hcube.trans hcc.symm)

theorem leading_energy_minimum {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    criticalCoefficient c ≤ c / x + 2 * x ^ 2 / c := by
  let a := optimalScale c
  have ha : 0 < a := optimalScale_pos hc
  have ha3 : c ^ 2 = 4 * a ^ 3 := by have hh := optimalScale_cube hc; dsimp [a]; nlinarith
  have hid : c / x + 2 * x ^ 2 / c - (c / a + 2 * a ^ 2 / c) =
      2 * (x - a) ^ 2 * (x + 2 * a) / (c * x) := by
    field_simp [hc.ne', hx.ne', ha.ne']
    have hh := congrArg (fun y : ℝ => y * (a - x)) ha3
    nlinarith
  have hnon : 0 ≤ 2 * (x - a) ^ 2 * (x + 2 * a) / (c * x) := by positivity
  have heq := optimized_energy_eq hc
  change c / a + 2 * a ^ 2 / c = criticalCoefficient c at heq
  linarith

end GapExtremal.R417
