/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import LeanPool.ShellsortMean.Residual
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Exact prefix counts and centered residuals for a fixed residue class. -/

@[expose] public section

namespace Shellsort
open scoped BigOperators

/-- Actual count of positions in the finite prefix with the given residue. -/
def residuePrefixCount (g a y : ℕ) : ℕ :=
  ∑ v ∈ Finset.range y, if v % g = a then 1 else 0

theorem residuePrefixCount_succ (g a y : ℕ) :
    residuePrefixCount g a (y + 1) = residuePrefixCount g a y +
      if y % g = a then 1 else 0 := by
  exact Finset.sum_range_succ _ _

theorem residuePrefixCount_formula (g a y : ℕ) (hg : 0 < g) (ha : a < g) :
    residuePrefixCount g a y = y / g + if a < y % g then 1 else 0 := by
  by_cases hg1 : g = 1
  · subst g
    have ha0 : a = 0 := by omega
    subst a
    simp [residuePrefixCount, Nat.mod_one]
  have hg2 : 1 < g := by omega
  induction y with
  | zero => simp [residuePrefixCount]
  | succ y ih =>
    have hv : y % g < g := Nat.mod_lt y hg
    by_cases he : y % g + 1 = g
    · have hm : (y + 1) % g = 0 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hg2, he, Nat.mod_self]
      have hd := Nat.succ_div_of_mod_eq_zero hm
      rw [residuePrefixCount_succ, ih, hd, hm]
      split_ifs <;> omega
    · have hv' : y % g + 1 < g := by omega
      have hm : (y + 1) % g = y % g + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hg2, Nat.mod_eq_of_lt hv']
      have hd := Nat.succ_div_of_mod_ne_zero (by omega : (y + 1) % g ≠ 0)
      rw [residuePrefixCount_succ, ih, hd, hm]
      split_ifs <;> omega

/-- This identifies the signed residual with a genuine finite-position count. -/
theorem counted_residual_eq_phase (g a y : ℕ) (hg : 0 < g) (ha : a < g) :
    (g : ℤ) * residuePrefixCount g a y - y = phaseResidual g a y := by
  rw [residuePrefixCount_formula g a y hg ha]
  have hdiv : (y % g : ℤ) + (g : ℤ) * (y / g : ℕ) = (y : ℤ) := by
    exact_mod_cast Nat.mod_add_div y g
  unfold phaseResidual
  split_ifs <;> push_cast at hdiv ⊢ <;> nlinarith

theorem counted_residual_bounds (g a y : ℕ) (hg : 0 < g) (ha : a < g) :
    -(a : ℤ) ≤ (g : ℤ) * residuePrefixCount g a y - y ∧
    (g : ℤ) * residuePrefixCount g a y - y ≤ (g : ℤ) - 1 - a := by
  rw [counted_residual_eq_phase g a y hg ha]
  exact phaseResidual_bounds g a y hg ha

end Shellsort
