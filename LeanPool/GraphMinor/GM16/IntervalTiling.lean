/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.Lattice.Nat

/-!
# Tiling a horizontal interval by width-two intervals

The bricks in one row cover that row's closed rectangle. The
one-dimensional calculation joins consecutive width-two intervals,
then takes their product with the common vertical interval. This
is used to cover the enclosed wall disc by its closed bricks in
XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set

/-- Consecutive nonnegative-width intervals cover their full interval. -/
theorem interval_eq_union_step (a d : ℝ) (hd : 0 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    Icc a (a+d*(n : ℝ)) = ⋃ k < n, Icc (a+d*(k : ℝ)) (a+d*(k : ℝ)+d) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp
    have hn1 : 1 ≤ n := by omega
    rw [biUnion_lt_succ,← ih hn1]
    have hNonneg : 0 ≤ d*(n : ℝ) := mul_nonneg hd (Nat.cast_nonneg _)
    have hEq : a+d*((n+1 : ℕ) : ℝ) = a+d*(n : ℝ)+d := by
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    rw [hEq]
    exact (Icc_union_Icc_eq_Icc (by linarith) (by linarith)).symm

/-- Consecutive closed intervals of width two cover their full interval. -/
theorem interval_eq_union_width_two (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Icc a (a+2*(n : ℝ)) = ⋃ k < n, Icc (a+2*(k : ℝ)) (a+2*(k : ℝ)+2) :=
  interval_eq_union_step a 2 (by norm_num) hn

/-- The unit intervals from zero to a positive integer cover that interval. -/
theorem interval_eq_union_unit {n : ℕ} (hn : 1 ≤ n) :
    Icc (0 : ℝ) (n : ℝ) = ⋃ k < n, Icc (k : ℝ) ((k : ℝ)+1) := by
  simpa only [zero_add,one_mul] using interval_eq_union_step 0 1 (by norm_num) hn

/-- Taking a common vertical interval gives the closed rectangles in a row. -/
theorem rectangle_eq_union_width_two (a c d : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Icc a (a+2*(n : ℝ)) ×ˢ Icc c d =
      ⋃ k < n, Icc (a+2*(k : ℝ)) (a+2*(k : ℝ)+2) ×ˢ Icc c d := by
  rw [interval_eq_union_width_two a hn]
  ext p
  constructor
  · rintro ⟨hx,hy⟩
    obtain ⟨k,hk,hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨k,hk,hx,hy⟩
  · intro hp
    obtain ⟨k,hk,hx,hy⟩ := mem_iUnion₂.mp hp
    exact ⟨mem_iUnion₂.mpr ⟨k,hk,hx⟩,hy⟩

end GraphMinor.GM16
