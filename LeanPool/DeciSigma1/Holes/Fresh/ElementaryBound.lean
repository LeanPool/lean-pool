/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Arithmetic.ElementaryBounds
public import LeanPool.DeciSigma1.Holes.Fresh.Bound
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # A double exponential bound for fresh tuples

The text-count recurrence is quadratic with fixed coefficients. Bounding its logarithm by a
geometric sequence gives an elementary estimate that also covers empty tuples and zero states.

## Main declarations

- `freshTupleBound_le_double_exp2`: the fresh-tuple bound is at most
  `2 ^ (2 ^ ((k + n + 16) ^ 4))`.
-/

@[expose] public section


namespace DeciSigma1.Holes.Fresh

open Arithmetic

private def arithmeticBudget (k n : ℕ) : ℕ :=
  k * (k * n + 1) + n * n + 7 * k * n + k + 12

private theorem edgeLengthBound_le_exp2 (k n : ℕ) :
    edgeLengthBound k n ≤ exp2 (arithmeticBudget k n) := by
  have hm : deletionMargin k n ≤ 3 * k * n + 5 := by
    have h := Nat.mul_le_mul_left k (Nat.sub_le n 1)
    unfold deletionMargin
    nlinarith
  have hp : (k + 1) ^ (k * n + 1) * n ^ n ≤
      exp2 (k * (k * n + 1) + n * n) := by
    rw [exp2_add, exp2_mul, exp2_mul]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (succ_le_exp2 k) _)
      (Nat.pow_le_pow_left (le_exp2 n) _)
  calc
    edgeLengthBound k n ≤ exp2 (k * (k * n + 1) + n * n) +
        exp2 (6 * k * n + 11) := by
      unfold edgeLengthBound
      have := le_exp2 (6 * k * n + 11)
      nlinarith
    _ ≤ exp2 (k * (k * n + 1) + n * n + (6 * k * n + 11) + 1) :=
      exp2_add_le _ _
    _ ≤ _ := exp2_mono (by unfold arithmeticBudget; nlinarith)

private theorem parseFactor_le_exp2 (k n : ℕ) :
    parseFactor k n ≤ exp2 (arithmeticBudget k n) := by
  apply exp2_mono
  have := Nat.mul_le_mul_left k (Nat.sub_le n 1)
  have hkn : k * n ≤ 7 * k * n := by nlinarith
  unfold arithmeticBudget
  omega

private theorem textCountBoundAtDepth_le_exp2 (k n d : ℕ) :
    textCountBoundAtDepth k n d ≤ exp2 ((4 * arithmeticBudget k n + 4) * 3 ^ d) := by
  induction d with
  | zero =>
    simp only [textCountBoundAtDepth, pow_zero, Nat.mul_one]
    exact (succ_le_exp2 k).trans (exp2_mono (by unfold arithmeticBudget; omega))
  | succ d ih =>
    refine (quadratic_step_le_exp2 ih (parseFactor_le_exp2 k n)
      (edgeLengthBound_le_exp2 k n)).trans (exp2_mono ?_)
    have h := Nat.one_le_pow d 3 (by decide)
    rw [pow_succ]
    nlinarith

/-- The fresh-tuple bound has double exponential growth with a quartic inner polynomial.
No positivity assumptions on the tuple size or the number of states are required. -/
theorem freshTupleBound_le_double_exp2 (k n : ℕ) :
    freshTupleBound k n ≤ exp2 (exp2 ((k + n + 16) ^ 4)) := by
  let q := arithmeticBudget k n
  let B := 4 * q + 4
  let d := k * n
  have ht : textCountBound k n ≤ exp2 (B * 3 ^ d) :=
    textCountBoundAtDepth_le_exp2 k n d
  have ha := parseFactor_le_exp2 k n
  have he := edgeLengthBound_le_exp2 k n
  have hp : textCountBound k n * parseFactor k n ≤ exp2 (B * 3 ^ d + q) := by
    rw [exp2_add]; exact Nat.mul_le_mul ht ha
  have hx : expansionBlockCountBound k n ≤ exp2 (B * 3 ^ d + 2 * q + 2) := by
    calc
      _ ≤ exp2 (B * 3 ^ d + q + 2) * exp2 q :=
        Nat.mul_le_mul ((Nat.add_le_add hp (le_refl 2)).trans
          (exp2_add_le (B * 3 ^ d + q) 1)) he
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have hB : B ≤ B * 3 ^ d := Nat.le_mul_of_pos_right _ (by positivity)
  have hx' : expansionBlockCountBound k n ≤ exp2 (2 * B * 3 ^ d) :=
    hx.trans (exp2_mono (by dsimp [B] at *; nlinarith))
  have hthree : 3 ^ d ≤ exp2 (2 * d) := by
    rw [exp2_mul]
    exact Nat.pow_le_pow_left (by decide : 3 ≤ exp2 2) d
  have hlog : 2 * B * 3 ^ d * (d + 1) ≤ exp2 (B + 3 * d + 1) := by
    calc
      _ ≤ 2 * exp2 B * exp2 (2 * d) * exp2 d :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (le_exp2 B)) hthree)
          (succ_le_exp2 d)
      _ = _ := by
        change exp2 1 * exp2 B * exp2 (2 * d) * exp2 d = _
        rw [← exp2_add, ← exp2_add, ← exp2_add]
        congr 1; omega
  have hpoly : k + B + 3 * d + 2 ≤ (k + n + 16) ^ 4 := by
    dsimp [B, q, d, arithmeticBudget]
    ring_nf
    omega
  calc
    freshTupleBound k n ≤ exp2 k * exp2 (2 * B * 3 ^ d) ^ (d + 1) :=
      Nat.mul_le_mul (le_exp2 k) (Nat.pow_le_pow_left hx' _)
    _ = exp2 (k + 2 * B * 3 ^ d * (d + 1)) := by rw [← exp2_mul, ← exp2_add]
    _ ≤ exp2 (exp2 k + exp2 (B + 3 * d + 1)) :=
      exp2_mono (Nat.add_le_add (le_exp2 k) hlog)
    _ ≤ exp2 (exp2 (k + (B + 3 * d + 1) + 1)) := exp2_mono (exp2_add_le _ _)
    _ ≤ exp2 (exp2 ((k + n + 16) ^ 4)) :=
      exp2_mono (exp2_mono (by omega))

end DeciSigma1.Holes.Fresh
