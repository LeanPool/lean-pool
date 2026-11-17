/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import Mathlib.Order.Interval.Finset.Nat

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

/-!
Stage 145 — promoted after complete Round 28 verification (including concrete witness).
Source direction: Doerr--Doerr (2013), collecting coupons with random
initial stake. A dimension-explicit, finite Cauchy tail modulus for the
half-geometric harmonic correction. This result is useful toward Stage 139
and does not use the unverified Stage 138 finite transform.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open scoped BigOperators

namespace ECRuntime

/-- Exact finite tail of the geometric half series between two levels. -/
private theorem stage145_geometric_tail_exact (n d : Nat) :
    (Finset.Icc (n + 1) (n + d)).sum (fun j =>
      (1 : Real) / (2 : Real) ^ j) =
      (1 : Real) / (2 : Real) ^ n -
        (1 : Real) / (2 : Real) ^ (n + d) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hout : n + d + 1 ∉ Finset.Icc (n + 1) (n + d) := by simp
      have hIcc : Finset.Icc (n + 1) (n + (d + 1)) =
          insert (n + d + 1) (Finset.Icc (n + 1) (n + d)) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert hout, ih]
      have hpow : (2 : Real) ^ (n + d) ≠ 0 := by positivity
      have hpow0 : (2 : Real) ^ n ≠ 0 := by positivity
      rw [show n + (d + 1) = n + d + 1 by omega, pow_succ]
      field_simp [hpow, hpow0]
      ring

/-- The harmonic half-geometric correction has a uniform finite tail
bound, decaying geometrically with the starting index. No limits or
infinite series are assumed. -/
theorem proposed_rlsUniformInitial_harmonicCorrection_tailBound
    (n m : Nat) (h : n ≤ m) :
    0 ≤ (Finset.Icc (n + 1) m).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ∧
    (Finset.Icc (n + 1) m).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤
      (1 : Real) / (2 : Real) ^ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    positivity
  · calc
      (Finset.Icc (n + 1) (n + d)).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤
        (Finset.Icc (n + 1) (n + d)).sum (fun j =>
          (1 : Real) / (2 : Real) ^ j) := by
            apply Finset.sum_le_sum
            intro j hj
            have hj0 : 1 ≤ j :=
              le_trans (Nat.succ_le_succ (Nat.zero_le n))
                (Finset.mem_Icc.mp hj).1
            have hj1 : (1 : Real) ≤ (j : Real) := by
              exact_mod_cast hj0
            have hp : (0 : Real) < (2 : Real) ^ j := by positivity
            have hden : (0 : Real) < (j : Real) * (2 : Real) ^ j :=
              mul_pos (lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hj1) hp
            have hmul := mul_le_mul_of_nonneg_right hj1 (le_of_lt hp)
            exact (div_le_div_iff₀ hden hp).2
              (by simpa only [one_mul] using hmul)
      _ = (1 : Real) / (2 : Real) ^ n -
            (1 : Real) / (2 : Real) ^ (n + d) :=
          stage145_geometric_tail_exact n d
      _ ≤ (1 : Real) / (2 : Real) ^ n := by
          have hp : 0 ≤ (1 : Real) / (2 : Real) ^ (n + d) := by positivity
          linarith

end ECRuntime
