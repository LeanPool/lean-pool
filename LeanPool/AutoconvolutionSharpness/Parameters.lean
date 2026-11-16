/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The factorial and geometric factors in the lower bound

The factorial ratio admits a lower bound uniform in the central index.
The finite geometric quotient includes both endpoints of each sum.
-/

@[expose] public section

open Finset

namespace Autoconvolutions.Parameters

/-- The factorial factor with central index `N = 2 * n` and displacement `j`. -/
noncomputable def factorialRatio (N j : ℕ) : ℝ :=
  (N.factorial : ℝ) ^ 2 / (((N - j).factorial : ℝ) * ((N + j).factorial : ℝ))

private theorem factorialRatio_succ {N j : ℕ} (hj : j < N) :
    factorialRatio N (j + 1) =
      (((N : ℝ) - j) / (N + j + 1)) * factorialRatio N j := by
  have h₁ : N - j = (N - (j + 1)) + 1 := by omega
  have h₂ : N + (j + 1) = (N + j) + 1 := by omega
  have h₃ : ((N - (j + 1) : ℕ) : ℝ) + 1 = N - j := by
    rw [Nat.cast_sub (by omega : j + 1 ≤ N)]
    push_cast
    ring
  unfold factorialRatio
  rw [h₁, h₂, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [h₃]
  have h₄ : (j : ℝ) < N := by exact_mod_cast hj
  have h₅ : (0 : ℝ) < (N - (j + 1)).factorial := by positivity
  have h₆ : (0 : ℝ) < (N + j).factorial := by positivity
  field_simp

/-- A quantitative form of the factorial product estimate, for any
displacement through the central index. -/
theorem factorialRatio_lower {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    1 - (j : ℝ) ^ 2 / N ≤ factorialRatio N j := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  induction j with
  | zero =>
    simp [factorialRatio, pow_two, (Nat.factorial_pos N).ne']
  | succ j ih =>
    have hj' : j < N := by omega
    have hjR : (j : ℝ) < N := by exact_mod_cast hj'
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hp : 0 ≤ ((N : ℝ) - j) / (N + j + 1) := by positivity
    have hstep : 1 - ((j : ℝ) + 1) ^ 2 / N ≤
        (((N : ℝ) - j) / (N + j + 1)) * (1 - (j : ℝ) ^ 2 / N) := by
      have hden : (0 : ℝ) < N + j + 1 := by positivity
      field_simp
      nlinarith [sq_nonneg (j : ℝ), mul_nonneg hj0 (sq_nonneg (j : ℝ))]
    rw [factorialRatio_succ hj', Nat.cast_succ]
    exact hstep.trans (mul_le_mul_of_nonneg_left (ih (by omega)) hp)

/-- The finite geometric quotient in the paper (both sums include `K`). -/
noncomputable def geomRatio (q : ℝ) (K : ℕ) : ℝ :=
  (∑ s ∈ range (K + 1), (s : ℝ) * q ^ s) / (∑ s ∈ range (K + 1), q ^ s) ^ 2

end Autoconvolutions.Parameters
