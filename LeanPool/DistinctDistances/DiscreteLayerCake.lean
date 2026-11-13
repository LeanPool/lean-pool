/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# A discrete layer-cake bound for monotone thresholds

The same telescoping inequality supports the centroid and second-moment bounds.
-/

@[expose] public section

namespace Esgk

open scoped BigOperators

/-- Telescoping: for `τ` nondecreasing on `0, …, k`, the increments `τ (i+1) - τ i` over the
indices `i < k` with `x ≤ τ i` sum to at most `max 0 (τ k - x)`. -/
lemma sum_ite_increment_le_max {k : ℕ} (τ : ℕ → ℝ) (hτ : ∀ i < k, τ i ≤ τ (i + 1))
    (x : ℝ) :
    ∑ i ∈ Finset.range k, (if x ≤ τ i then τ (i + 1) - τ i else 0) ≤ max 0 (τ k - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ih' := ih (fun i hi ↦ hτ i (Nat.lt_trans hi (Nat.lt_succ_self k)))
    have hk := hτ k (Nat.lt_succ_self k)
    split_ifs with hx
    · rw [max_eq_right (by linarith)] at ih'
      linarith [le_max_right 0 (τ (k + 1) - x)]
    · rw [max_eq_left (by linarith)] at ih'
      linarith [le_max_left 0 (τ (k + 1) - x)]

end Esgk
