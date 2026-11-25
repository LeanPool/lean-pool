/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.Coefficients
public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.Power
public import Mathlib.Tactic.Ring

/-!
# Uniform bounds for finite homogeneous power truncations

A single bound controls every power below a degree cutoff from homogeneous input tails.

## Main results

* `FQFP.norm_pow_sub_positivePowerTrunc_le`.
-/

@[expose] public section
open Finset
namespace FQFP

private lemma two_pow_add_sum_reverse (m k : ℕ) :
    (2 : ℝ) ^ m + ∑ i ∈ range k, (2 : ℝ) ^ (m + k - 1 - i) = 2 ^ (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ']
    have hsum : (∑ i ∈ range k, (2 : ℝ) ^ (m + (k + 1) - 1 - (i + 1))) =
        ∑ i ∈ range k, (2 : ℝ) ^ (m + k - 1 - i) := by
      apply sum_congr rfl
      intro i hi
      congr 1
      have := mem_range.mp hi
      lia
    rw [hsum, show m + (k + 1) - 1 - 0 = m + k by lia]
    calc
      _ = (2 ^ m + ∑ i ∈ range k, (2 : ℝ) ^ (m + k - 1 - i)) + 2 ^ (m + k) := by ring
      _ = _ := by
        rw [ih, show m + (k + 1) = (m + k) + 1 by lia, pow_succ]
        ring

/-- Homogeneous input bounds and all input tails control every finite power truncation. -/
theorem norm_pow_sub_positivePowerTrunc_le {A : Type*} [NormedRing A]
    (y : A) (u : ℕ → A) {s : ℝ} (hs : 0 ≤ s) (hy : ‖y‖ ≤ 2 * s)
    (k n : ℕ) (hkn : k < n)
    (hu : ∀ i, 1 ≤ i → i < n → ‖u i‖ ≤ s ^ i)
    (hR : ∀ j, 2 ≤ j → j ≤ n →
      ‖y - ∑ i ∈ range (j - 1), u (i + 1)‖ ≤ s ^ j) :
    ‖y ^ k - positivePowerTrunc u k n‖ ≤ (2 : ℝ) ^ (n - 1) * s ^ n := by
  induction k generalizing n with
  | zero => simp [positivePowerTrunc, show n ≠ 0 by lia, hs]
  | succ k ih =>
    let M := n - (k + 1)
    have hM : M + k + 1 = n := by
      dsimp [M]
      lia
    have htail : ‖y - ∑ i ∈ range M, u (i + 1)‖ ≤ s ^ (M + 1) := by
      simpa only [Nat.add_sub_cancel] using hR (M + 1) (by lia) (by lia)
    have hfirst : ‖(y - ∑ i ∈ range M, u (i + 1)) * y ^ k‖ ≤ 2 ^ k * s ^ n := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa only [pow_zero, mul_one, one_mul, show M + 1 = n by lia] using htail
      · calc
          _ ≤ s ^ (M + 1) * (2 * s) ^ k :=
            norm_mul_le_of_le htail ((norm_pow_le' y hk).trans
              (pow_le_pow_left₀ (norm_nonneg y) hy k))
          _ = 2 ^ k * (s ^ (M + 1) * s ^ k) := by
            rw [mul_pow]
            ring
          _ = _ := by rw [← pow_add, show M + 1 + k = n by lia]
    have hterm (i : ℕ) (hi : i ∈ range M) :
        ‖u (i + 1) * (y ^ k - positivePowerTrunc u k (n - (i + 1)))‖ ≤
          (2 : ℝ) ^ (n - (i + 1) - 1) * s ^ n := by
      have hiM := mem_range.mp hi
      have hiN : i + 1 ≤ n := by lia
      have hr := ih (n - (i + 1)) (by lia)
        (fun j hj hjn ↦ hu j hj (by lia)) (fun j hj hjn ↦ hR j hj (by lia))
      calc
        _ ≤ s ^ (i + 1) * (2 ^ (n - (i + 1) - 1) * s ^ (n - (i + 1))) :=
          norm_mul_le_of_le (hu (i + 1) (by lia) (by lia)) hr
        _ = 2 ^ (n - (i + 1) - 1) * (s ^ (i + 1) * s ^ (n - (i + 1))) := by ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hiN]
    have hconst : (2 : ℝ) ^ k + ∑ i ∈ range M, (2 : ℝ) ^ (n - (i + 1) - 1) =
        2 ^ (n - 1) := by
      have heq : (∑ i ∈ range M, (2 : ℝ) ^ (n - (i + 1) - 1)) =
          ∑ i ∈ range M, (2 : ℝ) ^ (k + M - 1 - i) := by
        apply sum_congr rfl
        intro i hi
        congr 1
        have := mem_range.mp hi
        lia
      rw [heq, two_pow_add_sum_reverse, show k + M = n - 1 by lia]
    rw [pow_sub_positivePowerTrunc_succ]
    calc
      _ ≤ 2 ^ k * s ^ n + ∑ i ∈ range M, 2 ^ (n - (i + 1) - 1) * s ^ n :=
        norm_add_le_of_le hfirst ((norm_sum_le _ _).trans (sum_le_sum hterm))
      _ = (2 ^ k + ∑ i ∈ range M, (2 : ℝ) ^ (n - (i + 1) - 1)) * s ^ n := by
        rw [add_mul, sum_mul]
      _ = _ := by rw [hconst]

end FQFP
