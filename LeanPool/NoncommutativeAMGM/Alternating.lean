/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Basic

/-!
# Finite alternating-sum estimates

The pairing argument used in Section 3.6. The nonnegativity and monotonicity
hypotheses concern only the finite range in the sum.
-/

public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- Every finite alternating sum starting with a positive term is nonnegative
when its terms are nonnegative and decreasing. -/
theorem alternating_sum_nonneg (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i < N, 0 ≤ a i) (hdec : ∀ i, i + 1 < N → a (i + 1) ≤ a i) :
    0 ≤ ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * a i := by
  induction N using Nat.twoStepInduction generalizing a with
  | zero => simp
  | one => simpa using ha 0 (by omega)
  | more N ih _ =>
    have htail := ih (fun i ↦ a (i + 2))
      (fun i hi ↦ ha (i + 2) (by omega))
      (fun i hi ↦ hdec (i + 2) (by omega))
    have hpair : 0 ≤ a 0 - a 1 := sub_nonneg.mpr (hdec 0 (by omega))
    have hsplit : (∑ i ∈ Finset.range (N + 2), (-1 : ℝ) ^ i * a i) =
        (a 0 - a 1) + ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * a (i + 2) := by
      rw [show N + 2 = 2 + N by omega, Finset.sum_range_add]
      simp [Finset.sum_range_succ, pow_add, Nat.add_comm, sub_eq_add_neg]
    rw [hsplit]
    exact add_nonneg hpair htail

/-- The finite alternating tail is bounded below by minus its first term.
This avoids the parity-dependent endpoint bookkeeping in Section 3.6. -/
theorem alternating_sum_ge_neg_first (N : ℕ) (a : ℕ → ℝ)
    (ha0 : 0 ≤ a 0) (ha : ∀ i < N, 0 ≤ a i)
    (hdec : ∀ i, i + 1 < N → a (i + 1) ≤ a i) :
    -a 0 ≤ ∑ i ∈ Finset.range N, (-1 : ℝ) ^ (i + 1) * a i := by
  by_cases hN : N = 0
  · simp only [hN, Finset.range_zero, Finset.sum_empty]
    linarith
  · obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
    have htail := alternating_sum_nonneg M (fun i ↦ a (i + 1))
      (fun i hi ↦ ha (i + 1) (by omega))
      (fun i hi ↦ hdec (i + 1) (by omega))
    rw [Finset.sum_range_succ']
    have hshift : (∑ i ∈ Finset.range M, (-1 : ℝ) ^ (i + 1 + 1) * a (i + 1)) =
        ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * a (i + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [pow_add]
    rw [hshift]
    simp only [zero_add, pow_one, neg_mul, one_mul]
    linarith

end NoncommutativeAMGM
