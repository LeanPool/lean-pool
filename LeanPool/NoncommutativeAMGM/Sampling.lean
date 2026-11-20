/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Basic

/-!
# Sampling without replacement

The motivational probability display on page 2 has its inequality reversed.
This file proves the corrected upper bound and certifies a counterexample to
the printed direction. This observation does not refute either main theorem.
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- Probability of no repeated index in `m` independent uniform draws from `n` indices. -/
noncomputable def noRepetitionProbability (n m : ℕ) : ℝ :=
  ∏ i ∈ Finset.range m, (1 - (i : ℝ) / n)

theorem sum_range_cast (m : ℕ) :
    ∑ i ∈ Finset.range m, (i : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The valid exponential inequality has the upper-bound direction. -/
theorem noRepetitionProbability_le_exp {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) :
    noRepetitionProbability n m ≤
      Real.exp (-(m : ℝ) * ((m : ℝ) - 1) / (2 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : noRepetitionProbability n m ≤
      ∏ i ∈ Finset.range m, Real.exp (-(i : ℝ) / n) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      have hiR : (i : ℝ) ≤ n := by exact_mod_cast (le_trans (Finset.mem_range.mp hi).le hm)
      exact sub_nonneg.mpr ((div_le_one hnR).mpr hiR)
    · intro i _
      simpa only [neg_div] using Real.one_sub_le_exp_neg ((i : ℝ) / n)
  have hsum : (∑ i ∈ Finset.range m, -(i : ℝ) / n) =
      -(m : ℝ) * ((m : ℝ) - 1) / (2 * n) := by
    simp_rw [neg_div]
    rw [Finset.sum_neg_distrib, ← Finset.sum_div, sum_range_cast]
    ring
  exact hprod.trans_eq ((Real.exp_sum _ _).symm.trans (congrArg Real.exp hsum))

/-- Exact counterexample to the lower-bound direction printed on page 2. -/
theorem printed_sampling_lower_bound_fails :
    ¬ Real.exp (-(2 : ℝ) * (2 - 1) / (2 * 2)) ≤ noRepetitionProbability 2 2 := by
  have hexp := Real.one_sub_lt_exp_neg (x := (1 / 2 : ℝ)) (by norm_num)
  norm_num [noRepetitionProbability, Finset.prod_range_succ] at *
  linarith

end NoncommutativeAMGM
