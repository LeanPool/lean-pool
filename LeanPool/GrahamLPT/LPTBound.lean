/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.Key
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# LPTBound

Graham's 1969 bound for LPT.
Helpers carry the prefix `lb2_`; the `_internal` twins of the Challenge theorems are closed in
`Contracts.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The sorted form of `lpt_bound`. -/
theorem lb2_bound_sorted {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti :
  Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) :
    3 * (m : ℝ) * makespan p σ ≤ (4 * m - 1) * makespan p τ := by
  have hm : (1 : ℝ) ≤ m := by
    have := NeZero.ne m
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hτ0 : 0 ≤ makespan p τ := bs_makespan_nonneg p hp τ
  obtain ⟨i, hi⟩ := bs_exists_load_eq_makespan p σ
  by_cases h : ∃ j, σ j = i
  · obtain ⟨k, hk, hload⟩ := bs_exists_last_job p σ i h
    have hC : makespan p σ = loadBefore p σ k (σ k) + p k := by rw [← hi, hload, hk]
    rw [hC]
    rcases le_or_gt (3 * p k) (makespan p τ) with h3 | h3
    · have h1 := bs_mul_loadBefore_le p σ hσ k
      have h2 := bs_sum_filter_add_le p hp k
      have h4 := sum_le_mul_makespan_internal p τ
      have h5 := mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 h3)
      nlinarith
    · have hkey := key_lemma p hp hanti σ hσ k τ (makespan p τ)
        (fun i => (bs_loadBefore_le_load p hp τ _ i).trans (load_le_makespan_internal p τ i)) h3
      have h5 := mul_nonneg (sub_nonneg.2 hm) hτ0
      have hm0 : (0 : ℝ) ≤ m := by linarith
      have h6 := mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ 3 * m)
      nlinarith
  · push Not at h
    have h0 : makespan p σ = 0 := by rw [← hi]; exact bs_load_eq_zero p σ i h
    rw [h0, mul_zero]
    exact mul_nonneg (by linarith) hτ0

/-- Graham's bound for LPT: for nonnegative lengths, every LPT schedule `σ` and every assignment
`τ` satisfy
`3m · C(σ) ≤ (4m − 1) · C(τ)`. -/
theorem lpt_bound_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m) :
    3 * (m : ℝ) * makespan p σ ≤ (4 * m - 1) * makespan p τ := by
  obtain ⟨π, hanti, hl⟩ := hσ
  have h := lb2_bound_sorted (p ∘ π) (fun j => hp _) hanti (σ ∘ π) hl (τ ∘ π)
  rwa [makespan_comp_internal, makespan_comp_internal] at h

/-- Every LPT schedule is within the factor `4/3 − 1/(3m)` of the optimum. -/
theorem lpt_le_optMakespan_internal {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) :
    makespan p σ ≤ (4 / 3 - 1 / (3 * m)) * optMakespan m p := by
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan_internal (m := m) p
  have h := lpt_bound_internal p hp σ hσ τ
  rw [hτ] at h
  have hm : (0 : ℝ) < m := by
    have := NeZero.ne m
    exact_mod_cast Nat.pos_of_ne_zero this
  have heq : (4 / 3 - 1 / (3 * (m : ℝ))) * optMakespan m p = (4 * m - 1) * optMakespan m p / (3 *
    m) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  linarith

end GrahamLPT
