/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# ListBound

Graham's 1966 bound for list scheduling.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The makespan of a list schedule, through the last job `k` of a heaviest machine:
`m · (L_k + p_k) ≤ Σ p + (m − 1) · p_k`. -/
theorem lb_mul_le {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) (hσ :
  IsListSchedule p σ)
    (k : Fin n) : (m : ℝ) * (loadBefore p σ k (σ k) + p k) ≤ ∑ j, p j + (m - 1) * p k := by
  have h1 := bs_mul_loadBefore_le p σ hσ k
  have h2 := bs_sum_filter_add_le p hp k
  linarith

/-- Graham's bound for list scheduling: for nonnegative lengths, every list schedule `σ` and every
assignment `τ`
satisfy `m · C(σ) ≤ (2m − 1) · C(τ)`. -/
theorem listSchedule_bound {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) :
    (m : ℝ) * makespan p σ ≤ (2 * m - 1) * makespan p τ := by
  have hm : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (NeZero.pos m)
  have hτ0 := bs_makespan_nonneg p hp τ
  obtain ⟨i, hi⟩ := bs_exists_load_eq_makespan p σ
  by_cases h : ∃ j, σ j = i
  · obtain ⟨k, hk, hload⟩ := bs_exists_last_job p σ i h
    subst hk
    have hmul := lb_mul_le p hp σ hσ k
    have hsum := sum_le_mul_makespan p τ
    have hpk := le_makespan_of_nonneg p hp τ k
    have hpk' : ((m : ℝ) - 1) * p k ≤ ((m : ℝ) - 1) * makespan p τ :=
      mul_le_mul_of_nonneg_left hpk (by linarith)
    rw [← hi, hload]
    linarith
  · push Not at h
    have h0 := bs_load_eq_zero p σ i h
    rw [← hi, h0, mul_zero]
    exact mul_nonneg (by linarith) hτ0

/-- Every list schedule is within the factor `2 − 1/m` of the optimum. -/
theorem listSchedule_le_optMakespan {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p
  j)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) :
    makespan p σ ≤ (2 - 1 / m) * optMakespan m p := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) p
  have hb := listSchedule_bound p hp σ hσ τ
  rw [hτ] at hb
  have heq : (2 - 1 / (m : ℝ)) * optMakespan m p = (2 * m - 1) * optMakespan m p / m := by
    field_simp
  rw [heq, le_div_iff₀ hm]
  linarith

end GrahamLPT
