/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.LPTBound
import LeanPool.GrahamLPT.ListBound
import LeanPool.GrahamLPT.TightLPT
import LeanPool.GrahamLPT.TightList
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Ratio

The least constants, `2 − 1/m` and `4/3 − 1/(3m)`.
Helpers carry the prefix `rt_`; the `_internal` twins of the Challenge theorems are closed in
`Contracts.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- `2 − 1/m` is the least constant `c` with `C(σ) ≤ c · C(τ)` for every list schedule `σ` of every
nonnegative instance on `m` machines and every assignment `τ`. -/
theorem isLeast_listSchedule_ratio_internal (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsListSchedule p σ → makespan p σ ≤ c * makespan p τ} (2 - 1 / m) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hc : (2 : ℝ) - 1 / m = (2 * m - 1) / m := by field_simp
  refine ⟨?_, ?_⟩
  · intro n p σ τ hp hσ
    have h := listSchedule_bound_internal p hp σ hσ τ
    rw [hc, div_mul_eq_mul_div, le_div_iff₀ hm]
    linarith
  · intro c hc'
    obtain ⟨σ, hσ⟩ := exists_isListSchedule_internal (m := m) (unitJobs m)
    obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan_internal (m := m) (unitJobs m)
    have h := hc' _ (unitJobs m) σ τ (tl_unitJobs_nonneg m) hσ
    rw [unitJobs_listSchedule_makespan_internal m σ hσ, hτ, unitJobs_optMakespan_internal m] at h
    rw [hc, div_le_iff₀ hm]
    linarith

/-- `4/3 − 1/(3m)` is the least constant `c` with `C(σ) ≤ c · C(τ)` for every LPT schedule `σ` of
every nonnegative
instance on `m` machines and every assignment `τ`. -/
theorem isLeast_lpt_ratio_internal (m : ℕ) [NeZero m] :
    IsLeast {c : ℝ | ∀ (n : ℕ) (p : Fin n → ℝ) (σ τ : Fin n → Fin m), (∀ j, 0 ≤ p j) →
      IsLPTSchedule p σ → makespan p σ ≤ c * makespan p τ} (4 / 3 - 1 / (3 * m)) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hm3 : (0 : ℝ) < 3 * m := by positivity
  have hc : (4 : ℝ) / 3 - 1 / (3 * m) = (4 * m - 1) / (3 * m) := by field_simp
  refine ⟨?_, ?_⟩
  · intro n p σ τ hp hσ
    have h := lpt_bound_internal p hp σ hσ τ
    rw [hc, div_mul_eq_mul_div, le_div_iff₀ hm3]
    linarith
  · intro c hc'
    obtain ⟨σ, hσ⟩ := exists_isLPTSchedule_internal (m := m) (grahamJobs m)
    obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan_internal (m := m) (grahamJobs m)
    have h := hc' _ (grahamJobs m) σ τ (tg_grahamJobs_nonneg m) hσ
    rw [grahamJobs_lpt_makespan_internal m σ hσ, hτ, grahamJobs_optMakespan_internal m] at h
    rw [hc, div_le_iff₀ hm3]
    linarith

end GrahamLPT
