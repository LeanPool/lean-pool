/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
import LeanPool.GrahamLPT.Basic
import LeanPool.GrahamLPT.Equality
import LeanPool.GrahamLPT.GrahamScaled
import LeanPool.GrahamLPT.LPTBound
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Finset

/-!
# LPTForm

Dósa's theorem for LPT schedules, the two-way statement, and the strict inequality for every job
count other than `2m + 1`.
-/

@[expose] public section

namespace GrahamLPT

open Finset


/-- Dósa's theorem for LPT schedules: on `m ≥ 2` machines, an LPT schedule of a nonempty positive
instance attains Graham's
bound against the optimum only when the instance is a positive multiple of Graham's `2m + 1` jobs
in some order. -/
theorem graham_of_lpt_eq_bound_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n
  → ℝ) (hp : ∀ j, 0 < p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (heq : 3 * m * makespan p σ = (4 * m - 1) *
      optMakespan m p) :
    ∃ (a : ℝ) (e : Fin n ≃ Fin (2 * m + 1)), 0 < a ∧ ∀ j, p j = a * grahamJobs m (e j) := by
  obtain ⟨π, hanti, hls⟩ := hσ
  have heq' : 3 * m * makespan (p ∘ π) (σ ∘ π) = (4 * m - 1) * optMakespan m (p ∘ π) := by
    rw [makespan_comp_internal, gs_optMakespan_comp]
    exact heq
  obtain ⟨a, h, ha, hpa⟩ :=
    graham_of_listSchedule_eq_bound_internal hm hn (p ∘ π) (fun j => hp (π j)) hanti (σ ∘ π) hls
      heq'
  refine ⟨a, π.symm.trans (finCongr h), ha, fun j => ?_⟩
  have hj := hpa (π.symm j)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hj
  exact hj

/-- Graham's example is the only tight one (Dósa 2004): for a nonempty positive instance on `m ≥
2` machines, some LPT
schedule attains Graham's bound `3m · C(σ) = (4m − 1) · optMakespan` if and only if the instance
is a positive
multiple of Graham's `2m + 1` jobs in some order (and then every LPT schedule attains it,
`lpt_eq_bound_of_graham`). -/
theorem lpt_eq_bound_iff_graham_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (p : Fin n
  → ℝ)
    (hp : ∀ j, 0 < p j) :
    (∃ σ : Fin n → Fin m, IsLPTSchedule p σ ∧ 3 * m * makespan p σ = (4 * m - 1) * optMakespan m
      p) ↔
      ∃ (a : ℝ) (e : Fin n ≃ Fin (2 * m + 1)), 0 < a ∧ ∀ j, p j = a * grahamJobs m (e j) := by
  constructor
  · rintro ⟨σ, hσ, heq⟩
    exact graham_of_lpt_eq_bound_internal hm hn p hp σ hσ heq
  · rintro ⟨a, e, ha, he⟩
    obtain ⟨σ, hσ⟩ := exists_isLPTSchedule_internal (m := m) p
    exact ⟨σ, hσ, lpt_eq_bound_of_graham_internal p a ha e he σ hσ⟩

/-- With any number of jobs other than `2m + 1`, no LPT schedule of a nonempty positive instance
on `m ≥ 2` machines attains
Graham's bound: the inequality is strict. -/
theorem lpt_lt_bound_of_card_ne_internal {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (hn : 0 < n) (hn' : n ≠
  2 * m + 1)
    (p : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) :
    3 * m * makespan p σ < (4 * m - 1) * optMakespan m p := by
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan_internal (m := m) p
  have hle := lpt_bound_internal p (fun j => (hp j).le) σ hσ τ
  rw [hτ] at hle
  refine lt_of_le_of_ne hle fun heq => hn' ?_
  obtain ⟨_, e, _, _⟩ := graham_of_lpt_eq_bound_internal hm hn p hp σ hσ heq
  simpa using Fintype.card_congr e

end GrahamLPT
