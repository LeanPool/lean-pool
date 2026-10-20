/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

public import LeanPool.GrahamLPT.Defs
public import Mathlib.Data.Fin.VecNotation
import LeanPool.GrahamLPT.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity.Finset

/-!
# Counter

The strict third cannot be weakened: on `3` machines the six jobs `9, 5, 5, 4, 4, 4` have an LPT
schedule of makespan `13` while the optimal makespan is `12`. Every job is at least a third of the
optimum (the jobs
of length `4` equal `12 / 3`), so `n ≤ 2m` alone does not make LPT optimal and the strict
hypothesis of
`lpt_optimal_of_third_lt` cannot be weakened to `≤`. Helpers carry the prefix `cx_`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- A set of jobs all assigned to machine `i` has total length at most the load of `i`
(nonnegative lengths). -/
theorem cx_sum_le_load {m n : ℕ} (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (τ : Fin n → Fin m) (i : Fin m)
    (S : Finset (Fin n)) (hS : ∀ j ∈ S, τ j = i) : ∑ j ∈ S, p j ≤ load p τ i := by
  unfold load
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j _ _ => hp j)
  simpa using hS j hj

/-- Among three machines, two values both different from two distinct values coincide. -/
theorem cx_fin3_eq (a b c d : Fin 3) (hba : b ≠ a) (hca : c ≠ a) (hda : d ≠ a) (hcb : c ≠ b)
    (hdb : d ≠ b) : c = d := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [ne_eq, Fin.ext_iff] at *
  omega

/-- Among three machines, a value different from `a` equals one of two distinct values different
from `a`. -/
theorem cx_fin3_or (a b c d : Fin 3) (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) :
    d = b ∨ d = c := by
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [ne_eq, Fin.ext_iff] at *
  omega

/-- `loadBefore` as a sum over all jobs with an `if`. -/
theorem cx_loadBefore_eq {m n : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) :
    loadBefore p σ k i = ∑ j : Fin n, if (j : ℕ) < k ∧ σ j = i then p j else 0 := by
  unfold loadBefore
  rw [Finset.sum_filter]

/-- The instance `9, 5, 5, 4, 4, 4` is listed in nonincreasing order. -/
theorem cx_antitone : Antitone (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) := by
  intro a b h
  revert h
  fin_cases a <;> fin_cases b <;> simp [Fin.le_def] <;> norm_num

/-- The assignment `0, 1, 2, 1, 2, 0` of the jobs `9, 5, 5, 4, 4, 4` to `3` machines is an LPT
schedule (the
identity order) and has makespan `13`. -/
theorem cx_lpt_thirteen :
    IsLPTSchedule (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) (![0, 1, 2, 1, 2, 0] : Fin 6 → Fin 3) ∧
      makespan (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) (![0, 1, 2, 1, 2, 0] : Fin 6 → Fin 3) = 13 := by
  refine ⟨⟨1, ?_, ?_⟩, ?_⟩
  · simpa using cx_antitone
  · intro k i
    simp only [cx_loadBefore_eq, Fin.sum_univ_six, Function.comp_apply, Equiv.Perm.coe_one, id]
    fin_cases k <;> fin_cases i <;> norm_num
  · apply le_antisymm
    · rw [bs_makespan_le_iff]
      intro i
      fin_cases i <;> norm_num [load, Finset.sum_filter, Fin.sum_univ_six]
    · refine le_trans (le_of_eq ?_) (bs_load_le_makespan _ _ 0)
      norm_num [load, Finset.sum_filter, Fin.sum_univ_six]

/-- Every assignment of the jobs `9, 5, 5, 4, 4, 4` to `3` machines has a machine of load at least
`12`. -/
theorem cx_twelve_le_makespan (τ : Fin 6 → Fin 3) :
    12 ≤ makespan (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) τ := by
  set p : Fin 6 → ℝ := ![9, 5, 5, 4, 4, 4] with hpdef
  have hp : ∀ j, 0 ≤ p j := by
    intro j; fin_cases j <;> norm_num [hpdef]
  by_contra hlt
  push Not at hlt
  have key : ∀ (i : Fin 3) (S : Finset (Fin 6)), (∀ j ∈ S, τ j = i) → 12 ≤ ∑ j ∈ S, p j → False :=
    by
    intro i S hS h12
    have h1 := cx_sum_le_load p hp τ i S hS
    have h2 := bs_load_le_makespan p τ i
    linarith
  -- job `0` (length `9`) shares its machine with no other job
  by_cases h1 : τ 1 = τ 0
  · exact key (τ 0) {0, 1} (by simp [h1]) (by norm_num [hpdef])
  by_cases h2 : τ 2 = τ 0
  · exact key (τ 0) {0, 2} (by simp [h2]) (by norm_num [hpdef])
  by_cases h3 : τ 3 = τ 0
  · exact key (τ 0) {0, 3} (by simp [h3]) (by norm_num [hpdef])
  by_cases h4 : τ 4 = τ 0
  · exact key (τ 0) {0, 4} (by simp [h4]) (by norm_num [hpdef])
  by_cases h5 : τ 5 = τ 0
  · exact key (τ 0) {0, 5} (by simp [h5]) (by norm_num [hpdef])
  -- the jobs `3, 4, 5` (length `4`): two share a machine `x`, the third is on the remaining
  -- machine `y`;
  -- the jobs `1, 2` (length `5`) avoid `x` and so both join `y`
  have finish : ∀ (x y : Fin 3) (u v w : Fin 6), τ u = x → τ v = x → τ w = y → x ≠ τ 0 → y ≠ τ 0 →
    y ≠ x →
      p u = 4 → p v = 4 → p w = 4 → u ≠ v → u ≠ 1 → v ≠ 1 → u ≠ 2 → v ≠ 2 → False := by
    intro x y u v w hu hv hw hx0 hy0 hyx pu pv pw huv hu1 hv1 hu2 hv2
    by_cases g1 : τ 1 = x
    · refine key x {1, u, v} ?_ ?_
      · intro j hj
        simp only [mem_insert, mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> assumption
      · rw [Finset.sum_insert (by simp [Ne.symm hu1, Ne.symm hv1]), Finset.sum_pair huv, pu, pv]
        norm_num [hpdef]
    by_cases g2 : τ 2 = x
    · refine key x {2, u, v} ?_ ?_
      · intro j hj
        simp only [mem_insert, mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> assumption
      · rw [Finset.sum_insert (by simp [Ne.symm hu2, Ne.symm hv2]), Finset.sum_pair huv, pu, pv]
        norm_num [hpdef]
    have e1 : τ 1 = y := cx_fin3_eq (τ 0) x (τ 1) y hx0 h1 hy0 g1 hyx
    have e2 : τ 2 = y := cx_fin3_eq (τ 0) x (τ 2) y hx0 h2 hy0 g2 hyx
    have hw1 : w ≠ 1 := by rintro rfl; norm_num [hpdef] at pw
    have hw2 : w ≠ 2 := by rintro rfl; norm_num [hpdef] at pw
    refine key y {1, 2, w} ?_ ?_
    · intro j hj
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl | rfl <;> assumption
    · rw [Finset.sum_insert (by simp [Ne.symm hw1]), Finset.sum_pair (Ne.symm hw2), pw]
      norm_num [hpdef]
  have p3 : p 3 = 4 := by simp [hpdef]
  have p4 : p 4 = 4 := by simp [hpdef]
  have p5 : p 5 = 4 := by simp [hpdef]
  by_cases h34 : τ 4 = τ 3
  · by_cases h35 : τ 5 = τ 3
    · refine key (τ 3) {3, 4, 5} ?_ ?_
      · intro j hj
        simp only [mem_insert, mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> simp [h34, h35]
      · norm_num [hpdef]
    · exact finish (τ 3) (τ 5) 3 4 5 rfl h34 rfl h3 h5 h35 p3 p4 p5
        (by decide) (by decide) (by decide) (by decide) (by decide)
  · rcases cx_fin3_or (τ 0) (τ 3) (τ 4) (τ 5) h3 h4 h34 h5 with h53 | h54
    · exact finish (τ 3) (τ 4) 3 5 4 rfl h53 rfl h3 h4 h34 p3 p5 p4
        (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact finish (τ 4) (τ 3) 4 5 3 rfl h54 rfl h4 h3 (Ne.symm h34) p4 p5 p3
        (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The jobs `9, 5, 5, 4, 4, 4` have optimal makespan `12` on `3` machines, attained by `0, 1, 1,
2, 2, 2`. -/
theorem cx_opt_twelve : optMakespan 3 (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) = 12 := by
  apply le_antisymm
  · refine le_trans (optMakespan_le_internal _ (![0, 1, 1, 2, 2, 2] : Fin 6 → Fin 3)) ?_
    rw [bs_makespan_le_iff]
    intro i
    fin_cases i <;> norm_num [load, Finset.sum_filter, Fin.sum_univ_six]
  · obtain ⟨τ, hτ⟩ := bs_exists_makespan_eq_opt (m := 3) (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ)
    rw [← hτ]
    exact cx_twelve_le_makespan τ

/-- The strict hypothesis of `lpt_optimal_of_third_lt` cannot be weakened to `≤`, and `n ≤ 2m`
jobs do not make LPT
optimal: on `3` machines the six jobs `9, 5, 5, 4, 4, 4` are each at least a third of the optimal
makespan `12`,
yet an LPT schedule of them has makespan `13`. -/
theorem cx_third_le_not_optimal :
    ∃ (p : Fin 6 → ℝ) (σ : Fin 6 → Fin 3), (∀ j, 0 ≤ p j) ∧ IsLPTSchedule p σ ∧
      (∀ j, optMakespan 3 p ≤ 3 * p j) ∧ optMakespan 3 p < makespan p σ := by
  refine ⟨![9, 5, 5, 4, 4, 4], ![0, 1, 2, 1, 2, 0], ?_, cx_lpt_thirteen.1, ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num
  · intro j
    rw [cx_opt_twelve]
    fin_cases j <;> norm_num
  · rw [cx_opt_twelve, cx_lpt_thirteen.2]
    norm_num

theorem nine_five_four_lpt_thirteen_internal :
    IsLPTSchedule (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) (![0, 1, 2, 1, 2, 0] : Fin 6 → Fin 3) ∧
      makespan (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) (![0, 1, 2, 1, 2, 0] : Fin 6 → Fin 3) = 13 :=
  cx_lpt_thirteen

theorem nine_five_four_optMakespan_internal : optMakespan 3 (![9, 5, 5, 4, 4, 4] : Fin 6 → ℝ) = 12
  :=
  cx_opt_twelve

theorem lpt_third_le_not_optimal_internal :
    ∃ (p : Fin 6 → ℝ) (σ : Fin 6 → Fin 3), (∀ j, 0 ≤ p j) ∧ IsLPTSchedule p σ ∧
      (∀ j, optMakespan 3 p ≤ 3 * p j) ∧ optMakespan 3 p < makespan p σ :=
  cx_third_le_not_optimal

end GrahamLPT
