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
# OptList

The order `grahamOrder` of Graham's family, its lengths, and the optimum attained by a list
schedule in that order.
Helpers carry the prefix `ol_`; the `_internal` twins of the Challenge theorems are closed in
`Contracts.lean`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The order `grahamOrder m` is a permutation of the `2m + 1` jobs. -/
theorem grahamOrder_bijective_internal (m : ℕ) : Function.Bijective (grahamOrder m) := by
  rw [← Finite.injective_iff_bijective]
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  simp only [grahamOrder] at h
  rw [Fin.ext_iff]
  split_ifs at h <;> simp only [Fin.mk.injEq] at h <;> omega

/-- The machine of each position, as a natural number: `i` for `i < m − 1`; the last machine `m −
1` for positions
`m − 1`, `m` and `2m`; `2m − 1 − i` (that is, `m − 2 − a`) for position `m + 1 + a`. -/
def optimalMachineIndex (m i : ℕ) : ℕ :=
  if i < m - 1 then i else if i ≤ m then m - 1 else if i < 2 * m then 2 * m - 1 - i else m - 1

/-- The machine of each position: `i` for `i < m − 1`; the last machine for positions `m − 1`, `m`
and `2m`;
`m − 2 − a` (that is, `2m − 1 − i`) for position `i = m + 1 + a`, the least loaded one at that
step. -/
def optimalMachine (m : ℕ) [NeZero m] (i : Fin (2 * m + 1)) : Fin m :=
  ⟨optimalMachineIndex m i, by have := NeZero.pos m; unfold optimalMachineIndex; split_ifs <;>
      omega⟩

/-- The length of the job at each position, as a natural number. -/
def orderedJobLength (m i : ℕ) : ℕ :=
  if i < m - 1 then 2 * m - 1 - i else if i ≤ m then m else if i < 2 * m then 3 * m - i else m

/-- The load of machine `b` from the positions below `k`, as a natural number. -/
def optimalPrefixLoad (m k b : ℕ) : ℕ :=
  if b < m - 1 then (if b < k then 2 * m - 1 - b else 0) + (if 2 * m - 1 - b < k then m + 1 + b
    else 0)
  else (if m - 1 < k then m else 0) + (if m < k then m else 0) + (if 2 * m < k then m else 0)

theorem ol_q (m : ℕ) [NeZero m] (j : Fin (2 * m + 1)) : grahamJobs m (grahamOrder m j) =
    (orderedJobLength m
  j : ℝ) := by
  have hj := j.isLt
  have hm := NeZero.pos m
  simp only [grahamOrder]
  split_ifs with h₁ h₂ h₃ h₄
  · have hA : 2 * (j : ℕ) < 2 * m := by omega
    have hc : (2 * (j : ℕ)) / 2 = j := by omega
    simp only [grahamJobs, orderedJobLength, h₁, hA, hc, ite_true]
    have : ((2 * m - 1 - j : ℕ) : ℝ) + (j : ℝ) + 1 = 2 * (m : ℝ) := by
      exact_mod_cast (show 2 * m - 1 - (j : ℕ) + (j : ℕ) + 1 = 2 * m by omega)
    linarith
  · have hA : 2 * m - 2 < 2 * m := by omega
    have hle : (j : ℕ) ≤ m := by omega
    have hc : (2 * m - 2) / 2 = m - 1 := by omega
    simp only [grahamJobs, orderedJobLength, h₁, hle, hA, hc, ite_true, ite_false]
    have : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast (show m - 1 + 1 = m by omega)
    linarith
  · have hA : 2 * m - 1 < 2 * m := by omega
    have hle : (j : ℕ) ≤ m := by omega
    have hc : (2 * m - 1) / 2 = m - 1 := by omega
    simp only [grahamJobs, orderedJobLength, h₁, hle, hA, hc, ite_true, ite_false]
    have : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast (show m - 1 + 1 = m by omega)
    linarith
  · have hA : 2 * ((j : ℕ) - m - 1) + 1 < 2 * m := by omega
    have hle : ¬ (j : ℕ) ≤ m := by omega
    have hc : (2 * ((j : ℕ) - m - 1) + 1) / 2 = (j : ℕ) - m - 1 := by omega
    simp only [grahamJobs, orderedJobLength, h₁, hle, h₄, hA, hc, ite_true, ite_false]
    have : ((3 * m - j : ℕ) : ℝ) + (((j : ℕ) - m - 1 : ℕ) : ℝ) + 1 = 2 * (m : ℝ) := by
      exact_mod_cast (show 3 * m - (j : ℕ) + ((j : ℕ) - m - 1) + 1 = 2 * m by omega)
    linarith
  · have hA : ¬ 2 * m < 2 * m := by omega
    have hle : ¬ (j : ℕ) ≤ m := by omega
    simp only [grahamJobs, orderedJobLength, h₁, hle, h₄, hA, ite_false]

/-- The lengths of Graham's instance taken in the order `grahamOrder m` are
`2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m`: position `i` holds length `2m − 1 − i` for `i < m −
1`, `m` for
`i = m − 1` and `i = m`, `3m − i` for `m < i < 2m`, and `m` for `i = 2m`. -/
theorem grahamJobs_grahamOrder_internal (m : ℕ) (i : Fin (2 * m + 1)) :
    grahamJobs m (grahamOrder m i) =
      if (i : ℕ) < m - 1 then 2 * (m : ℝ) - 1 - ((i : ℕ) : ℝ)
      else if (i : ℕ) ≤ m then (m : ℝ)
      else if (i : ℕ) < 2 * m then 3 * (m : ℝ) - ((i : ℕ) : ℝ)
      else (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [grahamJobs, grahamOrder]
  · have : NeZero m := ⟨by omega⟩
    rw [ol_q]
    unfold orderedJobLength
    split_ifs with h₁ h₂ h₃
    · have : ((2 * m - 1 - i : ℕ) : ℝ) + ((i : ℕ) : ℝ) + 1 = 2 * (m : ℝ) := by
        exact_mod_cast (show 2 * m - 1 - (i : ℕ) + (i : ℕ) + 1 = 2 * m by omega)
      linarith
    · rfl
    · have : ((3 * m - i : ℕ) : ℝ) + ((i : ℕ) : ℝ) = 3 * (m : ℝ) := by
        exact_mod_cast (show 3 * m - (i : ℕ) + (i : ℕ) = 3 * m by omega)
      linarith
    · rfl

theorem ol_loadBefore (m : ℕ) [NeZero m] (k : ℕ) (b : Fin m) :
    loadBefore (grahamJobs m ∘ grahamOrder m) (optimalMachine m) k b = (optimalPrefixLoad m k b :
        ℝ) := by
  have hm := NeZero.pos m
  have hbm := b.isLt
  by_cases hb : (b : ℕ) < m - 1
  · have hfib : univ.filter (fun j : Fin (2 * m + 1) => (j : ℕ) < k ∧ optimalMachine m j = b) =
        ({⟨b, by omega⟩, ⟨2 * m - 1 - b, by omega⟩} : Finset (Fin (2 * m + 1))).filter
          (fun j : Fin (2 * m + 1) => (j : ℕ) < k) := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff,
          optimalMachine,
        optimalMachineIndex]
      split_ifs <;> omega
    rw [loadBefore, hfib, sum_filter, sum_pair (by simp only [ne_eq, Fin.ext_iff]; omega)]
    simp only [Function.comp_apply, ol_q]
    have e1 : orderedJobLength m b = 2 * m - 1 - b := by
      unfold orderedJobLength
      rw [ite_eq_left hb]
    have e2 : orderedJobLength m (2 * m - 1 - b) = m + 1 + b := by
      unfold orderedJobLength
      split_ifs <;> omega
    rw [e1, e2]
    unfold optimalPrefixLoad
    rw [ite_eq_left hb]
    split_ifs <;> push_cast [Nat.cast_add] <;> ring
  · have hb' : (b : ℕ) = m - 1 := by omega
    have hfib : univ.filter (fun j : Fin (2 * m + 1) => (j : ℕ) < k ∧ optimalMachine m j = b) =
        ({⟨m - 1, by omega⟩, ⟨m, by omega⟩, ⟨2 * m, by omega⟩} : Finset (Fin (2 * m + 1))).filter
          (fun j : Fin (2 * m + 1) => (j : ℕ) < k) := by
      ext j
      have hj := j.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff,
          optimalMachine,
        optimalMachineIndex]
      split_ifs <;> omega
    have hnot : (⟨m - 1, by omega⟩ : Fin (2 * m + 1)) ∉ ({⟨m, by omega⟩, ⟨2 * m, by omega⟩} :
      Finset _) := by
      simp only [mem_insert, mem_singleton, Fin.ext_iff]
      omega
    rw [loadBefore, hfib, sum_filter, sum_insert hnot,
      sum_pair (by simp only [ne_eq, Fin.ext_iff]; omega)]
    simp only [Function.comp_apply, ol_q]
    have e1 : orderedJobLength m (m - 1) = m := by unfold orderedJobLength; split_ifs <;> omega
    have e2 : orderedJobLength m m = m := by unfold orderedJobLength; split_ifs <;> omega
    have e3 : orderedJobLength m (2 * m) = m := by unfold orderedJobLength; split_ifs <;> omega
    rw [e1, e2, e3]
    unfold optimalPrefixLoad
    rw [ite_eq_right hb]
    split_ifs <;> push_cast [Nat.cast_add] <;> ring

theorem ol_listN (m k b : ℕ) (hk : k ≤ 2 * m) (hb : b < m) :
    optimalPrefixLoad m k (optimalMachineIndex m k) ≤ optimalPrefixLoad m k b := by
  unfold optimalPrefixLoad optimalMachineIndex
  split_ifs <;> omega

/-- In the order `grahamOrder m`, the schedule `optimalMachine` is a list schedule. -/
theorem ol_isListSchedule (m : ℕ) [NeZero m] :
    IsListSchedule (grahamJobs m ∘ grahamOrder m) (optimalMachine m) := by
  intro k i
  rw [ol_loadBefore, ol_loadBefore]
  exact_mod_cast ol_listN m k i (by have := k.isLt; omega) i.isLt

theorem ol_load (m : ℕ) [NeZero m] (b : Fin m) :
    load (grahamJobs m ∘ grahamOrder m) (optimalMachine m) b = 3 * (m : ℝ) := by
  rw [← bs_loadBefore_of_le _ _ (2 * m + 1) le_rfl, ol_loadBefore]
  have hb := b.isLt
  have : optimalPrefixLoad m (2 * m + 1) b = 3 * m := by unfold optimalPrefixLoad; split_ifs <;>
      omega
  rw [this]
  push_cast
  ring

/-- Its makespan is `3m`. -/
theorem ol_makespan (m : ℕ) [NeZero m] :
    makespan (grahamJobs m ∘ grahamOrder m) (optimalMachine m) = 3 * m := by
  apply le_antisymm
  · rw [bs_makespan_le_iff]
    intro i
    rw [ol_load]
  · rw [← ol_load m ⟨0, NeZero.pos m⟩]
    exact load_le_makespan_internal _ _ _

/-- The optimum `3m` of Graham's instance is attained by a list schedule in the order `grahamOrder
m`, that is
`2m − 1, …, m + 1, m, m, 2m − 1, …, m + 1, m` (`grahamJobs_grahamOrder`): some assignment `σ` is a
list schedule of
the jobs taken in that order and has makespan `3m`. -/
theorem grahamJobs_exists_optimal_listSchedule_internal (m : ℕ) [NeZero m] :
    ∃ σ : Fin (2 * m + 1) → Fin m,
      IsListSchedule (grahamJobs m ∘ grahamOrder m) (σ ∘ grahamOrder m) ∧ makespan (grahamJobs m)
        σ = 3 * m := by
  let π : Equiv.Perm (Fin (2 * m + 1)) := Equiv.ofBijective _ (grahamOrder_bijective_internal m)
  have hπ : (π : Fin (2 * m + 1) → Fin (2 * m + 1)) = grahamOrder m := rfl
  have hσ : (optimalMachine m ∘ π.symm) ∘ π = optimalMachine m := by
    funext j
    simp
  refine ⟨optimalMachine m ∘ π.symm, ?_, ?_⟩
  · rw [← hπ, hσ, hπ]
    exact ol_isListSchedule m
  · rw [← makespan_comp_internal (grahamJobs m) (optimalMachine m ∘ π.symm) π, hσ, hπ]
    exact ol_makespan m

end GrahamLPT
