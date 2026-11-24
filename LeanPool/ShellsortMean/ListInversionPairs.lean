/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.InsertionOperations
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin

/-! List inversion counts as counts of ordered position pairs. -/

@[expose] public section

namespace Shellsort
open scoped BigOperators

theorem largerCount_ofFn {α : Type*} [LinearOrder α] (a : α)
    {L : ℕ} (f : Fin L → α) :
    largerCount a (List.ofFn f) = ∑ v : Fin L, if a < f v then 1 else 0 := by
  induction L with
  | zero => simp [largerCount]
  | succ L ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    have ih' := ih (fun i => f i.succ)
    unfold largerCount at ih'
    by_cases h : a < f 0 <;> simp [largerCount, h, ih', Nat.add_comm]

/-- The independently recursive inversion statistic is the actual index-pair count. -/
theorem listInversions_ofFn {α : Type*} [LinearOrder α] {L : ℕ} (f : Fin L → α) :
    listInversions (List.ofFn f) =
      ∑ j : Fin L, ∑ i : Fin L, if i < j ∧ f j < f i then 1 else 0 := by
  induction L with
  | zero => simp [listInversions]
  | succ L ih =>
    rw [List.ofFn_succ', List.concat_eq_append, listInversions_append_singleton,
      ih, largerCount_ofFn]
    have hlast (i : Fin L) : ¬ Fin.last L < i.castSucc :=
      not_lt_of_ge (le_of_lt (Fin.castSucc_lt_last i))
    simp only [Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff,
      Fin.castSucc_lt_last, hlast, lt_self_iff_false, false_and,
      true_and, ite_false, add_zero]

/-- Index-pair characterization of the executed successful-right-shift counter. -/
theorem insertionExecution_ofFn_count {α : Type*} [LinearOrder α]
    {L : ℕ} (f : Fin L → α) :
    (insertionExecution (List.ofFn f)).2 =
      ∑ j : Fin L, ∑ i : Fin L, if i < j ∧ f j < f i then 1 else 0 := by
  rw [insertionExecution_count, listInversions_ofFn]

end Shellsort
