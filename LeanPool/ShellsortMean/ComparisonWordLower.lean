/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ComparisonWordTree
public import LeanPool.ShellsortMean.ComparisonTreeSeparation

/-! A completed sort identifies the original slot of each distinct rank.
Together with the literal comparison trace this gives a lower bound for any
positive gap word with last gap one, irrespective of its length or scale. -/
@[expose] public section

namespace Shellsort.ComparisonAudit
open HarvestBlockIteration HarvestOperationalAudit

theorem sorted_last {n : ℕ} (p : RankPlacement n) (w : List ℕ)
    (hlast : w.getLast? = some 1) : sortWord p w = Equiv.refl _ := by
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  clear hlast
  induction pre generalizing p with
  | nil => exact gapSort_one p
  | cons a as ih => exact ih (gapSort p a)

/-- Reading a sorted leaf at index i recovers the original slot p(i). -/
private theorem label_at {n : ℕ} (p : RankPlacement n) (a : Vector (Fin n) n)
    (h : a.map p.symm = slots (Equiv.refl _)) (i : Fin n) : a[i.val] = p i := by
  have v := congrArg (fun b : Vector (Fin n) n => b[i.val]) h
  apply p.symm.injective
  simpa [slots] using v

theorem word_mean_lower {n : ℕ} (w : PositiveWord)
    (hlast : (w.map Subtype.val).getLast? = some 1) :
    Real.logb 2 (n.factorial : ℝ) ≤
      uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons p w : ℝ)) := by
  let t := wordTree (Vector.ofFn (id : Fin n → Fin n)) w
  have recover (p : RankPlacement n) (i : Fin n) : (t.run p).1[i.val] = p i := by
    apply label_at
    have out := (initial_wordTree w p).1
    rw [runWord_slots, sorted_last p _ hlast] at out
    exact out
  apply tree_uniform_lower t
  · intro p q eq
    apply Equiv.ext
    intro i
    exact (recover p i).symm.trans ((congrArg (fun a : Vector (Fin n) n => a[i.val]) eq).trans
      (recover q i))
  · intro p
    exact (initial_wordTree w p).2.le

end Shellsort.ComparisonAudit
