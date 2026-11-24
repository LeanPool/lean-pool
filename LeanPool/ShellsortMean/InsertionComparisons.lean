/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.InsertionOperations

/-!
The same linear insertion execution, now instrumented with key comparisons.
Every test against a nonempty predecessor counts once. Empty-prefix checks,
index arithmetic, allocation, record writes and final key placement are not
key comparisons. This is a counter model, not machine running time.
-/
@[expose] public section

namespace Shellsort

/-- The output of a comparison-counting insertion operation and its two cost counters. -/
structure ComparedInsertion (α : Type*) where
  /-- The output in the orientation of the insertion routine. -/
  output : List α
  /-- The number of existing keys shifted past the inserted key. -/
  shifts : ℕ
  /-- The number of executed key comparisons, including a stopping comparison when present. -/
  comparisons : ℕ
  deriving Repr

/-- Insert one key into a reversed sorted chain and record its shifts and comparisons. -/
def insertCompared {α : Type*} [LinearOrder α] (a : α) : List α → ComparedInsertion α
  | [] => ⟨[a], 0, 0⟩
  | b :: l =>
    if a < b then
      let next := insertCompared a l
      ⟨b :: next.output, next.shifts + 1, next.comparisons + 1⟩
    else ⟨a :: b :: l, 0, 1⟩

theorem insertCompared_projection {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    ((insertCompared a l).output, (insertCompared a l).shifts) = insertFromRight a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have ho := congrArg Prod.fst ih
    have hs := congrArg Prod.snd ih
    simp only at ho hs
    by_cases hab : a < b <;> simp [insertCompared, insertFromRight, hab, ho, hs]

theorem insertCompared_output {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (insertCompared a l).output = (insertFromRight a l).1 :=
  congrArg Prod.fst (insertCompared_projection a l)

theorem insertCompared_shifts {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (insertCompared a l).shifts = (insertFromRight a l).2 :=
  congrArg Prod.snd (insertCompared_projection a l)

/-- There is at most one final unsuccessful key comparison in a single insertion. -/
theorem insertCompared_bounds {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (insertCompared a l).shifts ≤ (insertCompared a l).comparisons ∧
      (insertCompared a l).comparisons ≤ (insertCompared a l).shifts + 1 := by
  induction l with
  | nil => simp [insertCompared]
  | cons b l ih =>
    by_cases hab : a < b
    · simp only [insertCompared, hab, ite_true]
      omega
    · simp [insertCompared, hab]

/-- Insertion sort with an internal reversed output and accumulated cost counters. -/
def insertionComparedBack {α : Type*} [LinearOrder α] : List α → ComparedInsertion α :=
  List.reverseRec ⟨[], 0, 0⟩ (fun _ a previous =>
    let step := insertCompared a previous.output
    ⟨step.output, previous.shifts + step.shifts, previous.comparisons + step.comparisons⟩)

theorem insertionComparedBack_nil {α : Type*} [LinearOrder α] :
    insertionComparedBack ([] : List α) = ⟨[], 0, 0⟩ := by simp [insertionComparedBack]

theorem insertionComparedBack_append {α : Type*} [LinearOrder α] (l : List α) (a : α) :
    insertionComparedBack (l ++ [a]) =
      ⟨(insertCompared a (insertionComparedBack l).output).output,
        (insertionComparedBack l).shifts + (insertCompared a (insertionComparedBack
          l).output).shifts,
        (insertionComparedBack l).comparisons +
          (insertCompared a (insertionComparedBack l).output).comparisons⟩ := by
  simp [insertionComparedBack]

theorem insertionComparedBack_projection {α : Type*} [LinearOrder α] (l : List α) :
    ((insertionComparedBack l).output, (insertionComparedBack l).shifts) = insertionBack l := by
  induction l using List.reverseRecOn with
  | nil => simp [insertionComparedBack_nil, insertionBack_nil]
  | append_singleton l a ih =>
    have ho := congrArg Prod.fst ih
    have hs := congrArg Prod.snd ih
    simp only at ho hs
    rw [insertionComparedBack_append, insertionBack_append_singleton]
    simp only [ho, hs, insertCompared_output, insertCompared_shifts]

/-- The first key of a nonempty chain requires no key comparison. -/
theorem insertionComparedBack_bounds {α : Type*} [LinearOrder α] (l : List α) :
    (insertionComparedBack l).shifts ≤ (insertionComparedBack l).comparisons ∧
      (insertionComparedBack l).comparisons ≤
        (insertionComparedBack l).shifts + (l.length - 1) := by
  induction l using List.reverseRecOn with
  | nil => simp [insertionComparedBack_nil]
  | append_singleton l a ih =>
    by_cases hl : l = []
    · subst l
      rw [insertionComparedBack_append [] a]
      simp [insertionComparedBack_nil, insertCompared]
    · have hlen : 0 < l.length := List.length_pos_iff.mpr hl
      have hb := insertCompared_bounds a (insertionComparedBack l).output
      simp only [insertionComparedBack_append, List.length_append, List.length_singleton]
      omega

/-- Insertion sort returning ascending output with the original cost counters. -/
def insertionComparedExecution {α : Type*} [LinearOrder α] (l : List α) : ComparedInsertion α :=
  let result := insertionComparedBack l
  ⟨result.output.reverse, result.shifts, result.comparisons⟩

/-- Instrumentation preserves both the original output and the entire shift count. -/
theorem insertionComparedExecution_projection {α : Type*} [LinearOrder α] (l : List α) :
    ((insertionComparedExecution l).output, (insertionComparedExecution l).shifts) =
      insertionExecution l := by
  have hp := insertionComparedBack_projection l
  have ho := congrArg Prod.fst hp
  have hs := congrArg Prod.snd hp
  simp only at ho hs
  simp only [insertionComparedExecution, insertionExecution, ho, hs]

theorem insertionComparedExecution_output {α : Type*} [LinearOrder α] (l : List α) :
    (insertionComparedExecution l).output = (insertionExecution l).1 :=
  congrArg Prod.fst (insertionComparedExecution_projection l)

theorem insertionComparedExecution_shifts {α : Type*} [LinearOrder α] (l : List α) :
    (insertionComparedExecution l).shifts = (insertionExecution l).2 :=
  congrArg Prod.snd (insertionComparedExecution_projection l)

/-- True all-input linear-search comparison sandwich, including the empty chain. -/
theorem insertionComparedExecution_bounds {α : Type*} [LinearOrder α] (l : List α) :
    (insertionExecution l).2 ≤ (insertionComparedExecution l).comparisons ∧
      (insertionComparedExecution l).comparisons ≤ (insertionExecution l).2 + (l.length - 1) := by
  have hb := insertionComparedBack_bounds l
  have hs := insertionComparedExecution_shifts l
  change (insertionComparedBack l).shifts = (insertionExecution l).2 at hs
  simpa only [insertionComparedExecution, hs] using hb

end Shellsort
