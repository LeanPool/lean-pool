/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Induction

/-!
A finite insertion execution, counting successful right shifts. The sorted
physical prefix is represented backwards, so its head is the predecessor of
the current hole. Each successful comparison key < predecessor moves that
predecessor one slot right and adds exactly one to the counter. The counter
does not include extracting the key or its final placement.

The inversion statistic below is defined separately from this execution.
-/
@[expose] public section

namespace Shellsort

/-- The number of entries strictly larger than the specified key. -/
def largerCount {α : Type*} [LinearOrder α] (a : α) (l : List α) : ℕ :=
  (l.filter (fun b => a < b)).length

/-- The number of entries strictly smaller than the specified key. -/
def smallerCount {α : Type*} [LinearOrder α] (a : α) (l : List α) : ℕ :=
  (l.filter (fun b => b < a)).length

/-- Pair count by the left endpoint of an inversion, independently of an algorithm. -/
def listInversions {α : Type*} [LinearOrder α] : List α → ℕ
  | [] => 0
  | a :: l => smallerCount a l + listInversions l

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

/-- Insert at the physical right end of a sorted prefix represented backwards. -/
def insertFromRight {α : Type*} [LinearOrder α] (a : α) (l : List α) : List α × ℕ :=
  ((insertCompared a l).output, (insertCompared a l).shifts)

private theorem insertFromRight_cons {α : Type*} [LinearOrder α] (a b : α) (l : List α) :
    insertFromRight a (b :: l) =
      if a < b then (b :: (insertFromRight a l).1, (insertFromRight a l).2 + 1)
      else (a :: b :: l, 0) := by
  by_cases h : a < b <;> simp [insertFromRight, insertCompared, h]

theorem insertFromRight_perm {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (insertFromRight a l).1.Perm (a :: l) := by
  induction l with
  | nil => simp [insertFromRight, insertCompared]
  | cons b l ih =>
    by_cases hab : a < b
    · simp only [insertFromRight_cons, hab, ite_true]
      exact (ih.cons b).trans (List.Perm.swap a b l)
    · simp [insertFromRight_cons, hab]

theorem insertFromRight_sorted {α : Type*} [LinearOrder α] (a : α) (l : List α)
    (hl : l.Pairwise (fun x y => y ≤ x)) :
    (insertFromRight a l).1.Pairwise (fun x y => y ≤ x) := by
  induction l with
  | nil => simp [insertFromRight, insertCompared]
  | cons b l ih =>
    obtain ⟨hb, hl⟩ := List.pairwise_cons.mp hl
    by_cases hab : a < b
    · simp only [insertFromRight_cons, hab, ite_true]
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hl⟩
      intro y hy
      have hmem := (insertFromRight_perm a l).mem_iff.mp hy
      rcases List.mem_cons.mp hmem with rfl | hymem
      · exact le_of_lt hab
      · exact hb y hymem
    · simp only [insertFromRight_cons, hab, ite_false]
      apply List.pairwise_cons.mpr
      refine ⟨?_, List.pairwise_cons.mpr ⟨hb, hl⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hymem
      · exact le_of_not_gt hab
      · exact (hb y hymem).trans (le_of_not_gt hab)

theorem largerCount_perm {α : Type*} [LinearOrder α] (a : α) {l r : List α}
    (h : l.Perm r) : largerCount a l = largerCount a r :=
  (h.filter (fun b => a < b)).length_eq

/-- The branch counter equals the number of larger prefix keys, proved using
the sorted-prefix invariant; it is false on general unsorted prefixes. -/
theorem insertFromRight_count {α : Type*} [LinearOrder α] (a : α) (l : List α)
    (hl : l.Pairwise (fun x y => y ≤ x)) :
    (insertFromRight a l).2 = largerCount a l := by
  induction l with
  | nil => simp [insertFromRight, insertCompared, largerCount]
  | cons b l ih =>
    obtain ⟨hb, hl⟩ := List.pairwise_cons.mp hl
    by_cases hab : a < b
    · simp [insertFromRight_cons, hab, ih hl, largerCount, Nat.add_comm]
    · have hfilter : (b :: l).filter (fun x => a < x) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simp only [decide_eq_true_eq, not_lt]
        rcases List.mem_cons.mp hy with rfl | hymem
        · exact le_of_not_gt hab
        · exact (hb y hymem).trans (le_of_not_gt hab)
      simp [insertFromRight_cons, hab, largerCount, hfilter]

theorem listInversions_append_singleton {α : Type*} [LinearOrder α]
    (l : List α) (a : α) :
    listInversions (l ++ [a]) = listInversions l + largerCount a l := by
  induction l with
  | nil => simp [listInversions, smallerCount, largerCount]
  | cons b l ih =>
    by_cases hab : a < b <;>
      simp [listInversions, smallerCount, largerCount, List.filter_append, ih, hab] <;>
      omega

/-- Insertion sort with an internal reversed output and accumulated cost counters. -/
def insertionComparedBack {α : Type*} [LinearOrder α] : List α → ComparedInsertion α :=
  List.reverseRec ⟨[], 0, 0⟩ (fun _ a previous =>
    let step := insertCompared a previous.output
    ⟨step.output, previous.shifts + step.shifts, previous.comparisons + step.comparisons⟩)

/-- Process input keys in their original left-to-right order. The first output
is the sorted physical prefix represented backwards; the second is shifts. -/
def insertionBack {α : Type*} [LinearOrder α] (l : List α) : List α × ℕ :=
  ((insertionComparedBack l).output, (insertionComparedBack l).shifts)

theorem insertionBack_nil {α : Type*} [LinearOrder α] :
    insertionBack ([] : List α) = ([], 0) := by
  simp [insertionBack, insertionComparedBack]

theorem insertionBack_append_singleton {α : Type*} [LinearOrder α]
    (l : List α) (a : α) :
    insertionBack (l ++ [a]) =
      ((insertFromRight a (insertionBack l).1).1,
        (insertionBack l).2 + (insertFromRight a (insertionBack l).1).2) := by
  simp [insertionBack, insertionComparedBack, insertFromRight]

theorem insertionBack_perm {α : Type*} [LinearOrder α] (l : List α) :
    (insertionBack l).1.Perm l := by
  induction l using List.reverseRecOn with
  | nil => simp [insertionBack_nil]
  | append_singleton l a ih =>
    rw [insertionBack_append_singleton]
    exact ((insertFromRight_perm a _).trans (ih.cons a)).trans
      (List.perm_append_comm : ([a] ++ l).Perm (l ++ [a]))

theorem insertionBack_sorted {α : Type*} [LinearOrder α] (l : List α) :
    (insertionBack l).1.Pairwise (fun x y => y ≤ x) := by
  induction l using List.reverseRecOn with
  | nil => simp [insertionBack_nil]
  | append_singleton l a ih =>
    rw [insertionBack_append_singleton]
    exact insertFromRight_sorted a _ ih

/-- Exact equality between the independently defined execution counter and inversions. -/
theorem insertionBack_count {α : Type*} [LinearOrder α] (l : List α) :
    (insertionBack l).2 = listInversions l := by
  induction l using List.reverseRecOn with
  | nil => simp [insertionBack_nil, listInversions]
  | append_singleton l a ih =>
    rw [insertionBack_append_singleton]
    simp only [ih, insertFromRight_count a _ (insertionBack_sorted l),
      largerCount_perm a (insertionBack_perm l), listInversions_append_singleton]

/-- Return the physically ordered chain and its successful-right-shift count. -/
def insertionExecution {α : Type*} [LinearOrder α] (l : List α) : List α × ℕ :=
  ((insertionBack l).1.reverse, (insertionBack l).2)

theorem insertionExecution_perm {α : Type*} [LinearOrder α] (l : List α) :
    (insertionExecution l).1.Perm l :=
  (List.reverse_perm _).trans (insertionBack_perm l)

theorem insertionExecution_sorted {α : Type*} [LinearOrder α] (l : List α) :
    (insertionExecution l).1.Pairwise (fun x y => x ≤ y) := by
  exact (insertionBack_sorted l).reverse

theorem insertionExecution_count {α : Type*} [LinearOrder α] (l : List α) :
    (insertionExecution l).2 = listInversions l := insertionBack_count l

end Shellsort
