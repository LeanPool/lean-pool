/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

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

def largerCount {α : Type*} [LinearOrder α] (a : α) (l : List α) : ℕ :=
  (l.filter (fun b => a < b)).length

def smallerCount {α : Type*} [LinearOrder α] (a : α) (l : List α) : ℕ :=
  (l.filter (fun b => b < a)).length

/-- Pair count by the left endpoint of an inversion, independently of an algorithm. -/
def listInversions {α : Type*} [LinearOrder α] : List α → ℕ
  | [] => 0
  | a :: l => smallerCount a l + listInversions l

/-- Insert at the physical right end of a sorted prefix represented backwards. -/
def insertFromRight {α : Type*} [LinearOrder α] (a : α) : List α → List α × ℕ
  | [] => ([a], 0)
  | b :: l =>
    if a < b then
      let next := insertFromRight a l
      (b :: next.1, next.2 + 1)
    else (a :: b :: l, 0)

theorem insertFromRight_perm {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (insertFromRight a l).1.Perm (a :: l) := by
  induction l with
  | nil => simp [insertFromRight]
  | cons b l ih =>
    by_cases hab : a < b
    · simp only [insertFromRight, hab, ite_true]
      exact (ih.cons b).trans (List.Perm.swap a b l)
    · simp [insertFromRight, hab]

theorem insertFromRight_sorted {α : Type*} [LinearOrder α] (a : α) (l : List α)
    (hl : l.Pairwise (fun x y => y ≤ x)) :
    (insertFromRight a l).1.Pairwise (fun x y => y ≤ x) := by
  induction l with
  | nil => simp [insertFromRight]
  | cons b l ih =>
    obtain ⟨hb, hl⟩ := List.pairwise_cons.mp hl
    by_cases hab : a < b
    · simp only [insertFromRight, hab, ite_true]
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hl⟩
      intro y hy
      have hmem := (insertFromRight_perm a l).mem_iff.mp hy
      rcases List.mem_cons.mp hmem with rfl | hymem
      · exact le_of_lt hab
      · exact hb y hymem
    · simp only [insertFromRight, hab, ite_false]
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
  | nil => simp [insertFromRight, largerCount]
  | cons b l ih =>
    obtain ⟨hb, hl⟩ := List.pairwise_cons.mp hl
    by_cases hab : a < b
    · simp [insertFromRight, hab, ih hl, largerCount, Nat.add_comm]
    · have hfilter : (b :: l).filter (fun x => a < x) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simp only [decide_eq_true_eq, not_lt]
        rcases List.mem_cons.mp hy with rfl | hymem
        · exact le_of_not_gt hab
        · exact (hb y hymem).trans (le_of_not_gt hab)
      simp [insertFromRight, hab, largerCount, hfilter]

theorem listInversions_append_singleton {α : Type*} [LinearOrder α]
    (l : List α) (a : α) :
    listInversions (l ++ [a]) = listInversions l + largerCount a l := by
  induction l with
  | nil => simp [listInversions, smallerCount, largerCount]
  | cons b l ih =>
    by_cases hab : a < b <;>
      simp [listInversions, smallerCount, largerCount, List.filter_append, ih, hab] <;>
      omega

/-- Process input keys in their original left-to-right order. The first output
is the sorted physical prefix represented backwards; the second is shifts. -/
def insertionBack {α : Type*} [LinearOrder α] : List α → List α × ℕ :=
  List.reverseRec ([], 0) (fun _ a previous =>
    let step := insertFromRight a previous.1
    (step.1, previous.2 + step.2))

theorem insertionBack_nil {α : Type*} [LinearOrder α] :
    insertionBack ([] : List α) = ([], 0) := by
  simp [insertionBack]

theorem insertionBack_append_singleton {α : Type*} [LinearOrder α]
    (l : List α) (a : α) :
    insertionBack (l ++ [a]) =
      ((insertFromRight a (insertionBack l).1).1,
        (insertionBack l).2 + (insertFromRight a (insertionBack l).1).2) := by
  simp [insertionBack]

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
