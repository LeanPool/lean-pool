/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import LeanPool.ShellsortMean.HarvestOperationalAudit

/-! Replacing ranks by any strictly order-preserving physical key values
commutes with a complete ordinary execution and preserves its key cost. -/
@[expose] public section

namespace Shellsort.HarvestOperationalAudit

private theorem relabel_insert {α β : Type} [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) (a : α) (l : List α) :
    (insertCompared (f a) (l.map f)).output = (insertCompared a l).output.map f ∧
    (insertCompared (f a) (l.map f)).comparisons = (insertCompared a l).comparisons := by
  induction l with
  | nil => simp [insertCompared]
  | cons b bs ih =>
    by_cases h : a < b <;> simp [insertCompared, h, ih.1, ih.2]

private theorem relabel_chain {α β : Type} [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) (l : List α) :
    (insertionComparedExecution (l.map f)).output = (insertionComparedExecution l).output.map f ∧
    (insertionComparedExecution (l.map f)).comparisons = (insertionComparedExecution
      l).comparisons := by
  have back (t : List α) :
      (insertionComparedBack (t.map f)).output = (insertionComparedBack t).output.map f ∧
      (insertionComparedBack (t.map f)).comparisons = (insertionComparedBack t).comparisons := by
    induction t using List.reverseRecOn with
    | nil => simp [insertionComparedBack_nil]
    | append_singleton t a ih =>
      have next := relabel_insert f a (insertionComparedBack t).output
      simp [insertionComparedBack_append, ih.1, ih.2, next.1, next.2]
  simp [insertionComparedExecution, (back l).1, (back l).2, List.map_reverse]

theorem relabel_pass {α β : Type} [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) {n : ℕ} (a : Vector α n) (h : {k : ℕ // 0 < k}) :
    runPass (a.map f) h = ((runPass a h).1.map f, (runPass a h).2) := by
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    let s : Fin h.val := ⟨i % h.val, Nat.mod_lt _ h.property⟩
    simp only [runPass, Vector.getElem_ofFn, Vector.getElem_map, ← physicalChain_map]
    rw [(relabel_chain f (physicalChain a h s)).1, List.getElem?_map, Option.getD_map]
  · simp only [runPass, Vector.getElem_ofFn, ← physicalChain_map]
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext s
    exact (relabel_chain f (physicalChain a h s)).2

theorem relabel_word {α β : Type} [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) {n : ℕ} (a : Vector α n) (w : HarvestBlockIteration.PositiveWord) :
    runWord (a.map f) w = ((runWord a w).1.map f, (runWord a w).2) := by
  induction w generalizing a with
  | nil => rfl
  | cons h t ih => simp only [runWord, relabel_pass, ih]

end Shellsort.HarvestOperationalAudit
