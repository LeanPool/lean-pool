/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestFullSchedule

/-! A slot-indexed execution of ordinary Shellsort, instrumented for key comparisons.
One vector caches the actual insertion result for each chain. Both the next
array and the pass counter are read from these results. The executable accepts
any linearly ordered keys; the specification theorem uses distinct ranks. -/
@[expose] public section

namespace Shellsort.HarvestOperationalAudit
open HarvestBlockIteration

/-- Sort each gap chain and return the reassembled array and executed comparison count. -/
def runPass {α : Type} [LinearOrder α] {n : ℕ} (a : Vector α n)
    (gap : {k : ℕ // 0 < k}) : Vector α n × ℕ :=
  let k := gap.val
  let chains := Vector.ofFn fun s : Fin k =>
    insertionComparedExecution (List.ofFn fun v : Fin (sourceTrialLength (n / k) (n % k) s.val) =>
      a[s.val + k * v.val]'(actual_chain_prefix_lt n k gap.property s v))
  let output := Vector.ofFn fun i : Fin n =>
    let s : Fin k := ⟨i.val % k, Nat.mod_lt _ gap.property⟩
    (chains[s.val].output[i.val / k]?).getD a[i.val]
  (output, (List.ofFn fun s : Fin k => chains[s.val].comparisons).sum)

/-- Execute the gap word and accumulate the number of key comparisons. -/
def runWord {α : Type} [LinearOrder α] {n : ℕ} (a : Vector α n) :
    PositiveWord → Vector α n × ℕ
  | [] => (a, 0)
  | h :: t =>
    let first := runPass a h
    let tail := runWord first.1 t
    (tail.1, first.2 + tail.2)

/-- Read the placement in physical slot order. Used only in the specification. -/
def slots {n : ℕ} (p : RankPlacement n) : Vector (Fin n) n :=
  Vector.ofFn fun i => p.symm i

theorem runPass_slots {n : ℕ} (p : RankPlacement n) (h : {k : ℕ // 0 < k}) :
    runPass (slots p) h = (slots (gapSort p h.val), gapComparisonCost p h.val h.property) := by
  rcases h with ⟨k, hk⟩
  let exec := fun s : Fin k => insertionComparedExecution (List.ofFn (chainKeys p k hk s))
  have chain (s : Fin k) : insertionComparedExecution
      (List.ofFn fun v : Fin (sourceTrialLength (n / k) (n % k) s.val) =>
        (slots p)[s.val + k * v.val]'(actual_chain_prefix_lt n k hk s v)) = exec s := by
    simp only [slots, Vector.getElem_ofFn]
    rfl
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    simp only [runPass, Vector.getElem_ofFn]
    rw [chain ⟨i % k, Nat.mod_lt _ hk⟩]
    let coord := positionChainEquiv n k hk (⟨i, hi⟩ : Fin n)
    change ((exec coord.1).output[coord.2.val]?).getD _ = _
    rw [show (exec coord.1).output = _ from gapCompared_chain_eq_gapSort p k hk coord.1]
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using coord.2.isLt)]
    simp only [List.getElem_ofFn, Option.getD_some]
    change (gapSort p k).symm ((positionChainEquiv n k hk).symm coord) = _
    rw [Equiv.symm_apply_apply]
    simp [slots]
  · simp only [runPass, Vector.getElem_ofFn]
    simp_rw [chain]
    rw [List.sum_ofFn]
    rfl

theorem runWord_slots {n : ℕ} (p : RankPlacement n) (w : PositiveWord) :
    runWord (slots p) w =
      (slots (sortWord p (w.map Subtype.val)), ordinaryWordComparisons p w) := by
  induction w generalizing p with
  | nil => rfl
  | cons h t ih =>
    simp only [runWord, runPass_slots, ih, List.map_cons, sortWord, ordinaryWordComparisons]

theorem exists_executed_family :
    ∃ W : ℕ → PositiveWord, ∀ n : ℕ, 2 ≤ n →
      ((W n).map Subtype.val).Pairwise (· > ·) ∧
      (∀ h ∈ W n, h.val < n) ∧ ((W n).map Subtype.val).getLast? = some 1 ∧
      (W n).length ≤ Nat.log 2 n ∧
      (∀ p : RankPlacement n, (runWord (slots p) (W n)).1 = Vector.ofFn id) ∧
      uniformAverage (fun p : RankPlacement n => ((runWord (slots p) (W n)).2 : ℝ)) ≤
        (1 + (2 : ℝ) ^ 165) * (n : ℝ) * Real.logb 2 n := by
  obtain ⟨W, spec⟩ := HarvestFullSchedule.exists_size_indexed_family
  refine ⟨W, fun n hn => ?_⟩
  obtain ⟨order, cap, last, sorted, count, cost⟩ := spec n hn
  refine ⟨order, cap, last, count, fun p => ?_, ?_⟩
  · rw [runWord_slots, sorted]; rfl
  · simpa only [runWord_slots] using cost

end Shellsort.HarvestOperationalAudit
