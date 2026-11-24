/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import LeanPool.ShellsortMean.OrdinaryWordComparisons

/-! A slot-indexed execution of ordinary Shellsort, instrumented for key comparisons.
One vector caches the actual insertion result for each chain. Both the next
array and the pass counter are read from these results. The executable accepts
any linearly ordered keys; the specification theorem uses distinct ranks. -/
@[expose] public section

namespace Shellsort.HarvestOperationalAudit
open HarvestBlockIteration

/-- Extract the slots of one residue chain in increasing physical position. -/
def physicalChain {α : Type} {n : ℕ} (a : Vector α n)
    (h : {k : ℕ // 0 < k}) (s : Fin h.val) : List α :=
  List.ofFn fun v : Fin (sourceTrialLength (n / h.val) (n % h.val) s.val) =>
    a[s.val + h.val * v.val]'(actual_chain_prefix_lt n h.val h.property s v)

theorem physicalChain_map {α β : Type} {n : ℕ} (a : Vector α n) (f : α → β)
    (h : {k : ℕ // 0 < k}) (s : Fin h.val) :
    (physicalChain a h s).map f = physicalChain (a.map f) h s := by
  simp [physicalChain, List.map_ofFn, Function.comp_def]

/-- Reassemble the sorted residue chains in physical slot order. -/
def assembleChains {α : Type} {n : ℕ} (a : Vector α n) (gap : {k : ℕ // 0 < k})
    (rows : Fin gap.val → List α) : Vector α n :=
  Vector.ofFn fun i : Fin n =>
    let s : Fin gap.val := ⟨i.val % gap.val, Nat.mod_lt _ gap.property⟩
    (rows s)[i.val / gap.val]?.getD a[i.val]

/-- Reassembly commutes with mapping each key and each sorted chain. -/
theorem assembleChains_map {α β : Type} {n : ℕ} (a : Vector α n) (f : α → β)
    (gap : {k : ℕ // 0 < k}) (rows : Fin gap.val → List α) :
    (assembleChains a gap rows).map f = assembleChains (a.map f) gap (fun s => (rows s).map f) := by
  apply Vector.ext
  intro i hi
  simp only [assembleChains, Vector.getElem_ofFn, Vector.getElem_map, List.getElem?_map,
    Option.getD_map]

/-- Sort each gap chain and return the reassembled array and executed comparison count. -/
def runPass {α : Type} [LinearOrder α] {n : ℕ} (a : Vector α n)
    (gap : {k : ℕ // 0 < k}) : Vector α n × ℕ :=
  let k := gap.val
  let chains := Vector.ofFn fun s : Fin k => insertionComparedExecution (physicalChain a gap s)
  let output := assembleChains a gap (fun s => chains[s.val].output)
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
  have chain (s : Fin k) : insertionComparedExecution (physicalChain (slots p) ⟨k, hk⟩ s) =
      exec s := by
    simp only [physicalChain, slots, Vector.getElem_ofFn]
    rfl
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    simp only [runPass, assembleChains, Vector.getElem_ofFn]
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

end Shellsort.HarvestOperationalAudit
