/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseRestorationTrace

/-!
# Extension Base Algorithm ATrace Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseAlgorithmATraceExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (sigmaN : PartialEdgeColoring E k)
    (hslotData : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      ∃ vt : V, ∃ gammaT deltaT : Fin k,
        ett.series.data.chosenVertex t.succ = some vt ∧
          ett.series.data.gamma t.succ = some gammaT ∧
          ett.series.data.delta t.succ = some deltaT) :
    Nonempty (ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN) := by
  classical
  let slots := ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport
  let ordered : List (Fin ett.rounds) :=
    List.insertionSort (fun a b : Fin ett.rounds => b.val ≤ a.val) slots.toList
  have orderedPerm : List.Perm ordered slots.toList := by
    exact List.perm_insertionSort _ _
  have orderedLength : slots.card = ordered.length := by
    exact (orderedPerm.length_eq.trans (Finset.length_toList slots)).symm
  have orderedPairwise : ordered.Pairwise (fun a b : Fin ett.rounds => b.val ≤ a.val) := by
    exact List.pairwise_insertionSort _ _
  have orderedNodup : ordered.Nodup := by
    exact orderedPerm.nodup_iff.mpr (Finset.nodup_toList slots)
  let slot : Fin slots.card → Fin ett.rounds := fun a =>
    ordered.get (Fin.cast orderedLength a)
  have slotMem : ∀ a : Fin slots.card, slot a ∈ slots := by
    intro a
    rw [show slot a = ordered.get (Fin.cast orderedLength a) by rfl]
    apply (Finset.mem_toList).mp
    exact orderedPerm.mem_iff.mp (List.get_mem ordered (Fin.cast orderedLength a))
  have slotAll : Finset.univ.image slot = slots := by
    ext t
    constructor
    · intro ht
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp ht
      simpa [← ha] using slotMem a
    · intro ht
      have hlist : t ∈ ordered := orderedPerm.mem_iff.mpr (Finset.mem_toList.mpr ht)
      obtain ⟨a, ha⟩ := (List.mem_iff_get.mp hlist)
      let a' : Fin slots.card := Fin.cast orderedLength.symm a
      refine Finset.mem_image.mpr ⟨a', Finset.mem_univ _, ?_⟩
      simpa [slot, a', Fin.cast_cast] using ha
  have slotDescending : ∀ a b : Fin slots.card, a.val < b.val →
      (slot b).val < (slot a).val := by
    intro a b hab
    have hp := orderedPairwise.rel_get_of_lt
      (show (Fin.cast orderedLength a) < (Fin.cast orderedLength b) by exact hab)
    have hne : ordered.get (Fin.cast orderedLength a) ≠ ordered.get (Fin.cast orderedLength b) := by
      intro he
      have hi := orderedNodup.get_inj_iff.mp he
      exact (ne_of_lt (show (Fin.cast orderedLength a).val <
          (Fin.cast orderedLength b).val by exact hab)) (congrArg Fin.val hi)
    have hlt : (ordered.get (Fin.cast orderedLength b)).val <
        (ordered.get (Fin.cast orderedLength a)).val := by
      exact lt_of_le_of_ne hp (fun h => hne (Fin.ext h.symm))
    exact hlt
  let support : Fin slots.card → V := fun a =>
    Classical.choose (hslotData (slot a) (slotMem a))
  let gamma : Fin slots.card → Fin k := fun a =>
    Classical.choose (Classical.choose_spec (hslotData (slot a) (slotMem a)))
  let delta : Fin slots.card → Fin k := fun a =>
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec (hslotData (slot a) (slotMem a))))
  have chosenData : ∀ a : Fin slots.card,
      ett.series.data.chosenVertex (slot a).succ = some (support a) ∧
        ett.series.data.gamma (slot a).succ = some (gamma a) ∧
        ett.series.data.delta (slot a).succ = some (delta a) := by
    intro a
    exact Classical.choose_spec (hslotData (slot a) (slotMem a)) |>.choose_spec |>.choose_spec
  let coloring : Fin (slots.card + 1) → PartialEdgeColoring E k := fun i =>
    Fin.induction sigmaN (fun j state =>
      TwoColorComponentSwap G state (gamma j) (delta j) (Sum.inl (support j))) i
  refine ⟨{
    steps := slots.card
    slot := slot
    support := support
    gamma := gamma
    delta := delta
    coloring := coloring
    initialColoring := by rfl
    enumerates := slotAll
    strictlyDescending := slotDescending
    chosenVertex := fun a => (chosenData a).1
    gammaField := fun a => (chosenData a).2.1
    deltaField := fun a => (chosenData a).2.2
    transition := ?_ }⟩
  intro a
  simp [coloring]

end GoldbergSeymour

end
