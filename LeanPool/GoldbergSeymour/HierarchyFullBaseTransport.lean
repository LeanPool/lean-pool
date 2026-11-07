/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData

/-!
# Transporting a full hierarchy base

Shared from the credited Trellis stable-change proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. Corresponding terminal metadata supplies
all dependent casts; only a parallel final extension needs the hierarchy splitter.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A corresponding nonparallel tree preserves the core, closure and support position. -/
def HierarchyBase.ofNonparallelCorresponding {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi sigma : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} (base : HierarchyBase ett phi)
    {U : TreeSequence G e0} (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (nonparallel : ett.series.data.kind (Fin.last ett.rounds) ≠ some TashkinovExtensionKind.PE) :
    HierarchyBase corr.replacementETT sigma := by
  have terminal := CorrespondingExtendedTashkinovTree.terminalTreeKind G k e0 sigma ett U corr
  let position : Fin ((corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc).length + 1) :=
    Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1) terminal.1.symm)
      base.supportPosition
  exact {
    core := base.core
    closure := base.closure
    supportPosition := position
    supportPositive := by simpa only [position, Fin.val_cast] using base.supportPositive
    terminalMissingColors := rfl
    parallel := fun kind => (nonparallel (terminal.2.symm.trans kind)).elim
    nonparallel := fun _ => (base.nonparallel nonparallel).trans terminal.1.symm }

/-- A full recolored route transports the hierarchy base, splitting only at a parallel end. -/
theorem HierarchyBase.fullTransport {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} (base : HierarchyBase ett phi)
    (maximum : MaximumProperty ett) (induction : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hierarchy : TashkinovHierarchy ett base) (proper : IsProperEdgeColoring G phi)
    (one : IsOneEdgeUncolored phi e0) (sigma : PartialEdgeColoring E k)
    (sigmaProper : IsProperEdgeColoring G sigma) (sigmaOne : IsOneEdgeUncolored sigma e0)
    (modified : ModColoring ett sigma)
    (combined : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
      CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma)
    (route :
      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) T) ∨
      ((ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
          TashkinovAugmentationSequence sigma seed T)) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
      MaximumProperty corr.replacementETT ∧ ∃ transported : HierarchyBase corr.replacementETT sigma,
        transported.core = base.core ∧ transported.closure = base.closure := by
  classical
  by_cases parallel : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE
  · have built : TashkinovAugmentationSequence sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) T := by
      rcases route with ⟨_, built⟩ | ⟨kind, _⟩
      · exact built
      · rcases kind with kind | kind <;> rw [parallel] at kind <;> cases kind
    obtain ⟨corr, maximal, transported, _, stages⟩ :=
      HierarchySplitter G k e0 input T phi sigma ett maximum
        (by have := ett.roundsPositive; omega) induction base hierarchy parallel
        proper one sigmaProper sigmaOne (combined parallel) built
    exact ⟨corr, maximal, transported, stages.1.symm, (stages.2.2.2.2.2 parallel).symm⟩
  · obtain ⟨corr⟩ := modified.2.2 T ett.abovePenultimate ett.strictAbovePenultimate route
    exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma modified T corr maximum,
      base.ofNonparallelCorresponding corr parallel, rfl, rfl⟩

end GoldbergSeymour

end
