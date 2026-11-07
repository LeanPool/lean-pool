/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HierarchyNonparallelBaseTransport
public import LeanPool.GoldbergSeymour.NonparallelHierarchyCorrespondence

/-!
# Transporting a full hierarchy base

Shared from the credited Trellis stable-change proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. Corresponding terminal metadata supplies
all dependent casts; only a parallel final extension needs the hierarchy splitter.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A full recolored route transports all hierarchy stages and the actual closure. -/
theorem TashkinovHierarchy.fullTransport {V E : Type*} [Fintype V] [Fintype E]
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
      MaximumProperty corr.replacementETT ∧
        ∃ (transported : HierarchyBase corr.replacementETT sigma)
          (replacement : TashkinovHierarchy corr.replacementETT transported),
          SameHierarchyStages hierarchy replacement ∧ transported.closure = base.closure := by
  classical
  by_cases parallel : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE
  · have built : TashkinovAugmentationSequence sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) T := by
      rcases route with ⟨_, built⟩ | ⟨kind, _⟩
      · exact built
      · rcases kind with kind | kind <;> rw [parallel] at kind <;> cases kind
    obtain ⟨corr, maximal, transported, replacement, stages⟩ :=
      HierarchySplitter G k e0 input T phi sigma ett maximum
        (by have := ett.roundsPositive; omega) induction base hierarchy parallel
        proper one sigmaProper sigmaOne (combined parallel) built
    exact ⟨corr, maximal, transported, replacement, stages,
      (stages.2.2.2.2.2 parallel).symm⟩
  · obtain ⟨corr⟩ := modified.2.2 T ett.abovePenultimate ett.strictAbovePenultimate route
    exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma modified T corr maximum,
      base.ofNonparallelCorresponding corr parallel,
      hierarchy.ofNonparallelCorresponding corr parallel,
      hierarchy.sameStagesOfNonparallelCorresponding corr parallel, rfl⟩

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
  obtain ⟨corr, maximal, transported, _, same, closure⟩ :=
    TashkinovHierarchy.fullTransport base maximum induction hierarchy proper one sigma
      sigmaProper sigmaOne modified combined route
  exact ⟨corr, maximal, transported, same.1.symm, closure⟩

/-- Fixed incident colors and missing colors on an initial segment supply full hierarchy
transport. -/
theorem TashkinovHierarchy.transportOfFixedPrefix {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input phi : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (hierarchy : TashkinovHierarchy ett base)
    (maximum : MaximumProperty ett) (induction : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (proper : IsProperEdgeColoring G phi) (one : IsOneEdgeUncolored phi e0)
    (sigma : PartialEdgeColoring E k) (sigmaProper : IsProperEdgeColoring G sigma)
    (sigmaOne : IsOneEdgeUncolored sigma e0)
    (stable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma)
    (initialSegment : TreeSequence G e0)
    (incidentFixed : ∀ edge, TreeIncidentEdge initialSegment edge → sigma edge = phi edge)
    (missingFixed : ∀ vertex ∈ TreeSequenceVertexSet initialSegment,
      MissingColors G sigma vertex = MissingColors G phi vertex)
    (closureInside : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
      TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet initialSegment)
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
      MaximumProperty corr.replacementETT ∧
        ∃ (transported : HierarchyBase corr.replacementETT sigma)
          (replacement : TashkinovHierarchy corr.replacementETT transported),
          SameHierarchyStages hierarchy replacement := by
  have modified := Td G k e0 input T phi ett maximum ett.roundsPositive induction sigma
    sigmaProper sigmaOne stable
  have combined (parallel : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) :
      CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← ett.generatingColoring] using stable
    · intro edge incident _
      obtain ⟨vertex, member, incident⟩ := incident
      exact incidentFixed edge ⟨vertex, closureInside parallel member, incident⟩
    · intro vertex member
      exact missingFixed vertex (closureInside parallel member)
  obtain ⟨corr, maximal, transported, replacement, same, _⟩ :=
    TashkinovHierarchy.fullTransport base maximum induction hierarchy proper one sigma
      sigmaProper sigmaOne modified combined route
  exact ⟨corr, maximal, transported, replacement, same⟩

end GoldbergSeymour

end
