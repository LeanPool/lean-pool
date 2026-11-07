/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.TreeColoringInvariant
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree

/-!
# P2752_T2_Prefix Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Corresponding hierarchy and stable-coloring data for the penultimate-prefix reduction. -/
structure HierarchyPrefixData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi} {base : HierarchyBase ett phi}
    (C : HierarchyCounterexample base) (Bplus : TreeSequence G e0)
    (sigma : PartialEdgeColoring E k) where
  belowFull : TreeSequenceInitialSegment Bplus T
  penultimateLength : T.length = Bplus.length + 1
  ladderBelow :
    TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Bplus
  /-- The extended tree restricted to the original prefix. -/
  oldETT : ExtendedTashkinovTree G k e0 input Bplus phi
  oldMaximum : MaximumProperty oldETT
  oldRung : oldETT.rounds = ett.rounds
  oldSeries : HEq oldETT.series ett.series
  /-- The hierarchy base for the original prefix. -/
  oldBase : HierarchyBase oldETT phi
  oldCore : oldBase.core = base.core
  oldClosure : oldBase.closure = base.closure
  oldSupport : oldBase.supportPosition.val = base.supportPosition.val
  /-- The original prefix hierarchy. -/
  oldHierarchy : TashkinovHierarchy oldETT oldBase
  oldCount : oldHierarchy.dividerCount = C.hierarchy.dividerCount
  oldStages :
    ∀ j : Fin (oldHierarchy.dividerCount + 1),
      let jo := Fin.cast (congrArg (fun n : ℕ => n + 1) oldCount) j
      oldHierarchy.stage j.castSucc = C.hierarchy.stage jo.castSucc ∧
        HierarchyStarredStage oldHierarchy j = HierarchyStarredStage C.hierarchy jo
  oldDividers :
    ∀ i : Fin oldHierarchy.dividerCount,
      (oldHierarchy.dividerPosition i).val = (C.hierarchy.dividerPosition (Fin.cast oldCount i)).val
  /-- The good-hierarchy witnesses for the original prefix. -/
  oldGood : GoodHierarchy oldHierarchy
  oldColors :
    ∀ j : Fin (oldHierarchy.dividerCount + 1),
      let jo := Fin.cast (congrArg (fun n : ℕ => n + 1) oldCount) j
      HierarchyStoredColorsAt oldHierarchy j = HierarchyStoredColorsAt C.hierarchy jo ∧
        HierarchyStageMissingColors oldHierarchy j = HierarchyStageMissingColors C.hierarchy jo ∧
          ∀ eta : Fin k,
            oldGood.gamma j eta = C.good.gamma jo eta ∧
              HierarchySegmentColors oldHierarchy j eta ⊆ HierarchySegmentColors C.hierarchy jo eta
  proper : IsProperEdgeColoring G sigma
  oneUncolored : IsOneEdgeUncolored sigma e0
  invariant : TreeColoringInvariant Bplus phi sigma
  incidentFixed : ∀ f : E, TreeIncidentEdge Bplus f → sigma f = phi f
  /-- The replacement extended tree with its ladder and coloring agreement certificates. -/
  corresponding : CorrespondingExtendedTashkinovTree G k e0 oldETT sigma Bplus
  maximum : MaximumProperty corresponding.replacementETT
  /-- The hierarchy base after replacement. -/
  newBase : HierarchyBase corresponding.replacementETT sigma
  /-- The hierarchy after replacement. -/
  newHierarchy : TashkinovHierarchy corresponding.replacementETT newBase
  /-- The good-hierarchy witnesses after replacement. -/
  newGood : GoodHierarchy newHierarchy
  sameGood : SameGoodHierarchy oldGood newGood

end GoldbergSeymour

end
