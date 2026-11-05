/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt

public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed

/-!
# Good Hierarchy

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A hierarchy with disjoint auxiliary color pairs satisfying avoidance, refresh and closure
conditions.
-/
structure GoodHierarchy {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating} {base : HierarchyBase ett phi}
    (H : TashkinovHierarchy ett base) where
  /-- The auxiliary color or color family used by this configuration. -/
  gamma : Fin (H.dividerCount + 1) → Fin k → Finset (Fin k)
  twoColors : ∀ j eta, eta ∈ HierarchyStoredColorsAt H j → (gamma j eta).card = 2
  avoidance :
    ∀ j eta,
      eta ∈ HierarchyStoredColorsAt H j →
        gamma j eta ⊆ HierarchyStageMissingColors H j \ HierarchySegmentColors H j eta
  disjointPairs :
    ∀ j eta theta,
      eta ∈ HierarchyStoredColorsAt H j →
        theta ∈ HierarchyStoredColorsAt H j → eta ≠ theta → Disjoint (gamma j eta) (gamma j theta)
  uniqueRefresh :
    ∀ i : Fin H.dividerCount,
    ∃! eta : Fin k, eta ∈ HierarchyStoredColorsAt H i.succ ∧ gamma i.succ eta ⊆
        ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \ TreeSequenceVertexSet
        (HierarchyStarredStage H i.castSucc)).biUnion fun v => MissingColors G phi v) ∧
    ∀ theta ∈ HierarchyStoredColorsAt H i.succ, theta ≠ eta → gamma i.succ theta = gamma
        i.castSucc theta
  parallelBase :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
      ¬TreeColorSetMinusClosed G phi base.core ((HierarchyStoredColorsAt H 0).biUnion (gamma 0)) ∧
        4 ≤
          ((TreeMissingColors phi Tn ∩ TreeMissingColors phi base.closure) \
              (HierarchyStoredColorsAt H 0).biUnion (gamma 0)).card
  minusClosed :
    ∀ i : Fin H.dividerCount,
      TreeColorSetMinusClosed G phi (H.stage i.succ.castSucc)
        ((HierarchyStoredColorsAt H i.succ).biUnion (gamma i.castSucc))

end GoldbergSeymour

end
