/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.OrderedTreeUnion

public import LeanPool.GoldbergSeymour.TreeSequencePrefix

/-!
# Hierarchy Base

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The core, closure and support position used to start a hierarchy for an extended tree. -/
structure HierarchyBase {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (phi : PartialEdgeColoring E k) where
  /-- The initial core tree of the hierarchy. -/
  core : TreeSequence G e0
  /-- The auxiliary closure used for a parallel-extension hierarchy base. -/
  closure : TreeSequence G e0
  /-- The position of the terminal extension support in the penultimate ladder tree. -/
  supportPosition : Fin ((ett.series.data.tree (Fin.last ett.rounds).castSucc).length + 1)
  supportPositive : 1 ≤ supportPosition.val
  terminalMissingColors :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    TreeMissingColors phi Tn = TreeMissingColors generating Tn
  parallel :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
      ett.series.data.chosenVertex n = some (Tn.vertex supportPosition) ∧
        TashkinovClosure phi
            (TreeSequencePrefix Tn supportPosition.val supportPositive
              (Nat.le_of_lt_succ supportPosition.isLt))
            closure ∧
          Nonempty (OrderedTreeUnion Tn closure core)
  nonparallel :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    ett.series.data.kind n ≠ some TashkinovExtensionKind.PE → core = Tn

end GoldbergSeymour

end
