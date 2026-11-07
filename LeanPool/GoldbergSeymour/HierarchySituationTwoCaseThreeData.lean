/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationTwoCommonTailData

/-!
# Hierarchy Situation Two Case Three Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A color missing at the terminal vertex and at an earlier vertex before the penultimate one. -/
structure HierarchySituationTwoCaseThreeData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) extends
    HierarchySituationTwoCommonTailData G k e0 input T phi ett base C ctx where
  /-- The distinguished color constrained by the accompanying missing-color conditions. -/
  alpha : Fin k
  alphaMissingTerminal : alpha ∈ MissingColors G phi (T.vertex terminalVertexIndex)
  /-- An earlier vertex position witnessing the missing-color condition. -/
  earlierVertexIndex : Fin (T.length + 1)
  earlierVertexBeforePenultimate : earlierVertexIndex.val < penultimateVertexIndex.val
  alphaMissingEarlier : alpha ∈ MissingColors G phi (T.vertex earlierVertexIndex)

end GoldbergSeymour

end
