/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext

/-!
# Hierarchy Situation Two Tail Data

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Common final-tail data with the last-edge color present at the penultimate vertex. -/
structure HierarchySituationTwoTailData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) where
  tailAtLeastTwo : 2 ≤ HierarchyFullTailLength C
  pathNumberFull : HierarchyPathNumber C.hierarchy = HierarchyFullTailLength C
  /-- The index of the final tree edge. -/
  lastEdgeIndex : Fin T.length
  /-- The index of the penultimate tree vertex. -/
  penultimateVertexIndex : Fin (T.length + 1)
  /-- The index of the final tree vertex. -/
  terminalVertexIndex : Fin (T.length + 1)
  lastEdgePosition : lastEdgeIndex.val + 1 = T.length
  penultimateVertexPosition : penultimateVertexIndex.val + 1 = T.length
  terminalVertexPosition : terminalVertexIndex.val = T.length
  lastEdgeNotIncidentPenultimate :
    ¬Incident G (T.vertex penultimateVertexIndex) (T.edge lastEdgeIndex)
  /-- The auxiliary color with the missing-color conditions recorded below. -/
  theta : Fin k
  thetaOnLastEdge : phi (T.edge lastEdgeIndex) = some theta
  thetaPresentPenultimate : theta ∉ MissingColors G phi (T.vertex penultimateVertexIndex)

end GoldbergSeymour

end
