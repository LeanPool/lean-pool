/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchySituationTwoTailData
public import LeanPool.GoldbergSeymour.TreeSequenceEdgeSet

/-!
# Hierarchy Situation Two Reordered Trees

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Certified reordered penultimate and final trees preserving the relevant vertex and edge sets. -/
structure HierarchySituationTwoReorderedTrees {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoTailData G k e0 input T phi ett base C ctx) where
  /-- The index of the next-to-last tree edge. -/
  penultimateEdgeIndex : Fin T.length
  penultimateEdgePosition : penultimateEdgeIndex.val + 2 = T.length
  /-- The reordered penultimate tree. -/
  minus : TreeSequence G e0
  /-- The reordered final tree. -/
  star : TreeSequence G e0
  originalPenultimate :
    TreeSequenceAdjoinEdge (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2))
      (T.edge penultimateEdgeIndex) (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))
  originalFinal :
    TreeSequenceAdjoinEdge (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))
      (T.edge D.lastEdgeIndex) T
  minusFinal :
    TreeSequenceAdjoinEdge (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2))
      (T.edge D.lastEdgeIndex) minus
  minusTerminalVertex : minus.vertex (Fin.last minus.length) = T.vertex D.terminalVertexIndex
  starFinal : TreeSequenceAdjoinEdge minus (T.edge penultimateEdgeIndex) star
  starPenultimateVertex : star.vertex (Fin.last star.length) = T.vertex D.penultimateVertexIndex
  minusVertexSet :
    TreeSequenceVertexSet minus = TreeSequenceVertexSet T \ {T.vertex D.penultimateVertexIndex}
  minusEdgeSet : TreeSequenceEdgeSet minus = TreeSequenceEdgeSet T \ {T.edge penultimateEdgeIndex}
  starVertexSet : TreeSequenceVertexSet star = TreeSequenceVertexSet T
  starEdgeSet : TreeSequenceEdgeSet star = TreeSequenceEdgeSet T

end GoldbergSeymour

end
