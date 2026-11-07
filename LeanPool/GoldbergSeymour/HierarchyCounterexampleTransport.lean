/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexample

/-!
# Counterexamples under rung and vertex-set identities

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Transport a counterexample using a new good hierarchy with the same rounds and vertices. -/
abbrev HierarchyCounterexample.transport {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ}
    {oldEdge newEdge : E} {oldInput newInput phi : PartialEdgeColoring E k}
    {oldTree : TreeSequence G oldEdge} {newTree : TreeSequence G newEdge}
    {oldETT : ExtendedTashkinovTree G k oldEdge oldInput oldTree phi}
    {newETT : ExtendedTashkinovTree G k newEdge newInput newTree phi}
    {oldBase : HierarchyBase oldETT phi} {newBase : HierarchyBase newETT phi}
    (counterexample : HierarchyCounterexample oldBase)
    (hierarchy : TashkinovHierarchy newETT newBase) (good : GoodHierarchy hierarchy)
    (maximum : MaximumProperty newETT) (rounds : newETT.rounds = oldETT.rounds)
    (vertices : TreeSequenceVertexSet newTree = TreeSequenceVertexSet oldTree) :
    HierarchyCounterexample newBase where
  positive := by rw [rounds]; exact counterexample.positive
  hierarchy := hierarchy
  good := good
  maximum := maximum
  notElementary := by rw [vertices]; exact counterexample.notElementary

end GoldbergSeymour

end
