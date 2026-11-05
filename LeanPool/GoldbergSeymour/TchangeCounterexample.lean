/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed

public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeExitPath
public import LeanPool.GoldbergSeymour.TreeMissingColors

/-!
# Tchange Counterexample

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A closed Tashkinov tree with three disjoint exit paths for a fixed pair of colors. -/
structure TchangeCounterexample {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : Nat) (e0 : E) where
  /-- The generating partial coloring. -/
  phi : PartialEdgeColoring E k
  /-- The underlying ordered tree. -/
  T : TreeSequence G e0
  /-- The first color of the two-color exit configuration. -/
  a : Fin k
  /-- The second color of the two-color exit configuration. -/
  b : Fin k
  colorsDistinct : a ≠ b
  triple : KTriple G k e0 phi
  tree : TashkinovTree G e0 phi T
  closed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)
  aMissing : a ∈ TreeMissingColors phi T
  bNotMissing : b ∉ TreeMissingColors phi T
  /-- The outside endpoint of the first exit path. -/
  a1 : V
  /-- The inside endpoint of the first exit path. -/
  b1 : V
  /-- The outside endpoint of the second exit path. -/
  a2 : V
  /-- The inside endpoint of the second exit path. -/
  b2 : V
  /-- The outside endpoint of the third exit path. -/
  a3 : V
  /-- The inside endpoint of the third exit path. -/
  b3 : V
  /-- The first two-color exit walk. -/
  P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a1) (Sum.inl b1)
  /-- The second two-color exit walk. -/
  P2 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl b2)
  /-- The third two-color exit walk. -/
  P3 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a3) (Sum.inl b3)
  exit1 : TreeExitPath T phi a b a1 b1 P1
  exit2 : TreeExitPath T phi a b a2 b2 P2
  exit3 : TreeExitPath T phi a b a3 b3 P3
  disjoint12 : ∀ x, x ∈ P1.support → x ∉ P2.support
  disjoint13 : ∀ x, x ∈ P1.support → x ∉ P3.support
  disjoint23 : ∀ x, x ∈ P2.support → x ∉ P3.support
  remote12 : a1 ≠ a2
  remote13 : a1 ≠ a3
  remote23 : a2 ≠ a3
  tree12 : b1 ≠ b2
  tree13 : b1 ≠ b3
  tree23 : b2 ≠ b3
  /-- The first selected boundary edge. -/
  f1 : E
  /-- The second selected boundary edge. -/
  f2 : E
  /-- The third selected boundary edge. -/
  f3 : E
  boundary1 : f1 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  boundary2 : f2 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  boundary3 : f3 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  incident1 : Incident G b1 f1
  incident2 : Incident G b2 f2
  incident3 : Incident G b3 f3
  support1 : Sum.inr f1 ∈ P1.support
  support2 : Sum.inr f2 ∈ P2.support
  support3 : Sum.inr f3 ∈ P3.support

end GoldbergSeymour

end
