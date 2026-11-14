/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchy

public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColors

public import LeanPool.GoldbergSeymour.MaximumProperty

/-!
# Step1Exit Leg Presentation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A good hierarchy together with two disjoint ordered exit paths and their boundary edges. -/
structure Step1ExitLegPresentation {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ) where
  /-- The initial partial coloring of the extension series. -/
  input : PartialEdgeColoring E k
  /-- The underlying ordered tree. -/
  T : TreeSequence G e0
  /-- The generating partial coloring. -/
  phi : PartialEdgeColoring E k
  /-- The extended Tashkinov tree underlying the presentation. -/
  ett : ExtendedTashkinovTree G k e0 input T phi
  /-- The hierarchy base, or base node when recording a cycle. -/
  base : HierarchyBase ett phi
  /-- The hierarchy carried by this presentation. -/
  hierarchy : TashkinovHierarchy ett base
  /-- The auxiliary color pairs and their good-hierarchy certificates. -/
  good : GoodHierarchy hierarchy
  rounds_eq : ett.rounds = n
  maximum : MaximumProperty ett
  divider_lt : hierarchy.dividerCount < q
  proper : IsProperEdgeColoring G phi
  oneUncolored : IsOneEdgeUncolored phi e0
  large :
    2 * ett.rounds + 11 ≤
      (TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card
  terminalMinusClosed :
    TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors hierarchy).biUnion
        (good.gamma (Fin.last hierarchy.dividerCount)))
  /-- The first color of the two-color exit configuration. -/
  a : Fin k
  /-- The second color of the two-color exit configuration. -/
  b : Fin k
  a_ne_b : a ≠ b
  aMissing : a ∈ TreeMissingColors phi T
  aClosed : TreeColorSetClosed G phi T { a }
  /-- The outside endpoint of the first exit path. -/
  a1 : V
  /-- The inside endpoint of the first exit path. -/
  b1 : V
  /-- The outside endpoint of the second exit path. -/
  a2 : V
  /-- The inside endpoint of the second exit path. -/
  b2 : V
  /-- The first two-color exit walk. -/
  P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a1) (Sum.inl b1)
  /-- The second two-color exit walk. -/
  P2 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl b2)
  exit1 : TreeExitPath T phi a b a1 b1 P1
  exit2 : TreeExitPath T phi a b a2 b2 P2
  disjoint12 : ∀ x, x ∈ P1.support → x ∉ P2.support
  outsideDistinct : a1 ≠ a2
  treeDistinct : b1 ≠ b2
  treeOrder : TreeVertexOrder T b1 b2
  /-- The first selected boundary edge. -/
  f1 : E
  /-- The second selected boundary edge. -/
  f2 : E
  boundary1 : f1 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  boundary2 : f2 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  incident1 : Incident G b1 f1
  incident2 : Incident G b2 f2
  support1 : Sum.inr f1 ∈ P1.support
  support2 : Sum.inr f2 ∈ P2.support

end GoldbergSeymour

end
