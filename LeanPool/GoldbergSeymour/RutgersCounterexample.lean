/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.RutgersClosedPresentation

/-!
# Rutgers Counterexample

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Three disjoint ordered exit paths and their boundary edges for a closed replacement
presentation.
-/
structure RutgersCounterexample {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (presentation : RutgersClosedPresentation G k e0 original) where
  /-- The distinguished color constrained by the accompanying missing-color conditions. -/
  alpha : Fin k
  /-- The second distinguished color in the alternating configuration. -/
  beta : Fin k
  colorsDistinct : alpha ≠ beta
  alphaMissing : alpha ∈ TreeMissingColors presentation.sigma presentation.U
  betaPresent : beta ∉ TreeMissingColors presentation.sigma presentation.U
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
  Q1 : (TwoColorIncidenceGraph G presentation.sigma alpha beta).Walk (Sum.inl a1) (Sum.inl b1)
  /-- The second two-color exit walk. -/
  Q2 : (TwoColorIncidenceGraph G presentation.sigma alpha beta).Walk (Sum.inl a2) (Sum.inl b2)
  /-- The third two-color exit walk. -/
  Q3 : (TwoColorIncidenceGraph G presentation.sigma alpha beta).Walk (Sum.inl a3) (Sum.inl b3)
  /-- The first selected boundary edge. -/
  f1 : E
  /-- The second selected boundary edge. -/
  f2 : E
  /-- The third selected boundary edge. -/
  f3 : E
  exit1 : TreeExitPath presentation.U presentation.sigma alpha beta a1 b1 Q1
  exit2 : TreeExitPath presentation.U presentation.sigma alpha beta a2 b2 Q2
  exit3 : TreeExitPath presentation.U presentation.sigma alpha beta a3 b3 Q3
  supportDisjoint12 : ∀ x, x ∈ Q1.support → x ∉ Q2.support
  supportDisjoint13 : ∀ x, x ∈ Q1.support → x ∉ Q3.support
  supportDisjoint23 : ∀ x, x ∈ Q2.support → x ∉ Q3.support
  outsideDistinct12 : a1 ≠ a2
  outsideDistinct13 : a1 ≠ a3
  outsideDistinct23 : a2 ≠ a3
  insideDistinct12 : b1 ≠ b2
  insideDistinct13 : b1 ≠ b3
  insideDistinct23 : b2 ≠ b3
  insideOrder12 : TreeVertexOrder presentation.U b1 b2
  insideOrder23 : TreeVertexOrder presentation.U b2 b3
  boundary1 :
    f1 ∈ BoundaryColorEdges G presentation.sigma (TreeSequenceVertexSet presentation.U) beta
  boundary2 :
    f2 ∈ BoundaryColorEdges G presentation.sigma (TreeSequenceVertexSet presentation.U) beta
  boundary3 :
    f3 ∈ BoundaryColorEdges G presentation.sigma (TreeSequenceVertexSet presentation.U) beta
  incident1 : Incident G b1 f1
  incident2 : Incident G b2 f2
  incident3 : Incident G b3 f3
  edgeOnWalk1 : Sum.inr f1 ∈ Q1.support
  edgeOnWalk2 : Sum.inr f2 ∈ Q2.support
  edgeOnWalk3 : Sum.inr f3 ∈ Q3.support

end GoldbergSeymour

end
