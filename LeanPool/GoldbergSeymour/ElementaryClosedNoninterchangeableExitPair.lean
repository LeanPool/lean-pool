/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ClosedColorExitPathBoundaryEdge
public import LeanPool.GoldbergSeymour.ElementaryClosedNoninterchangeableDisjointExitPaths

/-!
# Elementary Closed Noninterchangeable Exit Pair

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma ElementaryClosedNoninterchangeableExitPair {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (a b : Fin k) (hne : a ≠ b)
    (_ : a ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {a})
    (hnot : ¬ TreeInterchangeable G T phi a b) :
    ∃ (a1 b1 a2 b2 : V)
      (P1 : (TwoColorIncidenceGraph G phi a b).Walk
        (Sum.inl a1) (Sum.inl b1))
      (P2 : (TwoColorIncidenceGraph G phi a b).Walk
        (Sum.inl a2) (Sum.inl b2))
      (f1 f2 : E),
      TreeExitPath T phi a b a1 b1 P1 ∧
      TreeExitPath T phi a b a2 b2 P2 ∧
      (∀ x, x ∈ P1.support → x ∉ P2.support) ∧
      a1 ≠ a2 ∧ b1 ≠ b2 ∧
      f1 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b ∧
      f2 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b ∧
      Incident G b1 f1 ∧ Incident G b2 f2 ∧
      Sum.inr f1 ∈ P1.support ∧ Sum.inr f2 ∈ P2.support := by
  classical
  obtain ⟨a1, b1, a2, b2, P1, P2, hP1, hP2, hdisjoint, ha, hb⟩ :=
    ElementaryClosedNoninterchangeableDisjointExitPaths G T phi hproper
      helementary a b hne hclosed hnot
  obtain ⟨f1, hf1, hi1, hs1⟩ :=
    ClosedColorExitPathBoundaryEdge G T phi a b hclosed a1 b1 P1 hP1
  obtain ⟨f2, hf2, hi2, hs2⟩ :=
    ClosedColorExitPathBoundaryEdge G T phi a b hclosed a2 b2 P2 hP2
  exact ⟨a1, b1, a2, b2, P1, P2, f1, f2, hP1, hP2, hdisjoint,
    ha, hb, hf1, hf2, hi1, hi2, hs1, hs2⟩

end GoldbergSeymour

end
