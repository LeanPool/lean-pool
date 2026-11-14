/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ElementaryClosedExitPairDistinctComponents
public import LeanPool.GoldbergSeymour.ElementaryClosedExitPairSameComponent

/-!
# Elementary Closed Exit Pair Extends Triple

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma ElementaryClosedExitPairExtendsTriple {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G phi)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (a b : Fin k) (hne : a ≠ b)
    (hamissing : a ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {a})
    (hbpresent : b ∉ TreeMissingColors phi T)
    (a1 b1 a2 b2 : V)
    (P1 : (TwoColorIncidenceGraph G phi a b).Walk
      (Sum.inl a1) (Sum.inl b1))
    (P2 : (TwoColorIncidenceGraph G phi a b).Walk
      (Sum.inl a2) (Sum.inl b2))
    (hP1 : TreeExitPath T phi a b a1 b1 P1)
    (hP2 : TreeExitPath T phi a b a2 b2 P2)
    (hdisjoint : ∀ x, x ∈ P1.support → x ∉ P2.support)
    (haends : a1 ≠ a2) (hbends : b1 ≠ b2) :
    ∃ (a3 b3 : V)
      (P3 : (TwoColorIncidenceGraph G phi a b).Walk
        (Sum.inl a3) (Sum.inl b3))
      (f3 : E),
      TreeExitPath T phi a b a3 b3 P3 ∧
      (∀ x, x ∈ P1.support → x ∉ P3.support) ∧
      (∀ x, x ∈ P2.support → x ∉ P3.support) ∧
      a3 ≠ a1 ∧ a3 ≠ a2 ∧ b3 ≠ b1 ∧ b3 ≠ b2 ∧
      f3 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b ∧
      Incident G b3 f3 ∧ Sum.inr f3 ∈ P3.support := by
  classical
  by_cases hcomponents :
      TwoColorComponent G phi a b (Sum.inl a1) =
        TwoColorComponent G phi a b (Sum.inl a2)
  · exact ElementaryClosedExitPairSameComponent G T phi hproper helementary
      a b hne hamissing hclosed hbpresent a1 b1 a2 b2 P1 P2 hP1 hP2
      hdisjoint haends hbends hcomponents
  · exact ElementaryClosedExitPairDistinctComponents G T phi hproper
      helementary a b hne hamissing hclosed hbpresent a1 b1 a2 b2 P1 P2
      hP1 hP2 hdisjoint haends hbends hcomponents

end GoldbergSeymour

end
