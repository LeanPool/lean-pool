/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tashkinov Augmentation Sequence Restrict

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequenceRestrict
    {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S B C : TreeSequence G e0)
    (hSC : TashkinovAugmentationSequence phi S C)
    (hSB : TreeSequenceInitialSegment S B)
    (hBC : TreeSequenceInitialSegment B C) :
    TashkinovAugmentationSequence phi S B := by
  classical
  unfold TashkinovAugmentationSequence at hSC ⊢
  induction hSC generalizing B with
  | refl =>
      have hlen : B.length = S.length :=
        Nat.le_antisymm hBC.1 hSB.1
      have hBS : B = S :=
        TreeSequenceInitialSegment.eq_of_length_eq hBC hlen
      subst B
      exact Relation.ReflTransGen.refl
  | @tail A C hSA hAC ih =>
      rcases hAC with ⟨hlen, hinitAC, hcolor⟩
      by_cases hBA : B.length ≤ A.length
      · exact ih B hSB
          (TreeSequenceInitialSegment.of_common_extension hinitAC hBC hBA)
      · have hBlen : B.length = C.length := by
          rcases hBC with ⟨hBCle, _, _⟩
          omega
        have hBCeq : B = C :=
          TreeSequenceInitialSegment.eq_of_length_eq hBC hBlen
        subst B
        exact Relation.ReflTransGen.tail hSA ⟨hlen, hinitAC, hcolor⟩

/-- A one-edge extension lies in every longer prefix reached by its augmentation route. -/
theorem TreeSequenceAdjoinEdge.initialSegment_of_route {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 edge : E}
    {initial adjoined intermediate extension : TreeSequence G e0}
    {coloring : PartialEdgeColoring E k}
    (adjoin : TreeSequenceAdjoinEdge initial edge adjoined)
    (route : TashkinovAugmentationSequence coloring adjoined extension)
    (prefixSegment : TreeSequenceInitialSegment intermediate extension)
    (longer : initial.length < intermediate.length) :
    TreeSequenceInitialSegment adjoined intermediate := by
  obtain ⟨lengthEq, _, _⟩ := adjoin
  exact prefixSegment.of_common_extension
    (TashkinovAugmentationSequenceInitialSegment _ _ _ route) (by omega)

/-- Restrict a route from a one-edge extension to an intermediate longer prefix. -/
theorem TreeSequenceAdjoinEdge.restrict_route {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 edge : E}
    {initial adjoined intermediate extension : TreeSequence G e0}
    {coloring : PartialEdgeColoring E k}
    (adjoin : TreeSequenceAdjoinEdge initial edge adjoined)
    (route : TashkinovAugmentationSequence coloring adjoined extension)
    (prefixSegment : TreeSequenceInitialSegment intermediate extension)
    (longer : initial.length < intermediate.length) :
    TashkinovAugmentationSequence coloring adjoined intermediate := by
  exact TashkinovAugmentationSequenceRestrict _ _ _ _ route
    (adjoin.initialSegment_of_route route prefixSegment longer) prefixSegment

end GoldbergSeymour

end
