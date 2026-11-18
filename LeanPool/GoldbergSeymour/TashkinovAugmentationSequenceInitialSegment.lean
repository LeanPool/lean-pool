/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence

/-!
# Tashkinov Augmentation Sequence Initial Segment

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequenceInitialSegment
    {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (A B : TreeSequence G e0)
    (hAB : TashkinovAugmentationSequence phi A B) :
    TreeSequenceInitialSegment A B := by
  unfold TashkinovAugmentationSequence at hAB
  induction hAB with
  | refl => exact TreeSequenceInitialSegment.refl _
  | @tail B C hAB hBC initial =>
      obtain ⟨_, segment, _⟩ := hBC
      exact initial.trans segment

end GoldbergSeymour

end
