/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.TashkinovAugmentation

public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetStrict

/-!
# Boundary Missing Color Augmentation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem BoundaryMissingColorAugmentation {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (X : TreeSequence G e0)
    (c : Fin k) (f : E)
    (hf : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet X) c)
    (hc : c ∈ TreeMissingColors phi X) :
    ∃ Xplus : TreeSequence G e0,
      TreeSequenceAdjoinEdge X f Xplus ∧
      TashkinovAugmentation phi X Xplus ∧
      TreeSequenceVertexSet X ⊂ TreeSequenceVertexSet Xplus := by
  classical
  change f ∈ (BoundaryEdges G (TreeSequenceVertexSet X)).filter
    (fun g => phi g = some c) at hf
  rw [Finset.mem_filter] at hf
  obtain ⟨Xplus, hAdjoin⟩ :=
    TreeSequenceBoundaryEdgeAppendExists X f hf.1
  obtain ⟨hLength, hInitial, hLastEdge⟩ := hAdjoin
  refine ⟨Xplus, ⟨hLength, hInitial, hLastEdge⟩, ?_, ?_⟩
  · refine ⟨hLength, hInitial, c, ?_, hc⟩
    rw [hLastEdge]
    exact hf.2
  · apply TreeSequenceInitialSegmentVertexSetStrict hInitial
    omega

end GoldbergSeymour

end
