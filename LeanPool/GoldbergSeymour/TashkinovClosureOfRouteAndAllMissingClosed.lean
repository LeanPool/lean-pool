/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TreeColorSetClosed

/-!
# Tashkinov Closure Of Route And All Missing Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovClosureOfRouteAndAllMissingClosed
    {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S T : TreeSequence G e0)
    (hroute : TashkinovAugmentationSequence phi S T)
    (hclosed : TreeColorSetClosed G phi T (TreeMissingColors phi T)) :
    TashkinovClosure phi S T := by
  refine ⟨hroute, ?_⟩
  intro f c v hf hv hfc hmissing
  have hc : c ∈ TreeMissingColors phi T := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨v, hv, hmissing⟩
  have hempty := hclosed c hc
  have hboundaryColor :
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) c := by
    unfold BoundaryColorEdges
    exact Finset.mem_filter.mpr ⟨hf, hfc⟩
  rw [hempty] at hboundaryColor
  simp at hboundaryColor

end GoldbergSeymour

end
