/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColors
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt

/-!
# Hierarchy Terminal Stored Colors Subset Last

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchyTerminalStoredColorsSubsetLast {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base) :
    HierarchyTerminalStoredColors H ⊆
        HierarchyStoredColorsAt H (Fin.last H.dividerCount) ∧
      (∀ eta : Fin k,
        eta ∈ HierarchyStoredColorsAt H (Fin.last H.dividerCount) →
        eta ∉ HierarchyTerminalStoredColors H →
        eta ∈ TreeMissingColors phi T) := by
  classical
  have starToTerminal : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) T := by
    exact H.lastStarredInitialSegment
  have vertexSubset : TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount)) ⊆
        TreeSequenceVertexSet T := by
    exact starToTerminal.vertexSet_subset
  have missingSubset : TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)) ⊆
        TreeMissingColors phi T := by
    intro c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    obtain ⟨v, hv, hc⟩ := hc
    exact ⟨v, vertexSubset hv, hc⟩
  constructor
  · intro c hc
    simp only [HierarchyTerminalStoredColors, Finset.mem_sdiff] at hc
    simp only [HierarchyStoredColorsAt, Finset.mem_sdiff]
    exact ⟨hc.1, fun hm => hc.2 (missingSubset hm)⟩
  · intro c hc hnot
    simp only [HierarchyStoredColorsAt, Finset.mem_sdiff] at hc
    simp only [HierarchyTerminalStoredColors, Finset.mem_sdiff] at hnot
    by_contra hmissing
    exact hnot ⟨hc.1, hmissing⟩

end GoldbergSeymour

end
