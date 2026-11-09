/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt

/-!
# Hierarchy Stored Colors Antitone

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem HierarchyStoredColorsAntitone {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (i : Fin H.dividerCount) :
    HierarchyStoredColorsAt H i.succ ⊆
      HierarchyStoredColorsAt H i.castSucc := by
  classical
  unfold HierarchyStoredColorsAt
  intro c hc
  have initialVertices : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab v hv
    exact hab.vertexSet_subset hv
  have hstage : TreeSequenceInitialSegment
      (HierarchyStarredStage H i.castSucc)
      (HierarchyStarredStage H i.succ) := by
    exact H.starredStageInitialSegmentOfLE i.castSucc i.succ (by
      change i.val ≤ i.val + 1
      exact Nat.le_succ _)
  apply Finset.mem_sdiff.mpr
  refine ⟨(Finset.mem_sdiff.mp hc).1, ?_⟩
  intro hprev
  apply (Finset.mem_sdiff.mp hc).2
  unfold TreeMissingColors at hprev ⊢
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hprev
  apply Finset.mem_biUnion.mpr
  refine ⟨v, ?_, hcv⟩
  exact initialVertices hstage hv

end GoldbergSeymour

end
