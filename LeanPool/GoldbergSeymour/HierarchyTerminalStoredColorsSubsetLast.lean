/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

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
  have segmentRight {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) (hBC : B = C) :
      TreeSequenceInitialSegment A C := by
    subst C
    exact hAB
  have starToTerminal : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) T := by
    by_cases hz : H.dividerCount = 0
    · have hstar : HierarchyStarredStage H (Fin.last H.dividerCount) =
          base.core := by
        have hlast : Fin.last H.dividerCount =
            (0 : Fin (H.dividerCount + 1)) := by
          apply Fin.ext
          simp [hz]
        rw [hlast]
        rfl
      rw [hstar]
      have hindex : (1 : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := by
        apply Fin.ext
        simp [hz]
      have hstage : H.stage (1 : Fin (H.dividerCount + 2)) = T :=
        (congrArg H.stage hindex).trans H.terminalStage
      exact segmentRight H.coreInsideFirst hstage
    · let i : Fin H.dividerCount :=
        ⟨H.dividerCount - 1, Nat.sub_lt (Nat.zero_lt_of_ne_zero hz) (by omega)⟩
      have hlast : Fin.last H.dividerCount = i.succ := by
        apply Fin.ext
        simp [i]
        omega
      have hstar : HierarchyStarredStage H (Fin.last H.dividerCount) =
          H.stage i.succ.castSucc := by
        rw [hlast]
        rfl
      rw [hstar]
      have hterminal : H.stage i.succ.succ = T := by
        have hindex : i.succ.succ = Fin.last (H.dividerCount + 1) := by
          apply Fin.ext
          simp [i]
          omega
        exact (congrArg H.stage hindex).trans H.terminalStage
      exact segmentRight (H.nested i.succ) hterminal
  have vertexSubset : TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount)) ⊆
        TreeSequenceVertexSet T := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨Fin.castLE (Nat.succ_le_succ starToTerminal.1) i,
      starToTerminal.2.1 i⟩
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
