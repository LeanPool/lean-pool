/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchy

/-!
# Good Hierarchy Reserved Disjoint

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GoodHierarchyReservedDisjoint {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} {H : TashkinovHierarchy ett base}
    (good : GoodHierarchy H) (j : Fin (H.dividerCount + 1)) :
    (∀ eta ∈ HierarchyStoredColorsAt H j,
      good.gamma j eta ⊆
        TreeMissingColors phi (HierarchyStarredStage H j)) ∧
    Disjoint
      ((HierarchyStoredColorsAt H j).biUnion (good.gamma j))
      (HierarchyStoredColorsAt H j) := by
  classical
  have stage_subset : ∀ r : Fin (H.dividerCount + 1),
      HierarchyStageMissingColors H r ⊆
        TreeMissingColors phi (HierarchyStarredStage H r) := by
    intro r
    refine Fin.cases ?_ (fun i => ?_) r
    · change TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆
        TreeMissingColors phi base.core
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
      · obtain ⟨hchosen, hclosure, hu⟩ := base.parallel hp
        rcases hu with ⟨u⟩
        have hsub : TreeSequenceVertexSet
            (ett.series.data.tree n.castSucc) ⊆ TreeSequenceVertexSet base.core := by
          rw [u.vertexSet]
          exact Finset.subset_union_left
        intro c hc
        unfold TreeMissingColors at hc ⊢
        simp only [Finset.mem_biUnion] at hc ⊢
        obtain ⟨v, hv, hcv⟩ := hc
        exact ⟨v, hsub hv, hcv⟩
      · have hn := base.nonparallel hp
        rw [hn]
    · change TreeMissingColors phi (H.stage i.succ.castSucc) ⊆
        TreeMissingColors phi (H.stage i.succ.castSucc)
      exact fun c hc => hc
  constructor
  · intro eta heta c hc
    have hav := good.avoidance j eta heta
    exact stage_subset j ((Finset.mem_sdiff.mp (hav hc)).1)
  · rw [Finset.disjoint_left]
    intro c hc hs
    simp only [Finset.mem_biUnion] at hc
    obtain ⟨eta, heta, hce⟩ := hc
    have hav := good.avoidance j eta heta
    have hmiss : c ∈ TreeMissingColors phi (HierarchyStarredStage H j) := by
      exact stage_subset j ((Finset.mem_sdiff.mp (hav hce)).1)
    have hstored := (Finset.mem_sdiff.mp hs).2
    exact hstored hmiss

end GoldbergSeymour

end
