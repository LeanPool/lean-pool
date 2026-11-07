/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAntitone

/-!
# Good Hierarchy New Missing Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GoodHierarchyNewMissingClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett phi} {H : TashkinovHierarchy ett base}
    (good : GoodHierarchy H) (i : Fin H.dividerCount)
    (helementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (H.stage i.succ.castSucc)))
    (alpha : Fin k)
    (halpha : alpha ∈
      ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
          fun v => MissingColors G phi v)) :
    BoundaryColorEdges G phi
      (TreeSequenceVertexSet (H.stage i.succ.castSucc)) alpha = ∅ := by
  classical
  let current := TreeSequenceVertexSet (H.stage i.succ.castSucc)
  let starred := TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)
  let reserved := (HierarchyStoredColorsAt H i.succ).biUnion (good.gamma i.castSucc)
  obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp halpha
  have hvm : alpha ∈ TreeMissingColors phi (H.stage i.succ.castSucc) := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_sdiff.mp hv).1, hav⟩
  have initialVertices : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab x hx
    unfold TreeSequenceVertexSet at hx ⊢
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨hlen, hvertices, hedges⟩ := hab
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) a, Finset.mem_univ _, ?_⟩
    exact hvertices a
  have oldSegment : TreeSequenceInitialSegment
      (HierarchyStarredStage H i.castSucc)
      (H.stage i.succ.castSucc) := by
    by_cases hi : i.val = 0
    · have hi' : i = ⟨0, Fin.pos i⟩ := Fin.ext hi
      rw [hi']
      dsimp [starred]
      change TreeSequenceInitialSegment base.core (H.stage ⟨1, by omega⟩)
      exact H.coreInsideFirst
    · have hne : i.castSucc ≠ 0 := by
        intro hz
        apply hi
        exact congrArg Fin.val hz
      change TreeSequenceInitialSegment
        (Fin.cases base.core (fun j => H.stage j.castSucc.succ) i.castSucc)
        (H.stage i.castSucc.succ)
      have hindex : (i.castSucc.pred hne).succ = i.castSucc :=
        Fin.succ_pred i.castSucc hne
      have hstar :
          Fin.cases base.core (fun j => H.stage j.castSucc.succ) i.castSucc =
            H.stage i.castSucc.castSucc := by
        rw [← hindex]
        rfl
      rw [hstar]
      exact H.nested i.castSucc
  have oldMissing : ∀ {c : Fin k},
      c ∈ HierarchyStageMissingColors H i.castSucc →
      ∃ u, u ∈ starred ∧ c ∈ MissingColors G phi u := by
    intro c hc
    by_cases hi : i.val = 0
    · have hi' : i = ⟨0, Fin.pos i⟩ := Fin.ext hi
      dsimp [starred]
      rw [hi']
      rw [hi'] at hc
      simp only [HierarchyStageMissingColors, Fin.castSucc_succ, Fin.castSucc_mk, Fin.zero_eta,
    Fin.cases_zero] at hc
      have hseg : TreeSequenceInitialSegment
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) base.core := by
        exact base.lastRoundInitialSegmentCore
      unfold TreeMissingColors at hc
      obtain ⟨u, hu, hcu⟩ := Finset.mem_biUnion.mp hc
      refine ⟨u, ?_, hcu⟩
      exact initialVertices hseg hu
    · have hne : i.castSucc ≠ 0 := by
        intro hz
        apply hi
        exact congrArg Fin.val hz
      have hindex : (i.castSucc.pred hne).succ = i.castSucc :=
        Fin.succ_pred i.castSucc hne
      rw [← hindex] at hc
      simp only [HierarchyStageMissingColors, Fin.cases_succ] at hc
      unfold TreeMissingColors at hc
      obtain ⟨u, hu, hcu⟩ := Finset.mem_biUnion.mp hc
      refine ⟨u, ?_, hcu⟩
      have hstar : HierarchyStarredStage H i.castSucc =
          H.stage i.castSucc.castSucc := by
        unfold HierarchyStarredStage
        rw [← hindex]
        rfl
      dsimp [starred]
      rw [hstar]
      rw [hindex] at hu
      exact hu
  have hreserved : alpha ∉ reserved := by
    intro hr
    obtain ⟨eta, heta, hgamma⟩ := Finset.mem_biUnion.mp hr
    have hetaOld : eta ∈ HierarchyStoredColorsAt H i.castSucc :=
      HierarchyStoredColorsAntitone H i heta
    have havoid := good.avoidance i.castSucc eta hetaOld hgamma
    have hstageMissing : alpha ∈ HierarchyStageMissingColors H i.castSucc :=
      (Finset.mem_sdiff.mp havoid).1
    obtain ⟨u, hu, hum⟩ := oldMissing hstageMissing
    have hucurrent : u ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc) :=
      initialVertices oldSegment hu
    have huv : u ≠ v := by
      intro huv
      apply (Finset.mem_sdiff.mp hv).2
      rw [← huv]
      exact hu
    exact (Finset.disjoint_left.1
      (helementary (u := v) (v := u) (Finset.mem_sdiff.mp hv).1 hucurrent
        (Ne.symm huv)))
      hav hum
  have hminus : alpha ∈
      TreeMissingColors phi (H.stage i.succ.castSucc) \ reserved := by
    exact Finset.mem_sdiff.mpr ⟨hvm, hreserved⟩
  exact (good.minusClosed i) alpha hminus

end GoldbergSeymour

end
