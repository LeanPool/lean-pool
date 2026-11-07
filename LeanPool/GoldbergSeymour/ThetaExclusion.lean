/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength

/-!
# P2880_T1_Theta Exclusion

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2880_T1_ThetaExclusion
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (mu : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T mu)
    (base : HierarchyBase ett mu) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T mu ett base C)
    (j : Nat) (hpositive : 1 ≤ j) (hbefore : j < HierarchyFullTailLength C) :
    let H := C.hierarchy
    let q := Fin.last H.dividerCount
    let Y := HierarchyFullTailPrefix C j
    ∀ theta ∈ MissingColors G mu (Y.vertex (Fin.last Y.length)),
      theta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) := by
  classical
  dsimp only
  let H := C.hierarchy
  let q := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let Y := HierarchyFullTailPrefix C j
  let Z := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have helementary : ColoredVertexSetElementary G mu (TreeSequenceVertexSet Z) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T mu ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hAT : TreeSequenceInitialSegment A T := by
    have hnext : TreeSequenceInitialSegment (HierarchyStarredStage H q)
        (H.stage q.succ) := by
      refine Fin.cases ?_ (fun i => ?_) q
      · exact H.coreInsideFirst
      · exact H.nested i.succ
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    simpa only [hlast, H.terminalStage] using hnext
  have hordinary : TreeSequenceInitialSegment (H.stage q.castSucc) A := by
    exact H.stageInitialSegmentOfStarredStage q q le_rfl
  have hstageMissing :
      HierarchyStageMissingColors H q =
        TreeMissingColors mu (H.stage q.castSucc) := by
    refine Fin.cases ?_ (fun i => ?_) q
    · change TreeMissingColors mu (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors mu (H.stage 0)
      rw [H.baseStage]
    · simp only [HierarchyStageMissingColors, Fin.cases_succ]
  have hYlen : Y.length = A.length + j := by
    change min (A.length + j) T.length = A.length + j
    have htail : j < T.length - A.length := hbefore
    omega
  have hZlen : Z.length = T.length - 1 := by
    change min (A.length + (T.length - A.length - 1)) T.length = T.length - 1
    have htail : j < T.length - A.length := hbefore
    omega
  have hYT : TreeSequenceInitialSegment Y T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hZT : TreeSequenceInitialSegment Z T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have commonPrefix {U W : TreeSequence G e0}
      (hu : TreeSequenceInitialSegment U T)
      (hw : TreeSequenceInitialSegment W T) (hlen : U.length ≤ W.length) :
      TreeSequenceInitialSegment U W := by
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hw.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans
        (hu.2.1 i)
    · intro i
      exact (hw.2.2 (Fin.castLE hlen i)).symm.trans (hu.2.2 i)
  have hAY : TreeSequenceInitialSegment A Y :=
    commonPrefix hAT hYT (by rw [hYlen]; omega)
  have hYZ : TreeSequenceInitialSegment Y Z := by
    apply commonPrefix hYT hZT
    rw [hYlen, hZlen]
    have htail : j < T.length - A.length := hbefore
    omega
  have hnew : Y.vertex (Fin.last Y.length) ∉ TreeSequenceVertexSet A := by
    intro hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    have he := Y.vertex_injective ((hAY.2.1 i).trans hi)
    have heval := congrArg Fin.val he
    have hibound := i.isLt
    simp only [Fin.val_castLE, Fin.val_last] at heval
    rw [hYlen] at heval
    omega
  intro theta hmissing hgamma
  obtain ⟨eta, heta, htheta⟩ := Finset.mem_biUnion.mp hgamma
  have hstage : theta ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp (C.good.avoidance q eta heta htheta)).1
  rw [hstageMissing] at hstage
  obtain ⟨v, hv, hvMissing⟩ := Finset.mem_biUnion.mp hstage
  have hvA := TreeSequenceInitialSegmentVertexSetSubset hordinary hv
  have hvY := TreeSequenceInitialSegmentVertexSetSubset hAY hvA
  have hvZ := TreeSequenceInitialSegmentVertexSetSubset hYZ hvY
  have hyZ : Y.vertex (Fin.last Y.length) ∈ TreeSequenceVertexSet Z :=
    TreeSequenceInitialSegmentVertexSetSubset hYZ (by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨Fin.last Y.length, rfl⟩)
  have hne : v ≠ Y.vertex (Fin.last Y.length) := by
    intro heq
    exact hnew (heq ▸ hvA)
  exact Finset.disjoint_left.mp (helementary hvZ hyZ hne) hvMissing hmissing

end GoldbergSeymour

end
