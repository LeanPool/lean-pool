/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyPrefixData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeData
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix

/-!
# P2752_T2_Prefix Reconstruction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2752_T2_PrefixReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx)
    (beta : Fin k)
    (hunused : ∀ t : Fin T.length,
      (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length
        ≤ t.val → phi (T.edge t) ≠ some beta)
    (hpresent : beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex))
    (houtside : ∀ v : V,
      Sum.inl v ∈ TwoColorComponent G phi D.alpha beta
        (Sum.inl (T.vertex D.terminalVertexIndex)) →
      v ∉ TreeSequenceVertexSet
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))) :
    let yp := T.vertex D.terminalVertexIndex
    let Q := TwoColorComponent G phi D.alpha beta (Sum.inl yp)
    let sigma := TwoColorComponentSwap G phi D.alpha beta (Sum.inl yp)
    Sum.inl yp ∈ Q ∧
      (∃ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ Q) ∧
      (∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t)) ∧
      StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma ∧
      beta ∈ MissingColors G sigma yp ∧
      Nonempty (HierarchyPrefixData C
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) sigma) := by
  classical
  dsimp only
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  let yp := T.vertex D.terminalVertexIndex
  let sigma := TwoColorComponentSwap G phi D.alpha beta (Sum.inl yp)
  have hroot : Sum.inl yp ∈ TwoColorComponent G phi D.alpha beta (Sum.inl yp) := by
    change (TwoColorIncidenceGraph G phi D.alpha beta).connectedComponentMk
      (Sum.inl yp) = (TwoColorIncidenceGraph G phi D.alpha beta).connectedComponentMk
      (Sum.inl yp)
    rfl
  have hne : D.alpha ≠ beta := by
    intro h
    exact hpresent (h ▸ D.alphaMissingTerminal)
  have hA : TreeSequenceInitialSegment A T := by
    obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
    · have hq : H.dividerCount = 0 := by
        simpa using congrArg Fin.val hz
      have hcore : TreeSequenceInitialSegment base.core T := by
        have hh := H.coreInsideFirst
        have ht : H.stage ⟨1, by omega⟩ = T := by
          convert H.terminalStage using 1; congr 1; apply Fin.ext; simp [hq]
        rw [ht] at hh
        exact hh
      simpa [A, HierarchyStarredStage, hz] using hcore
    · have ha : A = H.stage (Fin.last H.dividerCount).castSucc := by
        simp [A, HierarchyStarredStage, hi]
      rw [ha]
      have hh := H.nested (Fin.last H.dividerCount)
      simpa [H.terminalStage] using hh
  have htail : 2 ≤ T.length - A.length := D.tailAtLeastTwo
  have hlen : Bplus.length = T.length - 1 := by
    change min (A.length + (T.length - A.length - 1)) T.length = T.length - 1
    omega
  have hBT : TreeSequenceInitialSegment Bplus T := by
    refine ⟨Nat.min_le_right _ _, ?_, ?_⟩ <;> intro i <;> rfl
  have prefixCompare {S : TreeSequence G e0}
      (hST : TreeSequenceInitialSegment S T) (hSB : S.length ≤ Bplus.length) :
      TreeSequenceInitialSegment S Bplus := by
    refine ⟨hSB, ?_, ?_⟩
    · intro i
      rw [← hBT.2.1 (Fin.castLE (Nat.succ_le_succ hSB) i)]
      convert hST.2.1 i using 1
      congr 1
    · intro i
      rw [← hBT.2.2 (Fin.castLE hSB i)]
      convert hST.2.2 i using 1
      congr 1
  have hAB : TreeSequenceInitialSegment A Bplus := prefixCompare hA (by omega)
  have hABstrict : A.length < Bplus.length := by omega
  have hNB : TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) Bplus := by
    have hindex : (Fin.last ett.rounds).castSucc =
        (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      rfl
    apply prefixCompare
    · rw [hindex]
      exact ett.abovePenultimate
    · have hn := ett.strictAbovePenultimate
      rw [hindex]
      omega
  have hrecolor : OutsideKempeRecoloring Bplus phi sigma D.alpha beta := by
    refine ⟨hne, {Sum.inl yp}, ?_, ?_⟩
    · intro z hz v hv
      have hz' : z = Sum.inl yp := Finset.mem_singleton.mp hz
      subst z
      exact houtside v hv
    · intro f
      simp [sigma, TwoColorComponentSwap]
  obtain ⟨hproper, hone, _, hinv, hincident⟩ :=
    OutsideKempeRecoloringStable G e0 Bplus ∅ phi sigma D.alpha beta
      ctx.proper ctx.oneEdgeUncolored hrecolor
  have hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma := by
    constructor
    · intro f hf _
      obtain ⟨v, hv, hvf⟩ := hf
      exact hincident f ⟨v, TreeSequenceInitialSegmentVertexSetSubset hNB hv, hvf⟩
    · intro v hv
      exact hinv.2 v (TreeSequenceInitialSegmentVertexSetSubset hNB hv)
  have hlastAlpha : phi (T.edge D.lastEdgeIndex) ≠ some D.alpha := by
    intro hf
    obtain ⟨i, hi⟩ := T.attaches D.lastEdgeIndex
    have hvertex : D.lastEdgeIndex.succ = D.terminalVertexIndex := by
      apply Fin.ext
      simpa [Fin.val_succ, D.terminalVertexPosition] using D.lastEdgePosition
    have hinc : Incident G yp (T.edge D.lastEdgeIndex) := by
      change yp ∈ G.ends (T.edge D.lastEdgeIndex)
      rw [hi, hvertex]
      exact Sym2.mem_mk_left _ _
    have hmissing : D.alpha ∉ PresentColors G phi yp :=
      (Finset.mem_sdiff.mp D.alphaMissingTerminal).2
    exact hmissing (by simp only [PresentColors, Finset.mem_filter,
      Finset.mem_univ, true_and]; exact ⟨T.edge D.lastEdgeIndex, hinc, hf⟩)
  have hlastBeta : phi (T.edge D.lastEdgeIndex) ≠ some beta := by
    apply hunused
    change A.length ≤ D.lastEdgeIndex.val
    have hp := D.lastEdgePosition
    omega
  have hlast : sigma (T.edge D.lastEdgeIndex) = phi (T.edge D.lastEdgeIndex) := by
    simp [sigma, TwoColorComponentSwap, hlastAlpha, hlastBeta]
  have hfixed : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t) := by
    intro t
    by_cases ht : t.val < Bplus.length
    · let j : Fin Bplus.length := ⟨t.val, ht⟩
      have he : Bplus.edge j = T.edge t := by
        rw [← hBT.2.2 j]
        rfl
      have hinc : TreeIncidentEdge Bplus (Bplus.edge j) := by
        obtain ⟨i, hi⟩ := Bplus.attaches j
        refine ⟨Bplus.vertex j.succ, ?_, ?_⟩
        · simp [TreeSequenceVertexSet]
        · change Bplus.vertex j.succ ∈ G.ends (Bplus.edge j)
          rw [hi]
          exact Sym2.mem_mk_left _ _
      simpa [he] using hincident (Bplus.edge j) hinc
    · have ht' : t = D.lastEdgeIndex := by
        apply Fin.ext
        have hp := D.lastEdgePosition
        omega
      simpa [ht'] using hlast
  obtain ⟨oldETT, oldMP, oldRung, oldSeries, oldBase, oldCore,
    oldClosure, oldSupport, oldH, oldCount, oldStages, oldDividers,
    oldGood, oldColors⟩ := GoodHierarchyTerminalPrefixRepackage G k e0 input
      T phi phi ett C.maximum base H C.good Bplus hAB hABstrict hBT
  obtain ⟨_, _, _, _, corr, newMP, newBase, newH, newGood,
    sameGood, _⟩ := HierarchyLEMStable G k e0 input Bplus phi sigma oldETT
      oldMP (by rw [oldRung]; exact C.positive)
      (by
        intro input' T' generating' lower hp hlt hm
        exact ctx.lowerRung lower hp (by omega) hm)
      oldBase oldH oldGood ctx.proper ctx.oneEdgeUncolored D.alpha beta hrecolor
  have hbeta := (TwoColorComponentSwapMissingBehavior G phi D.alpha beta hne
    ctx.proper (Sum.inl yp)).2.1 yp hroot D.alphaMissingTerminal
  refine ⟨hroot, ?_, hfixed, hstable, hbeta, ?_⟩
  · exact ⟨yp, by simp [yp, TreeSequenceVertexSet], hroot⟩
  · exact ⟨{
      belowFull := hBT
      penultimateLength := by change T.length = Bplus.length + 1; omega
      ladderBelow := hNB
      oldETT := oldETT
      oldMaximum := oldMP
      oldRung := oldRung
      oldSeries := oldSeries
      oldBase := oldBase
      oldCore := oldCore
      oldClosure := oldClosure
      oldSupport := oldSupport
      oldHierarchy := oldH
      oldCount := oldCount
      oldStages := oldStages
      oldDividers := oldDividers
      oldGood := oldGood
      oldColors := oldColors
      proper := hproper
      oneUncolored := hone
      invariant := hinv
      incidentFixed := hincident
      corresponding := corr
      maximum := newMP
      newBase := newBase
      newHierarchy := newH
      newGood := newGood
      sameGood := sameGood }⟩

end GoldbergSeymour

end
