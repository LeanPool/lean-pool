/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyMeasures
public import LeanPool.GoldbergSeymour.TerminalStoredColors
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeNormalizedData
public import LeanPool.GoldbergSeymour.TreeColoringInvariant
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# P2752_T2_Normalized Datum

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2752_T2_NormalizedDatum {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx)
    (beta : Fin k)
    (hmissing : beta ∈ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)))
    (hunused : ∀ t : Fin T.length,
      (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length
        ≤ t.val → phi (T.edge t) ≠ some beta)
    (halternative :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Dn := TashkinovStoredColors ett.series.data n
      let Dnq := HierarchyStoredColorsAt H q
      let Gamma := Dnq.biUnion (C.good.gamma q)
      let A := HierarchyStarredStage H q
      let tailUsed := (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ t : Fin T.length, A.length ≤ t.val ∧ phi (T.edge t) = some c
      (0 < H.dividerCount ∧ beta ∉ Dnq ∧ beta ∉ Gamma) ∨
        (H.dividerCount = 0 ∧ beta ∉ Dn ∧ beta ∉ Gamma) ∨
        (beta ∈ Dnq ∧ Disjoint (C.good.gamma q beta) tailUsed))
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (hfixed : ∀ t : Fin T.length, P.coloring (T.edge t) = phi (T.edge t))
    (hinvariant : TreeColoringInvariant
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) phi P.coloring)
    (hterminal : beta ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex)) :
    ∃ N : HierarchySituationTwoCaseThreeNormalizedData
        G k e0 P.corresponding.replacementInput T P.coloring
          P.corresponding.replacementETT P.replacementBase
          P.counterexample P.minimumContext,
      N.alpha = beta := by
  classical
  obtain ⟨hstar, hpath, _⟩ :=
    P2752_T2_HierarchyMeasures C.hierarchy P.counterexample.hierarchy P.sameGood.1
  have htail : HierarchyFullTailLength P.counterexample = HierarchyFullTailLength C := by
    unfold HierarchyFullTailLength
    dsimp only
    rw [← hstar]
  have hprefix : ∀ i : ℕ, HierarchyFullTailPrefix P.counterexample i =
      HierarchyFullTailPrefix C i := by
    intro i
    unfold HierarchyFullTailPrefix
    dsimp only
    simp only [← hstar]
  let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
  let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have hlenB : B.length = T.length - 2 := by
    have hp : 2 ≤ T.length - A.length := D.tailAtLeastTwo
    change min (A.length + (T.length - A.length - 2)) T.length = T.length - 2
    omega
  have hlenPlus : Bplus.length = T.length - 1 := by
    have hp : 2 ≤ T.length - A.length := D.tailAtLeastTwo
    change min (A.length + (T.length - A.length - 1)) T.length = T.length - 1
    omega
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, (fun _ => rfl), (fun _ => rfl)⟩
  have hplusT : TreeSequenceInitialSegment Bplus T :=
    ⟨Nat.min_le_right _ _, (fun _ => rfl), (fun _ => rfl)⟩
  have hBplus : TreeSequenceInitialSegment B Bplus := by
    have hle : B.length ≤ Bplus.length := by omega
    refine ⟨hle, ?_, ?_⟩
    · intro i
      rw [← hplusT.2.1 (Fin.castLE (Nat.succ_le_succ hle) i)]
      convert hBT.2.1 i using 1
      congr 1
    · intro i
      rw [← hplusT.2.2 (Fin.castLE hle i)]
      convert hBT.2.2 i using 1
      congr 1
  have hmissingNew : beta ∈ TreeMissingColors P.coloring B := by
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissing
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [hinvariant.2 v (TreeSequenceInitialSegmentVertexSetSubset hBplus hv)]
    exact hm
  obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hmissingNew
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
  obtain ⟨j, hj⟩ := hv
  let earlier : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ hBT.1) j
  have hearlier : T.vertex earlier = v := (hBT.2.1 j).trans hj
  have hearlierBefore : earlier.val < D.penultimateVertexIndex.val := by
    have hjbound : j.val ≤ T.length - 2 := by
      rw [← hlenB]
      exact Nat.le_of_lt_succ j.isLt
    have hT : 2 ≤ T.length :=
      le_trans D.tailAtLeastTwo (Nat.sub_le T.length A.length)
    have numeric {a b c : ℕ} (ha : a ≤ c - 2) (hc : 2 ≤ c)
        (hb : b + 1 = c) : a < b := by omega
    change j.val < D.penultimateVertexIndex.val
    exact numeric hjbound hT D.penultimateVertexPosition
  have hraw := P2752_T2_TerminalStoredColors ett P.corresponding
  obtain ⟨hcount, hcolors⟩ := P.sameGood.2
  have hlast : Fin.cast (congrArg (fun q : ℕ => q + 1) hcount)
      (Fin.last C.hierarchy.dividerCount) =
      Fin.last P.counterexample.hierarchy.dividerCount := by
    apply Fin.ext
    exact hcount
  have hstored : HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
      HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) := by
    simpa only [hlast] using (hcolors (Fin.last C.hierarchy.dividerCount)).1
  have hgamma : ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount),
      C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
        P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta := by
    simpa only [hlast] using (hcolors (Fin.last C.hierarchy.dividerCount)).2
  have hGamma :
      (HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount)).biUnion
          (C.good.gamma (Fin.last C.hierarchy.dividerCount)) =
      (HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)).biUnion
          (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)) := by
    rw [← hstored]
    exact Finset.biUnion_congr rfl hgamma
  have hused :
      (Finset.univ : Finset (Fin k)).filter (fun c =>
        ∃ t : Fin T.length, A.length ≤ t.val ∧ phi (T.edge t) = some c) =
      (Finset.univ : Finset (Fin k)).filter (fun c =>
        ∃ t : Fin T.length,
          (HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount)).length ≤ t.val ∧
          P.coloring (T.edge t) = some c) := by
    apply Finset.filter_congr
    intro c _
    simp only [← hstar, hfixed, A]
  refine ⟨{
    toHierarchySituationTwoCaseThreeData := {
      toHierarchySituationTwoCommonTailData := {
        tailAtLeastTwo := by rw [htail]; exact D.tailAtLeastTwo
        pathNumberFull := by rw [← hpath, htail]; exact D.pathNumberFull
        lastEdgeIndex := D.lastEdgeIndex
        penultimateVertexIndex := D.penultimateVertexIndex
        terminalVertexIndex := D.terminalVertexIndex
        lastEdgePosition := D.lastEdgePosition
        penultimateVertexPosition := D.penultimateVertexPosition
        terminalVertexPosition := D.terminalVertexPosition
        lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
        theta := D.theta
        thetaOnLastEdge := (hfixed D.lastEdgeIndex).trans D.thetaOnLastEdge }
      alpha := beta
      alphaMissingTerminal := hterminal
      earlierVertexIndex := earlier
      earlierVertexBeforePenultimate := hearlierBefore
      alphaMissingEarlier := by rw [hearlier]; exact hm }
    alphaMissingTwoBefore := by
      change beta ∈ TreeMissingColors P.coloring
        (HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 2))
      rw [htail, hprefix]
      exact hmissingNew
    alphaUnusedOnFullTail := ?_
    normalizedAlternative := ?_ }, rfl⟩
  · dsimp only
    intro t ht
    rw [hfixed t]
    apply hunused t
    simpa only [hstar] using ht
  · dsimp only
    rcases halternative with h | h | h
    · exact Or.inl ⟨by simpa only [← hcount] using h.1,
        by simpa only [← hstored] using h.2.1,
        by simpa only [← hGamma] using h.2.2⟩
    · exact Or.inr (Or.inl ⟨by simpa only [← hcount] using h.1,
        by simpa only [hraw] using h.2.1,
        by simpa only [← hGamma] using h.2.2⟩)
    · refine Or.inr (Or.inr ⟨by simpa only [← hstored] using h.1, ?_⟩)
      simpa only [← hgamma beta h.1, ← hused] using h.2

end GoldbergSeymour

end
