/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData

public import LeanPool.GoldbergSeymour.SplitSwapData
public import LeanPool.GoldbergSeymour.HierarchyMeasures
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# P2880_T1_Condition Nine Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2880_T1_ConditionNineTransport
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k) (sigma : PartialEdgeColoring E k)
    (S : P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx P
      alpha beta sigma)
    (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (hR : R.coloring = sigma)
    (hbeta :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let j := HierarchyPathNumber C.hierarchy
      let A := HierarchyStarredStage H q
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      let tailUsedThroughJ :=
        (Finset.univ : Finset (Fin k)).filter fun c =>
          ∃ r : Fin T.length,
            A.length ≤ r.val ∧ r.val < A.length + j ∧
              P.coloring (T.edge r) = some c
      beta ≠ alpha ∧
        beta ∈ TreeMissingColors P.coloring B ∧
        beta ∉ Gamma ∧ beta ∉ tailUsedThroughJ ∧
        (beta ∉ baseExtraMissing ∪ D ∨
          beta ∈ D ∧
            Disjoint (P.counterexample.good.gamma q beta ∪ {beta})
              tailUsedThroughJ)) :
    let H := R.counterexample.hierarchy
    let q := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let j := HierarchyPathNumber C.hierarchy
    let B := HierarchyFullTailPrefix C (j - 2)
    let n := Fin.last R.corresponding.replacementETT.rounds
    let Tn := R.corresponding.replacementETT.series.data.tree n.castSucc
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (R.counterexample.good.gamma q)
    let baseExtraMissing :=
      ((TreeSequenceVertexSet R.replacementBase.core \
        TreeSequenceVertexSet Tn).biUnion fun v => MissingColors G R.coloring v)
    let tailUsedThroughJ :=
      (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ r : Fin T.length, A.length ≤ r.val ∧ r.val < A.length + j ∧
          R.coloring (T.edge r) = some c
    beta ∉ Gamma ∧
      ((beta ∉ baseExtraMissing ∧ beta ∉ tailUsedThroughJ ∧
          beta ∉ Gamma ∧ beta ∉ D) ∨
        (beta ∈ D ∧ beta ∈ TreeMissingColors R.coloring B ∧
          Disjoint (R.counterexample.good.gamma q beta ∪ {beta})
            tailUsedThroughJ)) := by
  classical
  dsimp only
  have terminalLadder {inp gen nu : PartialEdgeColoring E k}
      (original : ExtendedTashkinovTree G k e0 inp T gen)
      (corr : CorrespondingExtendedTashkinovTree G k e0 original nu T) :
      corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        original.series.data.tree (Fin.last original.rounds).castSucc := by
    exact corr.terminalData.1
  have hterminal :
      R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc =
        P.corresponding.replacementETT.series.data.tree
          (Fin.last P.corresponding.replacementETT.rounds).castSucc :=
    (terminalLadder ett R.corresponding).trans (terminalLadder ett P.corresponding).symm
  have hcore : P.replacementBase.core = R.replacementBase.core :=
    P.sameGood.1.1.symm.trans R.sameGood.1.1
  obtain ⟨hstarP, _, _⟩ := P2752_T2_HierarchyMeasures C.hierarchy
    P.counterexample.hierarchy P.sameGood.1
  obtain ⟨hstarR, _, _⟩ := P2752_T2_HierarchyMeasures C.hierarchy
    R.counterexample.hierarchy R.sameGood.1
  have hstar :
      HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) =
        HierarchyStarredStage R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount) :=
    hstarP.symm.trans hstarR
  have lastColors (U : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx) :
      HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStoredColorsAt U.counterexample.hierarchy
          (Fin.last U.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
        C.good.gamma (Fin.last C.hierarchy.dividerCount) eta =
          U.counterexample.good.gamma
            (Fin.last U.counterexample.hierarchy.dividerCount) eta := by
    obtain ⟨hc, hcolors⟩ := U.sameGood.2
    have hlast : Fin.cast (congrArg (fun n : Nat => n + 1) hc)
        (Fin.last C.hierarchy.dividerCount) =
        Fin.last U.counterexample.hierarchy.dividerCount := Fin.ext hc
    simpa only [hlast] using hcolors (Fin.last C.hierarchy.dividerCount)
  have colorsP := lastColors P
  have colorsR := lastColors R
  have hstored :
      HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) =
        HierarchyStoredColorsAt R.counterexample.hierarchy
          (Fin.last R.counterexample.hierarchy.dividerCount) :=
    colorsP.1.symm.trans colorsR.1
  have hgamma : ∀ eta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount),
      P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta =
        R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta := by
    intro eta heta
    have ho : eta ∈ HierarchyStoredColorsAt C.hierarchy
        (Fin.last C.hierarchy.dividerCount) := colorsP.1.symm ▸ heta
    exact (colorsP.2 eta ho).symm.trans (colorsR.2 eta ho)
  have hGamma :
      (HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)).biUnion
          (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)) =
      (HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)).biUnion
          (R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount)) :=
    Finset.biUnion_congr hstored hgamma
  have hbaseMissing :
      ((TreeSequenceVertexSet R.replacementBase.core \
          TreeSequenceVertexSet (R.corresponding.replacementETT.series.data.tree
            (Fin.last R.corresponding.replacementETT.rounds).castSucc)).biUnion
        fun v => MissingColors G R.coloring v) =
      ((TreeSequenceVertexSet P.replacementBase.core \
          TreeSequenceVertexSet (P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc)).biUnion
        fun v => MissingColors G P.coloring v) := by
    rw [← hcore, hterminal]
    apply Finset.biUnion_congr rfl
    intro v hv
    rw [hR]
    exact S.invariant.2 v (TreeSequenceInitialSegmentVertexSetSubset
      S.coreInSplit (Finset.mem_sdiff.mp hv).1)
  have hused :
      (Finset.univ : Finset (Fin k)).filter (fun c =>
        ∃ r : Fin T.length,
          (HierarchyStarredStage R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount)).length ≤ r.val ∧
          r.val < (HierarchyStarredStage R.counterexample.hierarchy
            (Fin.last R.counterexample.hierarchy.dividerCount)).length +
              HierarchyPathNumber C.hierarchy ∧ R.coloring (T.edge r) = some c) =
      (Finset.univ : Finset (Fin k)).filter (fun c =>
        ∃ r : Fin T.length,
          (HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount)).length ≤ r.val ∧
          r.val < (HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount)).length +
              HierarchyPathNumber C.hierarchy ∧ P.coloring (T.edge r) = some c) := by
    rw [← hstar, hR]
    apply Finset.filter_congr
    intro c _
    constructor
    · rintro ⟨r, hlo, hhi, hcolor⟩
      exact ⟨r, hlo, hhi, (S.fixedThroughJ r hlo hhi).symm.trans hcolor⟩
    · rintro ⟨r, hlo, hhi, hcolor⟩
      exact ⟨r, hlo, hhi, (S.fixedThroughJ r hlo hhi).trans hcolor⟩
  rcases hbeta with ⟨_, _, hnotGamma, hnotUsed, hchoice⟩
  have hnotGammaR := hGamma ▸ hnotGamma
  refine ⟨hnotGammaR, ?_⟩
  rcases hchoice with hout | ⟨hD, hpair⟩
  · simp only [Finset.mem_union, not_or] at hout
    refine Or.inl ⟨?_, ?_, hnotGammaR, ?_⟩
    · rw [hbaseMissing]
      exact hout.1
    · rw [hused]
      exact hnotUsed
    · rw [← hstored]
      exact hout.2
  · refine Or.inr ⟨hstored ▸ hD, ?_, ?_⟩
    · rw [hR]
      exact S.missingTwoBefore.2
    · rw [← hgamma beta hD, hused]
      exact hpair

end GoldbergSeymour

end
