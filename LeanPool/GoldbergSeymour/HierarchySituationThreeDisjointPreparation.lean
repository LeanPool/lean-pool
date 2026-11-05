/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.SplitSwapPreparation
public import LeanPool.GoldbergSeymour.KempeOrientation
public import LeanPool.GoldbergSeymour.OutsidePrefixBranch
public import LeanPool.GoldbergSeymour.ConditionNineTransport
public import LeanPool.GoldbergSeymour.ThetaExclusion
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans
public import LeanPool.GoldbergSeymour.HierarchyMeasures
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTrans
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyTerminalPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyLEMStable
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyPathNumber
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchySituationThreeDisjointData
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloring
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.SameHierarchyStages
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoSplitTail
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceComponentSwap
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TreeColoringInvariant
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# Hierarchy Situation Three Disjoint Preparation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_reconstructed_188.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G P.coloring alpha beta (Sum.inl
        (T.vertex (Fin.last T.length))); P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx
        P alpha beta (TwoColorComponentSwap G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last
        T.length)))) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 P.corresponding.replacementETT sigma T),
        MaximumProperty corr.replacementETT ∧
    ∃ (newBase : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT newBase) (good : GoodHierarchy K), SameGoodHierarchy
        P.counterexample.good good := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
      P.counterexample.hierarchy
  let Tnq : TreeSequence G e0 :=
    H.stage
      (⟨H.dividerCount, by omega⟩ :
        Fin (H.dividerCount + (2 : ℕ)))
  let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount
  let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds
  let A : TreeSequence G e0 := HierarchyStarredStage H q
  let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc
  let Dn : Finset (Fin k) := TashkinovStoredColors m.series.data n
  let qualifies : Fin k → Fin k → Prop := fun (a b : Fin k) =>
    (0 : ℕ) < H.dividerCount ∧ a ∈ TreeMissingColors P.coloring Tnq ∨
      H.dividerCount = (0 : ℕ) ∧
        (a ∈ TreeMissingColors P.coloring Tn ∨ a ∈ TreeMissingColors P.coloring A ∧ a ∉ Dn
            ∧ b ∉ Dn)
  by_cases hc : qualifies alpha beta ∨ qualifies beta alpha
  · let X := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)
    have fixed : ∀ t : Fin T.length,
        (HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)).length ≤ t.val →
        t.val < X.length → sigma (T.edge t) = P.coloring (T.edge t) := by
      intro t _ ht
      exact S.fixedOnSplit t ht
    rcases hc with hc | hc
    · have changed := StableChangeCasesOneTwoSplitTail G k e0
        P.corresponding.replacementInput T P.coloring
        P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext alpha beta S.distinct S.oldMissingOnPenultimate
        (Sum.inl (T.vertex (Fin.last T.length))) S.path sigma S.swapped hc
        S.separatedAlpha X S.splitAboveStar.1 S.splitAboveStar.2
        S.splitInPenultimate fixed S.prefixRoute S.oldSuffix S.missingOnSplit
        S.penultimateMissing S.storedFirst S.gammaCutoff
      exact changed.2.2
    · obtain ⟨hgraph, hcomponents, hswaps, hpaths⟩ :=
        P2880_T1_KempeOrientation G P.coloring alpha beta S.distinct
      have hsigma : sigma = TwoColorComponentSwap G P.coloring beta alpha
          (Sum.inl (T.vertex (Fin.last T.length))) :=
        S.swapped.trans (hswaps _)
      have hpath : TwoColorPathComponent G P.coloring beta alpha
          (Sum.inl (T.vertex (Fin.last T.length))) := (hpaths _).mp S.path
      have hsep : Disjoint
          (TwoColorComponent G P.coloring beta alpha
            (Sum.inl (T.vertex (Fin.last T.length))))
          (TwoColorComponent G P.coloring beta alpha
            (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T beta)))) := by
        simpa only [← hcomponents] using S.separatedBeta
      have hcut :
          let H := P.counterexample.hierarchy
          let q := Fin.last H.dividerCount
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            (beta ∈ P.counterexample.good.gamma q eta ∨
              alpha ∈ P.counterexample.good.gamma q eta) →
            (HierarchyFirstMissingPosition P.coloring T eta).val ≤ X.length := by
        dsimp only
        intro eta heta hc
        exact S.gammaCutoff eta heta hc.symm
      have changed := StableChangeCasesOneTwoSplitTail G k e0
        P.corresponding.replacementInput T P.coloring
        P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext beta alpha (Ne.symm S.distinct)
        S.oldMissingOnPenultimate.symm
        (Sum.inl (T.vertex (Fin.last T.length))) hpath sigma hsigma hc
        hsep X S.splitAboveStar.1 S.splitAboveStar.2
        S.splitInPenultimate fixed S.prefixRoute S.oldSuffix S.missingOnSplit.symm
        S.penultimateMissing S.storedFirst hcut
      exact changed.2.2
  · exact P2880_T1_OutsidePrefixBranch G k e0 input T phi ett base C ctx P
      alpha beta sigma S hc

theorem HierarchySituationThreeDisjointPreparation
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
    (alpha beta : Fin k)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (halpha :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)) ∧
        alpha ∈ TreeMissingColors P.coloring B ∧
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          ∃ eta : Fin k, eta ∈ D ∧
            alpha ∈ P.counterexample.good.gamma q eta ∧
            (HierarchyFirstMissingPosition P.coloring T eta).val ≤
              B.length))
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
              tailUsedThroughJ))
    (hcomponentDisjoint :
      let j := HierarchyPathNumber C.hierarchy
      let X := HierarchyFullTailPrefix C (j - 1)
      let Q := TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))
      ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ Q) :
    Nonempty (HierarchySituationThreeDisjointData
      G k e0 input T phi ett base C ctx P alpha beta) := by
  classical
  let sigma := TwoColorComponentSwap G P.coloring alpha beta
    (Sum.inl (T.vertex (Fin.last T.length)))
  obtain ⟨S⟩ := P2880_T1_CommonPreparation G k e0 input T phi ett base C ctx P
    alpha beta hpathLower hpathUpper halpha hbeta hcomponentDisjoint
  let H := P.counterexample.hierarchy
  let q := Fin.last H.dividerCount
  let m := P.corresponding.replacementETT
  let n := Fin.last m.rounds
  let A := HierarchyStarredStage H q
  let Tnq := H.stage ⟨H.dividerCount, by omega⟩
  let Tn := m.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors m.series.data n
  let qualifies := fun (a b : Fin k) =>
    (0 < H.dividerCount ∧ a ∈ TreeMissingColors P.coloring Tnq) ∨
    (H.dividerCount = 0 ∧
      (a ∈ TreeMissingColors P.coloring Tn ∨
        (a ∈ TreeMissingColors P.coloring A ∧ a ∉ Dn ∧ b ∉ Dn)))
  have reconstructed :=
    @helper_reconstructed_188 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base C ctx P alpha beta S
  obtain ⟨corr, hmaximum, newBase, K, good, hsame⟩ := reconstructed
  have hnotElementary : ¬ ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet T) := by
    as_aux_lemma =>
      obtain ⟨v, hvB, hmissing⟩ := Finset.mem_biUnion.mp S.missingTwoBefore.2
      have hvX := TreeSequenceInitialSegmentVertexSetSubset S.twoBeforeInSplit hvB
      have hvT := TreeSequenceInitialSegmentVertexSetSubset S.splitInFull hvX
      have hroot : Sum.inl (T.vertex (Fin.last T.length)) ∈
          TwoColorComponent G P.coloring alpha beta
            (Sum.inl (T.vertex (Fin.last T.length))) := rfl
      have hne : v ≠ T.vertex (Fin.last T.length) := by
        intro heq
        exact S.splitOutside v hvX (heq.symm ▸ hroot)
      intro helementary
      have hd := helementary hvT
        (by
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨Fin.last T.length, rfl⟩) hne
      exact Finset.disjoint_left.mp hd hmissing S.missingTerminal
  let newC : HierarchyCounterexample newBase := {
    positive := by rw [corr.rungAgreement]; exact P.counterexample.positive
    hierarchy := K
    good := good
    maximum := hmaximum
    notElementary := hnotElementary }
  obtain ⟨R, hR⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx P sigma corr newBase newC hsame
  obtain ⟨hbetaOutside, hnine⟩ := P2880_T1_ConditionNineTransport G k e0
    input T phi ett base C ctx P alpha beta sigma S R hR hbeta
  obtain ⟨hstar, _, _⟩ := P2752_T2_HierarchyMeasures C.hierarchy
    R.counterexample.hierarchy R.sameGood.1
  have htail : HierarchyFullTailLength R.counterexample = HierarchyFullTailLength C := by
    unfold HierarchyFullTailLength
    dsimp only
    rw [← hstar]
  have hprefix : ∀ i : Nat, HierarchyFullTailPrefix R.counterexample i =
      HierarchyFullTailPrefix C i := by
    intro i
    unfold HierarchyFullTailPrefix
    dsimp only
    simp only [← hstar]
  let j := HierarchyPathNumber C.hierarchy
  let Y := HierarchyFullTailPrefix C j
  obtain ⟨theta, htheta⟩ := hvertexMissing R.coloring R.minimumContext.proper
    R.minimumContext.oneEdgeUncolored (Y.vertex (Fin.last Y.length))
  have hthetaOutside :
      theta ∉ (HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)).biUnion
          (R.counterexample.good.gamma
            (Fin.last R.counterexample.hierarchy.dividerCount)) := by
    apply P2880_T1_ThetaExclusion G k e0 R.corresponding.replacementInput T
      R.coloring R.corresponding.replacementETT R.replacementBase R.counterexample
      R.minimumContext j (by dsimp [j]; omega)
      (by rw [htail]; exact hpathUpper)
    rw [hprefix j]
    exact htheta
  refine ⟨{
    switched := R
    switchedColoring := hR.trans S.swapped
    proper := R.minimumContext.proper
    oneEdgeUncolored := R.minimumContext.oneEdgeUncolored
    invariantOnSplit := ?_
    affectedMissingOnSplit := ?_
    transportedSuffix := ?_
    betaMissingTerminal := ?_
    betaMissingTwoBeforeWitness := ?_
    betaOutsideGamma := hbetaOutside
    conditionNine := hnine
    theta := theta
    thetaMissingAtJ := htheta
    thetaOutsideGamma := hthetaOutside }⟩
  · rw [hR]
    exact S.invariant
  · rw [hR]
    exact S.missingOnSplit
  · rw [hR]
    exact S.newSuffix
  · rw [hR]
    exact S.missingTerminal
  · apply Finset.mem_biUnion.mp
    rw [hR]
    exact S.missingTwoBefore.2

end GoldbergSeymour

end
