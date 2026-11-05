/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.EligibleIndexBoundPreparation

/-!
# Hierarchy Situation Three Eligible Index Bound

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

namespace EligibleIndexBound

/-- Typed data construction shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperGoodS3640.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq V] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (base : HierarchyBase ett phi) →
  (C : HierarchyCounterexample base) →
  (ctx :
      HierarchyMinimumCounterexampleContext G k e0 input T phi ett
        base C) →
  (P :
      HierarchyReplacementPresentation G k e0 input T phi ett
        base C ctx) →
  (alpha : Fin k) →
  let old : HierarchyCounterexample P.replacementBase :=
    P.counterexample;
  let H :
    TashkinovHierarchy P.corresponding.replacementETT
      P.replacementBase :=
    old.hierarchy;
  let n :
    Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree
      n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  HierarchyPathNumber H = HierarchyPathNumber C.hierarchy →
  (hlenT : (3 : ℕ) ≤ T.length) →
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  TreeSequenceInitialSegment Tn X →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦
    if e = f then some alpha else mu e;
  (∀ v ∈ TreeSequenceVertexSet X,
      MissingColors G sigma v =
        MissingColors G mu v) →
  (∀ (U : TreeSequence G e0),
      TreeSequenceVertexSet U ⊆
          TreeSequenceVertexSet X →
        TreeMissingColors sigma U =
          TreeMissingColors mu U) →
  (∀ (U : TreeSequence G e0),
      TreeSequenceVertexSet U ⊆
          TreeSequenceVertexSet X →
        ∀ (R : Finset (Fin k)),
          TreeColorSetMinusClosed G sigma U R ↔
            TreeColorSetMinusClosed G mu U R) →
  (positiveB :
      (1 : ℕ) ≤
        P.corresponding.replacementETT.rounds) →
  (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin
              (P.corresponding.replacementETT.rounds +
                (2 : ℕ))))
        B) →
  (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                by
                have :=
                  TreeSequence.positive T
                omega⟩ :
              Fin
                (P.corresponding.replacementETT.rounds +
                  (2 : ℕ)))).length <
        B.length) →
  (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last
            (P.corresponding.replacementETT.rounds +
              (1 : ℕ))))) →
  (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last
            P.corresponding.replacementETT.rounds)) →
  (baseB :
      HierarchyBase
        {
          rounds :=
            P.corresponding.replacementETT.rounds,
          roundsPositive := positiveB,
          series :=
            P.corresponding.replacementETT.series,
          abovePenultimate := aboveB,
          strictAbovePenultimate :=
            strictB,
          belowFinal := belowB,
          generatingColoring :=
            generatingB :
          ExtendedTashkinovTree G k e0
            P.corresponding.replacementInput
            B mu }
        mu) →
  (HB :
      TashkinovHierarchy
        {
          rounds :=
            P.corresponding.replacementETT.rounds,
          roundsPositive :=
            positiveB,
          series :=
            P.corresponding.replacementETT.series,
          abovePenultimate :=
            aboveB,
          strictAbovePenultimate :=
            strictB,
          belowFinal := belowB,
          generatingColoring :=
            generatingB :
          ExtendedTashkinovTree G k
            e0
            P.corresponding.replacementInput
            B mu }
        baseB) →
  GoodHierarchy HB →
  let EB :
    ExtendedTashkinovTree G k e0
      P.corresponding.replacementInput
      B mu :=
    {
      rounds :=
        P.corresponding.replacementETT.rounds,
      roundsPositive :=
        positiveB,
      series :=
        P.corresponding.replacementETT.series,
      abovePenultimate :=
        aboveB,
      strictAbovePenultimate :=
        strictB,
      belowFinal := belowB,
      generatingColoring :=
        generatingB :
      ExtendedTashkinovTree G k
        e0
        P.corresponding.replacementInput
        B mu };
  TreeSequenceVertexSet
        baseB.core ⊆
      TreeSequenceVertexSet X →
  (EB.series.data.kind
          (Fin.last
            EB.rounds) =
        some
          TashkinovExtensionKind.PE →
      TreeSequenceVertexSet
          baseB.closure ⊆
        TreeSequenceVertexSet
          X) →
  (corr :
      CorrespondingExtendedTashkinovTree
        G k e0 EB sigma B) →
  (bs :
      HierarchyBase
        corr.replacementETT
        sigma) →
  baseB.core = bs.core →
  ({
              rounds :=
                P.corresponding.replacementETT.rounds,
              roundsPositive :=
                positiveB,
              series :=
                P.corresponding.replacementETT.series,
              abovePenultimate :=
                aboveB,
              strictAbovePenultimate :=
                strictB,
              belowFinal :=
                belowB,
              generatingColoring :=
                generatingB :
              ExtendedTashkinovTree
                G k e0
                P.corresponding.replacementInput
                B
                mu }.series.data.kind
          (Fin.last
            {
                rounds :=
                  P.corresponding.replacementETT.rounds,
                roundsPositive :=
                  positiveB,
                series :=
                  P.corresponding.replacementETT.series,
                abovePenultimate :=
                  aboveB,
                strictAbovePenultimate :=
                  strictB,
                belowFinal :=
                  belowB,
                generatingColoring :=
                  generatingB :
                ExtendedTashkinovTree
                  G k
                  e0
                  P.corresponding.replacementInput
                  B
                  mu }.rounds) =
        some
          TashkinovExtensionKind.PE ↔
      corr.replacementETT.series.data.kind
          (Fin.last
            corr.replacementETT.rounds) =
        some
          TashkinovExtensionKind.PE) →
  ({
              rounds :=
                P.corresponding.replacementETT.rounds,
              roundsPositive :=
                positiveB,
              series :=
                P.corresponding.replacementETT.series,
              abovePenultimate :=
                aboveB,
              strictAbovePenultimate :=
                strictB,
              belowFinal :=
                belowB,
              generatingColoring :=
                generatingB :
              ExtendedTashkinovTree
                G k
                e0
                P.corresponding.replacementInput
                B
                mu }.series.data.kind
          (Fin.last
            {
                rounds :=
                  P.corresponding.replacementETT.rounds,
                roundsPositive :=
                  positiveB,
                series :=
                  P.corresponding.replacementETT.series,
                abovePenultimate :=
                  aboveB,
                strictAbovePenultimate :=
                  strictB,
                belowFinal :=
                  belowB,
                generatingColoring :=
                  generatingB :
                ExtendedTashkinovTree
                  G
                  k
                  e0
                  P.corresponding.replacementInput
                  B
                  mu }.rounds) =
        some
          TashkinovExtensionKind.PE →
      baseB.closure =
        bs.closure) →
  (baseStageK :
      HB.stage
          (0 :
            Fin
              (HB.dividerCount +
                (2 :
                  ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last
              corr.replacementETT.rounds).castSucc) →
  (terminalStageK :
      HB.stage
          (Fin.last
            (HB.dividerCount +
              (1 :
                ℕ))) =
        B) →
  (nestedK :
      ∀
        (j :
          Fin
            (HB.dividerCount +
              (1 :
                ℕ))),
        TreeSequenceInitialSegment
          (HB.stage
            j.castSucc)
          (HB.stage
            j.succ)) →
  (strictK :
      ∀
        (j :
          Fin
            (HB.dividerCount +
              (1 :
                ℕ))),
        (HB.stage
              j.castSucc).length <
          (HB.stage
              j.succ).length) →
  (coreInsideK :
      TreeSequenceInitialSegment
        bs.core
        (HB.stage
          (⟨(1 :
                ℕ),
              by
              have :=
                TreeSequence.positive
                  T
              have :=
                TreeSequence.positive
                  B
              omega⟩ :
            Fin
              (HB.dividerCount +
                (2 :
                  ℕ))))) →
  (positiveK :
      ∀
        (i :
          Fin
            HB.dividerCount),
        (1 :
            ℕ) ≤
          (↑(HB.dividerPosition
                i) :
            ℕ)) →
  (increasingK :
      ∀
        (i
          j :
          Fin
            HB.dividerCount),
        (↑i :
              ℕ) <
            (↑j :
              ℕ) →
          (↑(HB.dividerPosition
                  i) :
              ℕ) <
            (↑(HB.dividerPosition
                  j) :
              ℕ)) →
  (dividerStageK :
      ∀
        (i :
          Fin
            HB.dividerCount),
        HB.stage
            (⟨(↑i :
                    ℕ) +
                  (1 :
                    ℕ),
                by
                have :=
                  TreeSequence.positive
                    T
                have :=
                  TreeSequence.positive
                    B
                omega⟩ :
              Fin
                (HB.dividerCount +
                  (2 :
                    ℕ))) =
          TreeSequencePrefix
            B
            (↑(HB.dividerPosition
                  i) :
              ℕ)
            (positiveK
              i)
            (by
              have :=
                TreeSequence.positive
                  T
              have :=
                TreeSequence.positive
                  B
              omega)) →
  let
    KF :
    TashkinovHierarchy
      corr.replacementETT
      bs :=
    by
    exact
      @helperKF3658
        (@V)
        (@E)
        inferInstance
        inferInstance
        inferInstance
        inferInstance
        (@G)
        (@k)
        (@e0)
        (@input)
        (@T)
        (@phi)
        (@ett)
        (@base)
        (@C)
        (@ctx)
        (@P)
        (@alpha)
        (@hlenT)
        (@positiveB)
        (@aboveB)
        (@strictB)
        (@belowB)
        (@generatingB)
        (@baseB)
        (@HB)
        (@corr)
        (@bs)
        (@baseStageK)
        (@terminalStageK)
        (@nestedK)
        (@strictK)
        (@coreInsideK)
        (@positiveK)
        (@increasingK)
        (@dividerStageK)
  (∀
      (j :
        Fin
          (HB.dividerCount +
            (1 :
              ℕ))),
      HierarchyStarredStage
          KF
          j =
        HierarchyStarredStage
          HB
          j) →
  (∀
      (j :
        Fin
          (HB.dividerCount +
            (1 :
              ℕ))),
      TreeSequenceInitialSegment
        (HB.stage
          j.castSucc)
        X) →
  corr.replacementETT.series.data.tree
        (Fin.last
            corr.replacementETT.rounds).castSucc =
      Tn →
  (∀
      (j :
        Fin
          (HB.dividerCount +
            (1 :
              ℕ))),
      HierarchyStoredColorsAt
          KF
          j =
        HierarchyStoredColorsAt
          HB
          j) →
  (∀
      (j :
        Fin
          (HB.dividerCount +
            (1 :
              ℕ))),
      HierarchyStageMissingColors
          KF
          j =
        HierarchyStageMissingColors
          HB
          j) →
  (∀
      (j :
        Fin
          (HB.dividerCount +
            (1 :
              ℕ)))
      (c :
        Fin
          k),
      HierarchySegmentColors
          KF
          j
          c =
        HierarchySegmentColors
          HB
          j
          c) →
  GoodHierarchy
    KF := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H n Tn mu hp hlenT B X hTnX r f
      sigma missingFixed missingTree minusEq positiveB aboveB strictB belowB generatingB baseB HB
      goodB EB coreBX closureBX corr bs hcore hpe hclosure baseStageK terminalStageK nestedK
      strictK coreInsideK positiveK increasingK dividerStageK KF starredEq stageBX terminalTree
      storedEq stageMissingEq segmentEq
  exact {
    gamma := goodB.gamma
    twoColors := by
      intro j c hc
      exact goodB.twoColors j c (by rw [storedEq j] at hc; exact hc)
    avoidance := by
      intro j c hc
      rw [stageMissingEq j, segmentEq j c]
      exact goodB.avoidance j c (by rw [storedEq j] at hc; exact hc)
    disjointPairs := by
      intro j c d hc hd hne
      exact goodB.disjointPairs j c d (by rw [storedEq j] at hc; exact hc)
        (by rw [storedEq j] at hd; exact hd) hne
    uniqueRefresh := by
      apply helper_uniqueRefresh_4523 <;> assumption
    parallelBase := by
      apply helper_parallelBase_4547 <;> assumption
    minusClosed := by
      intro i
      change TreeColorSetMinusClosed G sigma (HB.stage i.succ.castSucc)
        ((HierarchyStoredColorsAt KF i.succ).biUnion (goodB.gamma i.castSucc))
      rw [storedEq i.succ, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBX i.succ))]
      exact goodB.minusClosed i }

end EligibleIndexBound

end GoldbergSeymour

end
