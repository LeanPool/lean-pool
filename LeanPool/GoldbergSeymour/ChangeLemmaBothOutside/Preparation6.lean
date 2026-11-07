/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyPathNumberPrefix
public import LeanPool.GoldbergSeymour.ChangeLemmaBothOutside.Preparation1
public import LeanPool.GoldbergSeymour.GoodHierarchyTerminalPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyFieldTransport
public import LeanPool.GoldbergSeymour.SharedFacts.MixedChangeTransport.Preparation2

/-!
# ChangeLemmaBothOutside: supporting constructions, part 6

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.ChangeLemmaBothOutsidePreparation

/-- Typed data construction shared by the outside change lemma proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperGoodS6400.{u_1, u_2} :
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
  (alpha beta : Fin k) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) :=
    Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 :=
    ett.series.data.tree n.castSucc;
  let ib : Fin (T.length + (1 : ℕ)) :=
    HierarchyFirstMissingPosition phi T beta;
  let vb : V := T.vertex ib;
  (coreToA : TreeSequenceInitialSegment base.core A) →
  (TnToA : TreeSequenceInitialSegment Tn A) →
  (hAib : A.length < (↑ib : ℕ)) →
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (↑ib : ℕ) (by omega)
      (by omega);
  (rpB : (1 : ℕ) ≤ ett.rounds) →
  (aboveB :
      TreeSequenceInitialSegment
        (ett.series.data.tree
          (⟨ett.rounds, by omega⟩ :
            Fin (ett.rounds + (2 : ℕ))))
        B) →
  (strictB :
      (ett.series.data.tree
            (⟨ett.rounds, by omega⟩ :
              Fin (ett.rounds + (2 : ℕ)))).length <
        B.length) →
  (belowB :
      TreeSequenceInitialSegment B
        (ett.series.data.tree
          (Fin.last (ett.rounds + (1 : ℕ))))) →
  (genB :
      phi =
        ett.series.data.coloring
          (Fin.last ett.rounds)) →
  (baseB :
      HierarchyBase
        { rounds := ett.rounds,
          roundsPositive := rpB,
          series := ett.series,
          abovePenultimate := aboveB,
          strictAbovePenultimate := strictB,
          belowFinal := belowB,
          generatingColoring := genB :
          ExtendedTashkinovTree G k e0 input B
            phi }
        phi) →
  (hcoreB : baseB.core = base.core) →
  let ettB :
    ExtendedTashkinovTree G k e0 input B
      phi :=
    { rounds := ett.rounds,
      roundsPositive := rpB,
      series := ett.series,
      abovePenultimate := aboveB,
      strictAbovePenultimate := strictB,
      belowFinal := belowB,
      generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B
        phi };
  let sigma : PartialEdgeColoring E k :=
    TwoColorComponentSwap G phi alpha beta
      (Sum.inl vb);
  (treeMissingEq :
      ∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆
            TreeSequenceVertexSet A →
          TreeMissingColors sigma S =
            TreeMissingColors phi S) →
  (corr :
      CorrespondingExtendedTashkinovTree
        G k e0 ettB sigma B) →
  (baseS :
      HierarchyBase
        corr.replacementETT sigma) →
  (closureBToA :
      ∀
        (_ :
          ett.series.data.kind n =
            some
              TashkinovExtensionKind.PE),
        TreeSequenceVertexSet
            baseB.closure ⊆
          TreeSequenceVertexSet A) →
  (minusEq :
      ∀ (S : TreeSequence G e0)
        (_ :
          TreeSequenceVertexSet
              S ⊆
            TreeSequenceVertexSet
              A)
        (D : Finset (Fin k)),
        TreeColorSetMinusClosed G
            sigma S D ↔
          TreeColorSetMinusClosed
            G phi S D) →
  (count : ℕ) →
  (stages :
      Fin (count + (2 : ℕ)) →
        TreeSequence G e0) →
  (hbbase :
      stages
          (0 :
            Fin
              (count +
                (2 : ℕ))) =
        {
              rounds :=
                ett.rounds,
              roundsPositive :=
                rpB,
              series :=
                ett.series,
              abovePenultimate :=
                aboveB,
              strictAbovePenultimate :=
                strictB,
              belowFinal :=
                belowB,
              generatingColoring :=
                genB :
              ExtendedTashkinovTree
                G k e0 input
                B
                phi }.series.data.tree
          (Fin.last
              {
                  rounds :=
                    ett.rounds,
                  roundsPositive :=
                    rpB,
                  series :=
                    ett.series,
                  abovePenultimate :=
                    aboveB,
                  strictAbovePenultimate :=
                    strictB,
                  belowFinal :=
                    belowB,
                  generatingColoring :=
                    genB :
                  ExtendedTashkinovTree
                    G k e0
                    input B
                    phi }.rounds).castSucc) →
  (hbterminal :
      stages
          (Fin.last
            (count +
              (1 : ℕ))) =
        B) →
  (hbnested :
      ∀
        (j :
          Fin
            (count +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          (stages
            j.castSucc)
          (stages
            j.succ)) →
  (hbstrict :
      ∀
        (j :
          Fin
            (count +
              (1 :
                ℕ))),
        (stages
              j.castSucc).length <
          (stages
              j.succ).length) →
  (positions :
      Fin count →
        Fin
          (B.length +
            (1 :
              ℕ))) →
  (hbpositive :
      ∀
        (i :
          Fin
            count),
        (1 : ℕ) ≤
          (↑(positions
                i) :
            ℕ)) →
  (hbincreasing :
      ∀
        (i j :
          Fin
            count),
        (↑i :
              ℕ) <
            (↑j :
              ℕ) →
          (↑(positions
                  i) :
              ℕ) <
            (↑(positions
                  j) :
              ℕ)) →
  (hbdivider :
      ∀
        (i :
          Fin
            count),
        stages
            (⟨(↑i :
                    ℕ) +
                  (1 :
                    ℕ),
                by
                omega⟩ :
              Fin
                (count +
                  (2 :
                    ℕ))) =
          TreeSequencePrefix
            B
            (↑(positions
                  i) :
              ℕ)
            (hbpositive
              i)
            (Nat.le_of_lt_succ
              (positions
                  i).isLt)) →
  (hbcore :
      TreeSequenceInitialSegment
        baseB.core
        (stages
          (⟨(1 :
                ℕ),
              by
              omega⟩ :
            Fin
              (count +
                (2 :
                  ℕ))))) →
  (goodB :
      GoodHierarchy
        {
          dividerCount :=
            count,
          stage :=
            stages,
          baseStage :=
            hbbase,
          terminalStage :=
            hbterminal,
          nested :=
            hbnested,
          strict :=
            hbstrict,
          dividerPosition :=
            positions,
          dividerPositive :=
            hbpositive,
          dividerIncreasing :=
            hbincreasing,
          dividerStage :=
            hbdivider,
          coreInsideFirst :=
            hbcore :
          TashkinovHierarchy
            {
              rounds :=
                ett.rounds,
              roundsPositive :=
                rpB,
              series :=
                ett.series,
              abovePenultimate :=
                aboveB,
              strictAbovePenultimate :=
                strictB,
              belowFinal :=
                belowB,
              generatingColoring :=
                genB :
              ExtendedTashkinovTree
                G
                k
                e0
                input
                B
                phi }
            baseB }) →
  (stageBToA :
      ∀
        (j :
          Fin
            ({
                  dividerCount :=
                    count,
                  stage :=
                    stages,
                  baseStage :=
                    hbbase,
                  terminalStage :=
                    hbterminal,
                  nested :=
                    hbnested,
                  strict :=
                    hbstrict,
                  dividerPosition :=
                    positions,
                  dividerPositive :=
                    hbpositive,
                  dividerIncreasing :=
                    hbincreasing,
                  dividerStage :=
                    hbdivider,
                  coreInsideFirst :=
                    hbcore :
                  TashkinovHierarchy
                    {
                      rounds :=
                        ett.rounds,
                      roundsPositive :=
                        rpB,
                      series :=
                        ett.series,
                      abovePenultimate :=
                        aboveB,
                      strictAbovePenultimate :=
                        strictB,
                      belowFinal :=
                        belowB,
                      generatingColoring :=
                        genB :
                      ExtendedTashkinovTree
                        G
                        k
                        e0
                        input
                        B
                        phi }
                    baseB }.dividerCount +
              (1 :
                ℕ))),
        TreeSequenceInitialSegment
          ({
                dividerCount :=
                  count,
                stage :=
                  stages,
                baseStage :=
                  hbbase,
                terminalStage :=
                  hbterminal,
                nested :=
                  hbnested,
                strict :=
                  hbstrict,
                dividerPosition :=
                  positions,
                dividerPositive :=
                  hbpositive,
                dividerIncreasing :=
                  hbincreasing,
                dividerStage :=
                  hbdivider,
                coreInsideFirst :=
                  hbcore :
                TashkinovHierarchy
                  {
                    rounds :=
                      ett.rounds,
                    roundsPositive :=
                      rpB,
                    series :=
                      ett.series,
                    abovePenultimate :=
                      aboveB,
                    strictAbovePenultimate :=
                      strictB,
                    belowFinal :=
                      belowB,
                    generatingColoring :=
                      genB :
                    ExtendedTashkinovTree
                      G
                      k
                      e0
                      input
                      B
                      phi }
                  baseB }.stage
            j.castSucc)
          A) →
  (hcore :
      baseB.core =
        baseS.core) →
  (hpe :
      {
                rounds :=
                  ett.rounds,
                roundsPositive :=
                  rpB,
                series :=
                  ett.series,
                abovePenultimate :=
                  aboveB,
                strictAbovePenultimate :=
                  strictB,
                belowFinal :=
                  belowB,
                generatingColoring :=
                  genB :
                ExtendedTashkinovTree
                  G
                  k
                  e0
                  input
                  B
                  phi }.series.data.kind
            (Fin.last
              {
                  rounds :=
                    ett.rounds,
                  roundsPositive :=
                    rpB,
                  series :=
                    ett.series,
                  abovePenultimate :=
                    aboveB,
                  strictAbovePenultimate :=
                    strictB,
                  belowFinal :=
                    belowB,
                  generatingColoring :=
                    genB :
                  ExtendedTashkinovTree
                    G
                    k
                    e0
                    input
                    B
                    phi }.rounds) =
          some
            TashkinovExtensionKind.PE ↔
        corr.replacementETT.series.data.kind
            (Fin.last
              corr.replacementETT.rounds) =
          some
            TashkinovExtensionKind.PE) →
  (hclosure :
      {
                rounds :=
                  ett.rounds,
                roundsPositive :=
                  rpB,
                series :=
                  ett.series,
                abovePenultimate :=
                  aboveB,
                strictAbovePenultimate :=
                  strictB,
                belowFinal :=
                  belowB,
                generatingColoring :=
                  genB :
                ExtendedTashkinovTree
                  G
                  k
                  e0
                  input
                  B
                  phi }.series.data.kind
            (Fin.last
              {
                  rounds :=
                    ett.rounds,
                  roundsPositive :=
                    rpB,
                  series :=
                    ett.series,
                  abovePenultimate :=
                    aboveB,
                  strictAbovePenultimate :=
                    strictB,
                  belowFinal :=
                    belowB,
                  generatingColoring :=
                    genB :
                  ExtendedTashkinovTree
                    G
                    k
                    e0
                    input
                    B
                    phi }.rounds) =
          some
            TashkinovExtensionKind.PE →
        baseB.closure =
          baseS.closure) →
  (positionsS :
      Fin
          count →
        Fin
          (B.length +
            (1 :
              ℕ))) →
  (hspositive :
      ∀
        (i :
          Fin
            count),
        (1 :
            ℕ) ≤
          (↑(positionsS
                i) :
            ℕ)) →
  (hsincreasing :
      ∀
        (i
          j :
          Fin
            count),
        (↑i :
              ℕ) <
            (↑j :
              ℕ) →
          (↑(positionsS
                  i) :
              ℕ) <
            (↑(positionsS
                  j) :
              ℕ)) →
  (hsbase :
      stages
          (0 :
            Fin
              (count +
                (2 :
                  ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last
              corr.replacementETT.rounds).castSucc) →
  (hsterminal :
      stages
          (Fin.last
            (count +
              (1 :
                ℕ))) =
        B) →
  (hsnested :
      ∀
        (j :
          Fin
            (count +
              (1 :
                ℕ))),
        TreeSequenceInitialSegment
          (stages
            j.castSucc)
          (stages
            j.succ)) →
  (hsstrict :
      ∀
        (j :
          Fin
            (count +
              (1 :
                ℕ))),
        (stages
              j.castSucc).length <
          (stages
              j.succ).length) →
  (hsdivider :
      ∀
        (i :
          Fin
            count),
        stages
            (⟨(↑i :
                    ℕ) +
                  (1 :
                    ℕ),
                by
                omega⟩ :
              Fin
                (count +
                  (2 :
                    ℕ))) =
          TreeSequencePrefix
            B
            (↑(positionsS
                  i) :
              ℕ)
            (hspositive
              i)
            (Nat.le_of_lt_succ
              (positionsS
                  i).isLt)) →
  (hscore :
      TreeSequenceInitialSegment
        baseS.core
        (stages
          (⟨(1 :
                ℕ),
              by
              omega⟩ :
            Fin
              (count +
                (2 :
                  ℕ))))) →
  let
    HB :
    TashkinovHierarchy
      ettB
      baseB :=
    {
      dividerCount :=
        count,
      stage :=
        stages,
      baseStage :=
        hbbase,
      terminalStage :=
        hbterminal,
      nested :=
        hbnested,
      strict :=
        hbstrict,
      dividerPosition :=
        positions,
      dividerPositive :=
        hbpositive,
      dividerIncreasing :=
        hbincreasing,
      dividerStage :=
        hbdivider,
      coreInsideFirst :=
        hbcore :
      TashkinovHierarchy
        ettB
        baseB };
  let
    HS :
    TashkinovHierarchy
      corr.replacementETT
      baseS :=
    {
      dividerCount :=
        count,
      stage :=
        stages,
      baseStage :=
        hsbase,
      terminalStage :=
        hsterminal,
      nested :=
        hsnested,
      strict :=
        hsstrict,
      dividerPosition :=
        positionsS,
      dividerPositive :=
        hspositive,
      dividerIncreasing :=
        hsincreasing,
      dividerStage :=
        hsdivider,
      coreInsideFirst :=
        hscore :
      TashkinovHierarchy
        corr.replacementETT
        baseS };
  (storedEq :
      ∀
        (j :
          Fin
            (count +
              (1 :
                ℕ))),
        HierarchyStoredColorsAt
            HS
            j =
          HierarchyStoredColorsAt
            HB
            j) →
  (missingEq :
      ∀
        (j :
          Fin
            (count +
              (1 :
                ℕ))),
        HierarchyStageMissingColors
            HS
            j =
          HierarchyStageMissingColors
            HB
            j) →
  (segmentEq :
      ∀
        (j :
          Fin
            (count +
              (1 :
                ℕ)))
        (eta :
          Fin
            k)
        (_ :
          eta ∈
            HierarchyStoredColorsAt
              HB
              j),
        HierarchySegmentColors
            HS
            j
            eta =
          HierarchySegmentColors
            HB
            j
            eta) →
  (refreshEq :
      ∀
        (i :
          Fin
            count),
        ((TreeSequenceVertexSet
                  (HS.stage
                    i.succ.castSucc) \
                TreeSequenceVertexSet
                  (HierarchyStarredStage
                    HS
                    i.castSucc)).biUnion
            fun
              (v :
                V) ↦
            MissingColors
              G
              sigma
              v) =
          (TreeSequenceVertexSet
                  (HB.stage
                    i.succ.castSucc) \
                TreeSequenceVertexSet
                  (HierarchyStarredStage
                    HB
                    i.castSucc)).biUnion
            fun
              (v :
                V) ↦
            MissingColors
              G
              phi
              v) →
  GoodHierarchy
    HS := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb coreToA TnToA hAib B
      rpB aboveB strictB belowB genB baseB hcoreB ettB sigma treeMissingEq corr baseS closureBToA
      minusEq count stages hbbase hbterminal hbnested hbstrict positions hbpositive hbincreasing
      hbdivider hbcore goodB stageBToA hcore hpe hclosure positionsS hspositive hsincreasing hsbase
      hsterminal hsnested hsstrict hsdivider hscore HB HS storedEq missingEq segmentEq refreshEq
  exact {
    gamma := goodB.gamma
    twoColors := by intro j eta he; exact goodB.twoColors j eta (storedEq j ▸ he)
    avoidance := by
      intro j eta he
      rw [missingEq, segmentEq j eta (storedEq j ▸ he)]
      exact goodB.avoidance j eta (storedEq j ▸ he)
    disjointPairs := by
      intro j eta theta he ht hne
      exact goodB.disjointPairs j eta theta (storedEq j ▸ he) (storedEq j ▸ ht) hne
    uniqueRefresh := by
      intro i
      simpa only [storedEq, refreshEq] using goodB.uniqueRefresh i
    parallelBase := by
      dsimp only
      intro hp
      have hpOld := hpe.mpr hp
      have hc := hclosure hpOld
      have htree : corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc = Tn := hsbase.symm.trans hbbase
      change ¬TreeColorSetMinusClosed G sigma baseS.core
          ((HierarchyStoredColorsAt HS 0).biUnion (goodB.gamma 0)) ∧
        4 ≤ ((TreeMissingColors sigma (corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc) ∩
          TreeMissingColors sigma baseS.closure) \
          (HierarchyStoredColorsAt HS 0).biUnion (goodB.gamma 0)).card
      rw [← hcore, ← hc, storedEq, htree,
        treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset TnToA),
        treeMissingEq _ (closureBToA hpOld),
        minusEq _ (by rw [hcoreB]; exact TreeSequenceInitialSegmentVertexSetSubset coreToA)]
      exact goodB.parallelBase hpOld
    minusClosed := by
      intro i
      rw [storedEq, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ))]
      exact goodB.minusClosed i }

theorem helper_continuation_4653.{u_1, u_2} :
    helperContinuation4653Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hminimal alpha beta hne H q
      A n Tn Dn ia ib vb ell yLength Y segRefl segTrans coreToA TnToA AToT ordinaryToA starredToA
      hElementaryY hb vertexY hbY hAia hAib halphaA hbetaA horder habIndex B BToT ABstrict
      BstrictT rpB aboveB strictB belowB genB hMPB baseB hcoreB HB hcountB hstagesB hdividersB
      goodB hgoodB ettB outsideStored hDn sigma behavior unaffected fixedValue sigmaProper
      sigmaOne missingBefore sigmaNotElementary missingA treeMissingEq stable stableTn TnToB
      TnStrictB notControlled terminalRoute
  have treeControlled (t : Fin Tn.length) :
      phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta := by
    exact @helper_treeControlled_1302 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hone) (@alpha)
        (@beta) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB)
        (@notControlled) (@t)
  have augmentationControlled (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S B) (t : Fin B.length)
      (ht : S.length ≤ t.val) :
      phi (B.edge t) ≠ some alpha ∧ phi (B.edge t) ≠ some beta := by
    exact @helper_augmentationControlled_5115 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@AToT) (@hElementaryY) (@hb) (@vertexY) (@hbY) (@hAib) (@halphaA) (@horder) (@BToT)
        (@BstrictT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB) (@S) (@hseq)
        (@t) (@ht)
  have allControlled (t : Fin B.length) :
      phi (B.edge t) ≠ some alpha ∧ phi (B.edge t) ≠ some beta := by
    exact @helper_allControlled_1331 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB) (@TnToB)
        (@terminalRoute) (@treeControlled) (@augmentationControlled) (@t)
  have edgesFixed (t : Fin B.length) : sigma (B.edge t) = phi (B.edge t) :=
    fixedValue _ (allControlled t).1 (allControlled t).2
  have routeTransport (S : TreeSequence G e0) (hs : TashkinovAugmentationSequence phi S B) :
      TashkinovAugmentationSequence sigma S B := by
    exact @helper_routeTransport_711 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@segTrans) (@hAib) (@BToT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
        (@HB) (@missingBefore) (@edgesFixed) (@S) (@hs)
  have replacement :
      ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B,
        MaximumProperty corr.replacementETT ∧
        ∃ baseS : HierarchyBase corr.replacementETT sigma,
          ∃ HS : TashkinovHierarchy corr.replacementETT baseS,
            SameHierarchyStages HB HS := by
    exact @helper_replacement_5138 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
        (@hlower) (@alpha) (@beta) (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB)
        (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@sigmaProper) (@sigmaOne) (@stable) (@stableTn)
        (@TnToB) (@TnStrictB) (@terminalRoute) (@routeTransport)
  obtain ⟨corr, hMPS, baseS, HS, hsame⟩ := replacement
  have storedS : TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) = Dn := by
    exact corr.terminalData.2.2
  have hrS : corr.replacementETT.rounds = ett.rounds := corr.rungAgreement
  have stageBToA (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HB.stage j.castSucc) A := by
    rw [(hstagesB j).1]
    exact ordinaryToA _
  have starBToA (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage HB j) A := by
    rw [(hstagesB j).2]
    exact starredToA _
  have stageBToB (j : Fin (HB.dividerCount + 2)) :
      TreeSequenceInitialSegment (HB.stage j) B := by
    exact Fin.reverseInduction
      (motive := fun j => TreeSequenceInitialSegment (HB.stage j) B)
      (by simpa only [HB.terminalStage] using segRefl B)
      (fun i hi => segTrans (HB.nested i) hi) j
  have closureBToA (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
    exact @helper_closureBToA_1398 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@hcoreB) (@hp)
  have minusEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) (D : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D := by
    exact @helper_minusEq_1405 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@halphaA) (@hbetaA) (@unaffected) (@treeMissingEq) (@S) (@hS) (@D)
  rcases HB with ⟨count, stages, hbbase, hbterminal, hbnested, hbstrict, positions,
    hbpositive, hbincreasing, hbdivider, hbcore⟩
  rcases HS with ⟨countS, stagesS, hsbase, hsterminal, hsnested, hsstrict, positionsS,
    hspositive, hsincreasing, hsdivider, hscore⟩
  rcases hsame with ⟨hcore, hcount, hstages, hpositions, hpe, hclosure⟩
  dsimp only at hcount hstages hpositions
  cases hcount
  have hstage : stages = stagesS := eq_of_heq hstages
  cases hstage
  let HB : TashkinovHierarchy ettB baseB :=
    ⟨count, stages, hbbase, hbterminal, hbnested, hbstrict, positions,
      hbpositive, hbincreasing, hbdivider, hbcore⟩
  let HS : TashkinovHierarchy corr.replacementETT baseS :=
    ⟨count, stages, hsbase, hsterminal, hsnested, hsstrict, positionsS,
      hspositive, hsincreasing, hsdivider, hscore⟩
  have starEq (j : Fin (count + 1)) :
      HierarchyStarredStage HS j = HierarchyStarredStage HB j := by
    exact Fin.cases hcore.symm (fun i => rfl) j
  have storedEq (j : Fin (count + 1)) :
      HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j := by
    exact HB.storedColors_eq_of_agreement HS j j storedS (starEq j)
      (treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (starBToA j)))
  have missingEq (j : Fin (count + 1)) :
      HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
    exact HB.stageMissingColors_eq_of_agreement HS j j rfl
      (treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBToA j)))
  -- Only stored colors require a transported first-missing cutoff.
  have firstEq (eta : Fin k) (he : eta ∈ Dn) :
      HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta := by
    exact @helper_firstEq_1458 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@hDn) (@behavior) (@eta) (@he)
  have segmentEq (j : Fin (count + 1)) (eta : Fin k)
      (he : eta ∈ HierarchyStoredColorsAt HB j) :
      HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
    apply HB.segmentColors_eq_of_agreement HS j j eta rfl (starEq j)
      (congrArg Fin.val (firstEq eta (Finset.mem_sdiff.mp he).1))
    intro index
    have initial := stageBToB j.succ
    have fixed := edgesFixed (Fin.castLE initial.1 index)
    rw [initial.2.2] at fixed
    exact fixed
  have refreshEq (i : Fin count) :
      ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
          fun v => MissingColors G sigma v) =
      ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
          fun v => MissingColors G phi v) := by
    exact HB.segmentMissingColors_eq_of_agreement HS i i rfl (starEq i.castSucc)
      (fun v hv => missingA v (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ)
        (Finset.mem_sdiff.mp hv).1))
  let goodS : GoodHierarchy HS := by
    exact @helperGoodS6400 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@coreToA) (@TnToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
        (@hcoreB) (@treeMissingEq) (@corr) (@baseS) (@closureBToA) (@minusEq) (@count) (@stages)
        (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions) (@hbpositive)
        (@hbincreasing) (@hbdivider) (@hbcore) (@goodB) (@stageBToA) (@hcore) (@hpe) (@hclosure)
        (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
        (@hsstrict) (@hsdivider) (@hscore) (@storedEq) (@missingEq) (@segmentEq) (@refreshEq)
  let CS : HierarchyCounterexample baseS :=
    { positive := by rw [hrS]; exact C.positive
      hierarchy := HS
      good := goodS
      maximum := hMPS
      notElementary := sigmaNotElementary }
  have hstarLast : HierarchyStarredStage HS (Fin.last count) = A := by
    exact (starEq _).trans
      (H.lastStarredStage_eq_of_agreement HB hcountB (fun j => (hstagesB j).2))
  have hlastOrd : HS.stage (Fin.last count).castSucc = H.stage q.castSucc := by
    have hs := (hstagesB (Fin.last count)).1
    have hj : Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB) (Fin.last count) = q :=
      Fin.ext (by simp [q])
    simpa only [hj] using hs
  -- Path candidates restrict to the shorter prefix; the second measure decreases strictly.
  have pathLe : HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
    exact H.pathNumber_le_of_prefix HS
      (congrArg (fun S : TreeSequence G e0 => S.length) hstarLast) BToT ABstrict
  have tailLess : B.length - (HS.stage (Fin.last count).castSucc).length <
      T.length - (H.stage q.castSucc).length := by
    rw [hlastOrd]
    have hlen := (ordinaryToA q).1
    omega
  have hless : HierarchyCounterexampleLess (HierarchyCounterexampleMeasure CS)
      (HierarchyCounterexampleMeasure C) := by
    change HierarchyPathNumber HS < HierarchyPathNumber H ∨
      (HierarchyPathNumber HS = HierarchyPathNumber H ∧
        B.length - (HS.stage (Fin.last count).castSucc).length <
          T.length - (H.stage q.castSucc).length)
    rcases lt_or_eq_of_le pathLe with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, tailLess⟩
  exact hminimal CS hrS hcountB hless

theorem helper_finish_4308.{u_1, u_2} :
    helperFinish4308Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hminimal alpha beta hne
      hmissingPrefix horderedUnused hlocation H q A n Tn Dn ia ib va vb ell yLength Y segRefl
      segTrans commonPrefix coreToA TnToA AToT ordinaryToA starredToA hmissingY hElementaryY ha
      hb vertexY haY hbY hout hAia hAib halphaA hbetaA horder habIndex havb B BToT AToB ABstrict
      BToY BstrictT rpB aboveB strictB belowB genB hMPB hsB baseB hcoreB hclosureB hsupportB HB
      hcountB hstagesB hdividersB goodB hgoodB ettB missingSubset outsideStored hDn
  by_contra hcomponents
  let K := TwoColorComponent G phi alpha beta (Sum.inl vb)
  let sigma := TwoColorComponentSwap G phi alpha beta (Sum.inl vb)
  have hdisjoint : Disjoint (TwoColorComponent G phi alpha beta (Sum.inl va)) K :=
    (TwoColorComponentsDisjoint G phi alpha beta (Sum.inl va) (Sum.inl vb)).resolve_left
      hcomponents
  have haK : Sum.inl va ∉ K := by
    intro h
    exact Set.disjoint_left.mp hdisjoint (show Sum.inl va ∈
      TwoColorComponent G phi alpha beta (Sum.inl va) from rfl) h
  have behavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper
    (Sum.inl vb)
  have edgeOfVertex {v : V} {f : E} (hv : Sum.inl v ∈ K)
      (hf : Incident G v f) (hc : phi f = some alpha ∨ phi f = some beta) :
      Sum.inr f ∈ K := by
    have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr f) (Sum.inl v) :=
      ⟨hf, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      sigma f = some c ↔ phi f = some c := by
    exact @helper_unaffected_1187 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@ha) (@hb) (@f) (@c) (@hca) (@hcb)
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    simp [sigma, TwoColorComponentSwap, ha, hb]
  have sigmaProper : IsProperEdgeColoring G sigma :=
    TwoColorComponentSwapProper G phi alpha beta hne hproper _
  have sigmaOne : IsOneEdgeUncolored sigma e0 := by
    exact @helper_sigmaOne_1202 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hone) (@alpha)
        (@beta) (@hne) (@ha) (@hb) (@unaffected)
  have vertexB (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
      T.vertex i ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haB : va ∈ TreeSequenceVertexSet B := vertexB ia (le_of_lt habIndex)
  have hbB : vb ∈ TreeSequenceVertexSet B := vertexB ib le_rfl
  -- Elementarity fixes missing sets before the swapped endpoint, even inside its component.
  have missingBefore (v : V) (hv : v ∈ TreeSequenceVertexSet B) (hvb : v ≠ vb) :
      MissingColors G sigma v = MissingColors G phi v := by
    exact @SharedFacts.MixedChangeTransport.notMissingBeforeFirstPosition (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@hElementaryY) (@ha) (@hb) (@haY) (@hbY) (@hAib) (@BToY) (@haK) (@behavior)
        (@edgeOfVertex) (@v) (@hv) (@hvb)
  have hnewa : alpha ∈ MissingColors G sigma va := by
    rw [behavior.1 va haK]
    exact ha.1
  have hnewb : alpha ∈ MissingColors G sigma vb :=
    behavior.2.2.1 vb (show Sum.inl vb ∈ K from rfl) hb.1
  have sigmaNotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) :=
    fun he => Finset.disjoint_left.mp (he haB hbB havb) hnewa hnewb
  have missingA (v : V) (hv : v ∈ TreeSequenceVertexSet A) :
      MissingColors G sigma v = MissingColors G phi v :=
    missingBefore v (TreeSequenceInitialSegmentVertexSetSubset AToB hv)
      (by intro he; exact hout.2 (he ▸ hv))
  have treeMissingEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) :
      TreeMissingColors sigma S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv => missingA v (hS hv))
  have stable (S : TreeSequence G e0) (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A)
      (D : Finset (Fin k)) (hD : alpha ∉ D ∧ beta ∉ D) :
      StableColoring S D phi sigma := by
    exact @helper_stable_1247 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@halphaA)
        (@hbetaA) (@unaffected) (@missingA) (@S) (@hS) (@D) (@hD)
  have stableTn : StableColoring Tn Dn phi sigma :=
    stable Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA) Dn hDn
  have TnToB := segTrans TnToA AToB
  have TnStrictB : Tn.length < B.length := lt_of_le_of_lt TnToA.1 ABstrict
  have BToFinal := segTrans BToT ett.belowFinal
  have notControlled (c : Fin k) (hc : c = alpha ∨ c = beta) :
      c ∉ TreeMissingColors phi Tn ∪ Dn := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases hc with rfl | rfl
      · exact halphaA (missingSubset TnToA hm)
      · exact hbetaA (missingSubset TnToA hm)
    · rcases hc with rfl | rfl
      · exact hDn.1 hm
      · exact hDn.2 hm
  have storedOrMissing (c : Fin k) (hc : c ∈ ett.series.data.stored n) :
      c ∈ TreeMissingColors phi Tn ∪ Dn := by
    exact @helper_storedOrMissing_1276 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB) (@c) (@hc)
  -- Nonparallel extensions retain the certified connecting edge and one-edge seed.
  have terminalRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn B) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence phi seed B ∧
          phi f ≠ some alpha ∧ phi f ≠ some beta) := by
    exact @helper_terminalRoute_532 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@commonPrefix) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB)
        (@TnToB) (@TnStrictB) (@BToFinal) (@notControlled) (@storedOrMissing)
  exact @helper_continuation_4653 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@hminimal) (@alpha) (@beta) (@hne) (@segRefl) (@segTrans) (@coreToA) (@TnToA)
      (@AToT) (@ordinaryToA) (@starredToA) (@hElementaryY) (@hb) (@vertexY) (@hbY) (@hAia)
      (@hAib) (@halphaA) (@hbetaA) (@horder) (@habIndex) (@BToT) (@ABstrict) (@BstrictT) (@rpB)
      (@aboveB) (@strictB) (@belowB) (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@hcountB)
      (@hstagesB) (@hdividersB) (@goodB) (@hgoodB) (@outsideStored) (@hDn) (@behavior)
      (@unaffected) (@fixedValue) (@sigmaProper) (@sigmaOne) (@missingBefore)
      (@sigmaNotElementary) (@missingA) (@treeMissingEq) (@stable) (@stableTn) (@TnToB)
      (@TnStrictB) (@notControlled) (@terminalRoute)
theorem helper_continuation_4272.{u_1, u_2} :
    helperContinuation4272Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hminimal alpha beta hne
      hmissingPrefix horderedUnused hlocation H q A n Tn Dn ia ib va vb ell yLength Y segRefl
      segTrans commonPrefix lastPositive coreToA TnToA AToT ordinaryToA starredToA YToT hmissingY
      hElementaryY ha hb vertexY haY hbY hout hAia hAib missingNotA
  have halphaA : alpha ∉ TreeMissingColors phi A := missingNotA alpha ia ha.1 haY hout.1
  have hbetaA : beta ∉ TreeMissingColors phi A := missingNotA beta ib hb.1 hbY hout.2
  have horder := horderedUnused (Or.inl halphaA)
  have habIndex : ia.val < ib.val := by
    obtain ⟨i, j, hi, hj, hij⟩ := horder.1
    have hei := T.vertex_injective hi
    have hej := T.vertex_injective hj
    simpa [hei, hej] using hij
  have havb : va ≠ vb := by
    intro he
    have hi := congrArg Fin.val (T.vertex_injective he)
    omega
  -- Keep the exact ordered prefix ending at the beta-missing vertex.
  let B := TreeSequencePrefix T ib.val (by have := A.positive; omega)
    (Nat.le_of_lt_succ ib.isLt)
  have BToT : TreeSequenceInitialSegment B T :=
    ⟨Nat.le_of_lt_succ ib.isLt, (by intro i; rfl), (by intro i; rfl)⟩
  have AToB : TreeSequenceInitialSegment A B := commonPrefix AToT BToT (by exact le_of_lt hAib)
  have ABstrict : A.length < B.length := hAib
  have BToY : TreeSequenceInitialSegment B Y := commonPrefix BToT YToT hb.2
  have BstrictT : B.length < T.length := by
    exact @helper_BstrictT_1127 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@AToT) (@hAib)
        (@ABstrict) (@BToY)
  obtain ⟨ettB, hMPB, hrB, hsB, baseB, hcoreB, hclosureB, hsupportB,
      HB, hcountB, hstagesB, hdividersB, goodB, hgoodB⟩ :=
    GoodHierarchyTerminalPrefixRepackage G k e0 input T phi phi ett C.maximum
      base H C.good B AToB ABstrict BToT
  rcases ettB with ⟨rB, rpB, seriesB, aboveB, strictB, belowB, genB⟩
  cases hrB
  have heqB : seriesB = ett.series := eq_of_heq hsB
  cases heqB
  let ettB : ExtendedTashkinovTree G k e0 input B phi :=
    ⟨ett.rounds, rpB, ett.series, aboveB, strictB, belowB, genB⟩
  have missingSubset {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U) :
      TreeMissingColors phi S ⊆ TreeMissingColors phi U := by
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSU hv, hcv⟩
  have outsideStored (hcase :
      (0 < H.dividerCount ∧ (alpha ∈ TreeMissingColors phi (H.stage ⟨H.dividerCount, by omega⟩) ∨
        Disjoint ({alpha, beta} : Finset (Fin k)) (HierarchyStoredColorsAt H q))) ∨
      (H.dividerCount = 0 ∧ (alpha ∈ TreeMissingColors phi Tn ∨
        Disjoint ({alpha, beta} : Finset (Fin k)) Dn))) :
      alpha ∉ Dn ∧ beta ∉ Dn := by
    exact @helper_outsideStored_1149 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@lastPositive) (@TnToA) (@hAib) (@halphaA) (@hbetaA) (@rpB) (@aboveB) (@strictB)
        (@belowB) (@genB) (@baseB) (@HB) (@missingSubset) (@hcase)
  have finish (hDn : alpha ∉ Dn ∧ beta ∉ Dn) :
      TwoColorComponent G phi alpha beta (Sum.inl va) =
        TwoColorComponent G phi alpha beta (Sum.inl vb) := by
    exact @helper_finish_4308 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone) (@hlower)
        (@hminimal) (@alpha) (@beta) (@hne) (@hmissingPrefix) (@horderedUnused) (@hlocation)
        (@segRefl) (@segTrans) (@commonPrefix) (@coreToA) (@TnToA) (@AToT) (@ordinaryToA)
        (@starredToA) (@hmissingY) (@hElementaryY) (@ha) (@hb) (@vertexY) (@haY) (@hbY) (@hout)
        (@hAia) (@hAib) (@halphaA) (@hbetaA) (@horder) (@habIndex) (@havb) (@BToT) (@AToB)
        (@ABstrict) (@BToY) (@BstrictT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@hMPB)
        (@hsB) (@baseB) (@hcoreB) (@hclosureB) (@hsupportB) (@HB) (@hcountB) (@hstagesB)
        (@hdividersB) (@goodB) (@hgoodB) (@missingSubset) (@outsideStored) (@hDn)
  exact ⟨fun h => finish (outsideStored (Or.inl h)),
    fun h => finish (outsideStored (Or.inr h))⟩

end GoldbergSeymour.ChangeLemmaBothOutsidePreparation

end
