/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.EligibleIndexBoundPreparation

public import LeanPool.GoldbergSeymour.SharedFacts.OutsideAdvancement

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTailAtLeastTwo
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.HierarchyFieldTransport
public import LeanPool.GoldbergSeymour.SharedFacts.ShorteningProofs

/-!
# Hierarchy Situation One Shortening Contradiction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation6826Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
   Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hp : HierarchyPathNumber H = (1 : ℕ)) (htail : (2 : ℕ) ≤ T.length - A.length)
   (trans :
    ∀ {X Y Z : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y)
     (hYZ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)
   (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (by omega) (by omega);
  let X : TreeSequence G e0 := TreeSequencePrefix T (T.length - (2 : ℕ)) (by omega) (by omega);
  ∀ (hBlength : B.length = T.length - (1 : ℕ)) (hXlength : X.length = T.length - (2 : ℕ))
   (hBT : TreeSequenceInitialSegment B T) (hXB : TreeSequenceInitialSegment X B)
   (hTnX : TreeSequenceInitialSegment Tn X),
  let r : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  ∀
   (consecutive :
    ∀ (t : Fin T.length) (ht : A.length + (1 : ℕ) ≤ (↑t : ℕ)),
     G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ))
   (hyf : Incident G y f) (S : TreeSequence G e0) (hSBlen : S.length ≤ B.length) (beta : Fin k)
   (hbetaF : mu f = some beta) (z : V) (hzB : z ∈ TreeSequenceVertexSet B)
   (hbetaz : beta ∈ MissingColors G mu z) (hzy : z ≠ y) (hzX : z ∈ TreeSequenceVertexSet X)
   (hab : alpha ≠ beta),
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (fixed : ∀ (e : E) (hef : e ≠ f), sigma e = mu e)
   (missingFixed :
    ∀ (v : V) (hv : v ∈ TreeSequenceVertexSet X),
     MissingColors G sigma v = MissingColors G mu v)
   (fixedB : ∀ (t : Fin B.length), sigma (B.edge t) = mu (B.edge t))
   (missingTree :
    ∀ (U : TreeSequence G e0) (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X),
     TreeMissingColors sigma U = TreeMissingColors mu U)
   (minusEq :
    ∀ (U : TreeSequence G e0) (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X)
     (R : Finset (Fin k)),
     TreeColorSetMinusClosed G sigma U R ↔ TreeColorSetMinusClosed G mu U R)
   (lastPositive :
    ∀ (hq : H.dividerCount ≠ (0 : ℕ)),
     A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
   (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (P.corresponding.replacementETT.series.data.tree
      (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
       Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
     B)
   (strictB :
    (P.corresponding.replacementETT.series.data.tree
       (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
        Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (P.corresponding.replacementETT.series.data.tree
      (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
   (generatingB :
    mu =
     P.corresponding.replacementETT.series.data.coloring
      (Fin.last P.corresponding.replacementETT.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     mu)
   (HB :
    TashkinovHierarchy
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     baseB)
   (hcountB : HB.dividerCount = H.dividerCount)
   (hstagesB :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HB.stage j.castSucc = H.stage (Fin.cast (by omega) j).castSucc ∧
      HierarchyStarredStage HB j = HierarchyStarredStage H (Fin.cast (by omega) j))
   (goodB : GoodHierarchy HB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
   SharedFacts.ShorteningTransport.eB1665 G k e0 input T phi ett base C ctx P hlenT positiveB
       aboveB strictB belowB
    generatingB;
  ∀ (coreBX : TreeSequenceVertexSet baseB.core ⊆ TreeSequenceVertexSet X)
   (closureBX :
    ∀ (hpe : EB.series.data.kind (Fin.last EB.rounds) = some TashkinovExtensionKind.PE),
     TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X)
   (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
   (hmaximum : MaximumProperty corr.replacementETT)
   (bs : HierarchyBase corr.replacementETT sigma) (hcore : baseB.core = bs.core)
   (hpe :
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
         series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
         strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := generatingB :
         ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.series.data.kind
       (Fin.last
        {
         rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.rounds) =
      some TashkinovExtensionKind.PE ↔
     corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
      some TashkinovExtensionKind.PE)
   (hclosure :
    {
     rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
         series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
         strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := generatingB :
         ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.series.data.kind
       (Fin.last
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.rounds) =
      some TashkinovExtensionKind.PE →
     baseB.closure = bs.closure)
   (baseStageK :
    HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
     corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc)
   (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
   (nestedK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
   (strictK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     (HB.stage j.castSucc).length < (HB.stage j.succ).length)
   (coreInsideK :
    TreeSequenceInitialSegment bs.core
     (HB.stage (⟨(1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ)))))
   (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
   (increasingK :
    ∀ (i j : Fin HB.dividerCount),
     (↑i : ℕ) < (↑j : ℕ) → (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
   (dividerStageK :
    ∀ (i : Fin HB.dividerCount),
     HB.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ))) =
      TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
       (Nat.le_of_lt_succ (HB.dividerPosition i).isLt)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
   {
    dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
    terminalStage := terminalStageK, nested := nestedK, strict := strictK,
    dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
    dividerIncreasing := increasingK, dividerStage := dividerStageK,
    coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  ∀
   (starredEq :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HierarchyStarredStage KF j = HierarchyStarredStage HB j)
   (stageBX :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     TreeSequenceInitialSegment (HB.stage j.castSucc) X)
   (allStageB :
    ∀ (j : Fin (HB.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (HB.stage j) B)
   (terminalTree :
    corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc = Tn)
   (storedEq :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HierarchyStoredColorsAt KF j = HierarchyStoredColorsAt HB j),
  False

private abbrev helperContinuation7103Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
   Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hp : HierarchyPathNumber H = (1 : ℕ)) (htail : (2 : ℕ) ≤ T.length - A.length)
   (trans :
    ∀ {X Y Z : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y)
     (hYZ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)
   (chain :
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))),
     (↑i : ℕ) ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 : ℕ)))))
   (coreA : TreeSequenceInitialSegment P.replacementBase.core A)
   (hTnA : TreeSequenceInitialSegment Tn A) (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (by omega) (by omega);
  let X : TreeSequence G e0 := TreeSequencePrefix T (T.length - (2 : ℕ)) (by omega) (by omega);
  ∀ (hBlength : B.length = T.length - (1 : ℕ)) (hXlength : X.length = T.length - (2 : ℕ))
   (hBT : TreeSequenceInitialSegment B T) (hAX : TreeSequenceInitialSegment A X)
   (hXB : TreeSequenceInitialSegment X B) (hTnX : TreeSequenceInitialSegment Tn X)
   (hAB : TreeSequenceInitialSegment A B),
  let r : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  let w : V := T.vertex (Fin.last T.length);
  ∀
   (consecutive :
    ∀ (t : Fin T.length) (ht : A.length + (1 : ℕ) ≤ (↑t : ℕ)),
     G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ))
   (hends : G.ends f = s(y, w)) (hyf : Incident G y f) (S : TreeSequence G e0)
   (hSBlen : S.length ≤ B.length) (beta : Fin k) (hbetaF : mu f = some beta) (z : V)
   (hzB : z ∈ TreeSequenceVertexSet B) (hbetaz : beta ∈ MissingColors G mu z) (hzy : z ≠ y)
   (hzX : z ∈ TreeSequenceVertexSet X) (hab : alpha ≠ beta),
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (fixed : ∀ (e : E) (hef : e ≠ f), sigma e = mu e) (hsproper : IsProperEdgeColoring G sigma)
   (hsone : IsOneEdgeUncolored sigma e0)
   (incidentFixed : ∀ (e : E) (he : TreeIncidentEdge X e), sigma e = mu e)
   (missingFixed :
    ∀ (v : V) (hv : v ∈ TreeSequenceVertexSet X),
     MissingColors G sigma v = MissingColors G mu v)
   (fixedB : ∀ (t : Fin B.length), sigma (B.edge t) = mu (B.edge t))
   (stable :
    StableColoring Tn (TashkinovStoredColors P.corresponding.replacementETT.series.data n)
     (P.corresponding.replacementETT.series.data.coloring n) sigma)
   (hrouteB :
    P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence sigma Tn B ∨
     (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
       P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (edge : E) (seed : TreeSequence G e0),
       P.corresponding.replacementETT.series.data.connectingEdges n = ({ edge } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn edge seed ∧ TashkinovAugmentationSequence sigma seed B)
   (missingTree :
    ∀ (U : TreeSequence G e0) (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X),
     TreeMissingColors sigma U = TreeMissingColors mu U),
  False

private theorem helper_hdata_485.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  HierarchyPathNumber H = (1 : ℕ) →
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) ↦ by omega);
  let r : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  (∀ (e : E), TreeIncidentEdge X e → sigma e = mu e) →
  (∀ v ∈ TreeSequenceVertexSet X, MissingColors G sigma v = MissingColors G mu v) →
  StableColoring Tn (TashkinovStoredColors P.corresponding.replacementETT.series.data n)
      (P.corresponding.replacementETT.series.data.coloring n) sigma →
  (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn B ∨
      (P.corresponding.replacementETT.series.data.kind n =
            some TashkinovExtensionKind.SE ∨
          P.corresponding.replacementETT.series.data.kind n =
            some TashkinovExtensionKind.RE) ∧
        ∃ (edge : E) (seed : TreeSequence G e0),
          P.corresponding.replacementETT.series.data.connectingEdges n = { edge } ∧
            TreeSequenceAdjoinEdge Tn edge seed ∧
              TashkinovAugmentationSequence sigma seed B) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds)),
  MaximumProperty
      { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
        series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
        strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := generatingB :
        ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu } →
  ∀
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  (EB.series.data.kind (Fin.last EB.rounds) = some TashkinovExtensionKind.PE →
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X) →
  ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B),
  MaximumProperty corr.replacementETT ∧
    ∃ (bs : HierarchyBase corr.replacementETT sigma) (K :
      TashkinovHierarchy corr.replacementETT bs), SameHierarchyStages HB K := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H n Tn mu hp trans hlenT B X r
      f S hSBlen sigma hsproper hsone incidentFixed missingFixed stable hrouteB positiveB aboveB
      strictB belowB generatingB hmaxB baseB HB EB closureBX
  by_cases hpe : EB.series.data.kind (Fin.last EB.rounds) =
      some TashkinovExtensionKind.PE
  · have hb : TashkinovAugmentationSequence sigma Tn B := by
      rcases hrouteB with h | h
      · exact h.2
      · rcases h.1 with h | h <;> rw [hpe] at h <;> cases h
    have hcomb : CombinedStableColoring Tn baseB.closure
        (TashkinovStoredColors EB.series.data (Fin.last EB.rounds)) mu sigma := by
      refine ⟨?_, ?_⟩
      · have hh := stable
        change StableColoring Tn
          (TashkinovStoredColors EB.series.data (Fin.last EB.rounds))
          (P.corresponding.replacementETT.series.data.coloring
            (Fin.last P.corresponding.replacementETT.rounds)) sigma at hh
        rw [← P.corresponding.replacementETT.generatingColoring] at hh
        exact hh
      · refine ⟨?_, ?_⟩
        · intro edge he _
          obtain ⟨v, hv, hi⟩ := he
          exact incidentFixed edge ⟨v, closureBX hpe hv, hi⟩
        · intro v hv
          exact missingFixed v (closureBX hpe hv)
    exact HierarchySplitter G k e0 P.corresponding.replacementInput B mu sigma EB
      hmaxB old.positive P.minimumContext.lowerRung baseB HB hpe
      P.minimumContext.proper P.minimumContext.oneEdgeUncolored hsproper hsone hcomb hb
  · have hmodB := Td G k e0 P.corresponding.replacementInput B mu EB hmaxB
      old.positive P.minimumContext.lowerRung sigma hsproper hsone stable
    obtain ⟨corr⟩ := hmodB.2.2 B aboveB strictB hrouteB
    have hmaximum := MaximumPropertyTransport G k e0 EB sigma hmodB B corr hmaxB
    obtain ⟨bs, K, same⟩ := HB.nonparallelCorrespondence corr hpe
    exact ⟨corr, hmaximum, bs, K, same⟩

private theorem helper_hpS_917.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let mu : PartialEdgeColoring E k := P.coloring;
  (2 : ℕ) ≤ T.length - A.length →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  B.length = T.length - (1 : ℕ) →
  TreeSequenceInitialSegment B T →
  let r : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let f : E := T.edge r;
  (∀ (t : Fin T.length),
      A.length + (1 : ℕ) ≤ (↑t : ℕ) →
        G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)) →
  ∀ (S : TreeSequence G e0) (_ : S.length ≤ B.length) (beta : Fin k),
  alpha ≠ beta →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (H.dividerCount ≠ (0 : ℕ) →
      A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
    (bs : HierarchyBase corr.replacementETT sigma)
    (baseStageK :
      HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc)
    (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
    (nestedK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
    (strictK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        (HB.stage j.castSucc).length < (HB.stage j.succ).length)
    (coreInsideK :
      TreeSequenceInitialSegment bs.core
        (HB.stage (⟨(1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ)))))
    (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
    (increasingK :
      ∀ (i j : Fin HB.dividerCount),
        (↑i : ℕ) < (↑j : ℕ) →
          (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
    (dividerStageK :
      ∀ (i : Fin HB.dividerCount),
        HB.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ))) =
          TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
            (Nat.le_of_lt_succ (HB.dividerPosition i).isLt)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
    { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
      terminalStage := terminalStageK, nested := nestedK, strict := strictK,
      dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
      dividerIncreasing := increasingK, dividerStage := dividerStageK,
      coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  HierarchyStarredStage KF (Fin.last KF.dividerCount) = A →
  HierarchyPathNumber KF = (1 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H A mu htail hlenT B hBlength
      hBT r f consecutive S hSBlen beta hab sigma lastPositive positiveB aboveB strictB belowB
      generatingB baseB HB EB corr bs baseStageK terminalStageK nestedK strictK coreInsideK
      positiveK increasingK dividerStageK KF lastStar
  let candidates := (Finset.Icc 1 (B.length - A.length)).filter fun i =>
    ∀ t : Fin B.length, A.length + i ≤ t.val →
      G.ends (B.edge t) = s(B.vertex t.castSucc, B.vertex t.succ)
  have hm : 1 ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
    intro t ht
    rw [← hBT.2.2 t]
    have hc := consecutive (Fin.castLE hBT.1 t) ht
    have hv1 : (Fin.castLE hBT.1 t).castSucc =
        Fin.castLE (Nat.succ_le_succ hBT.1) t.castSucc := Fin.ext rfl
    have hv2 : (Fin.castLE hBT.1 t).succ =
        Fin.castLE (Nat.succ_le_succ hBT.1) t.succ := Fin.ext rfl
    rw [hv1, hv2, hBT.2.1 t.castSucc, hBT.2.1 t.succ] at hc
    exact hc
  have hn : candidates.Nonempty := ⟨1, hm⟩
  have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).1).1
  have hhi := Finset.min'_le candidates 1 hm
  unfold HierarchyPathNumber
  dsimp only
  rw [lastStar]
  change (if h : candidates.Nonempty then candidates.min' h else B.length - A.length) = 1
  rw [dite_eq_left hn]
  omega

private theorem helper_consecutive_824.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  HierarchyPathNumber H = (1 : ℕ) →
  (2 : ℕ) ≤ T.length - A.length →
  (3 : ℕ) ≤ T.length →
  ∀ (t : Fin T.length),
  A.length + (1 : ℕ) ≤ (↑t : ℕ) →
  G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P old H A hp htail hlenT t ht
  let candidates := (Finset.Icc 1 (T.length - A.length)).filter fun i =>
    ∀ t : Fin T.length, A.length + i ≤ t.val →
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
  have hp' := hp
  change (if h : candidates.Nonempty then candidates.min' h else T.length - A.length) = 1 at hp'
  have hn : candidates.Nonempty := by
    by_contra hn
    have hp'' : T.length - A.length = 1 := by
      simpa only [dite_eq_right hn] using hp'
    omega
  have hm : candidates.min' hn = 1 := by
    simpa only [dite_eq_left hn] using hp'
  have hc := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  rw [hm] at hc
  exact hc t ht

private theorem helper_hfe0_1615.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (_ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  ∀ (beta : Fin k),
  alpha ≠ beta →
  f ≠ e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha trans hlenT B r f S hSBlen beta hab he
  have hh := T.edge_injective (he.trans T.first_edge.symm)
  have hv := congrArg Fin.val hh
  dsimp [r] at hv
  omega

private theorem helper_fixedB_1646.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega);
  B.length = T.length - (1 : ℕ) →
  TreeSequenceInitialSegment B T →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), e ≠ f → sigma e = mu e) →
  ∀ (t : Fin B.length),
  sigma (B.edge t) = mu (B.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu trans hlenT B hBlength hBT r f S
      hSBlen sigma fixed t
  apply fixed
  intro he
  have hh := T.edge_injective ((hBT.2.2 t).trans he)
  have hh := congrArg Fin.val hh
  have ht := t.isLt
  change t.val = T.length - 1 at hh
  omega

private theorem helper_closureBX_1732.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega);
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    SharedFacts.ShorteningTransport.eB1665 G k e0 input T phi ett base C ctx P hlenT positiveB
        aboveB strictB
      belowB generatingB;
  TreeSequenceVertexSet baseB.core ⊆ TreeSequenceVertexSet X →
  EB.series.data.kind (Fin.last EB.rounds) = some TashkinovExtensionKind.PE →
  TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P mu hlenT B X positiveB aboveB strictB
      belowB generatingB baseB EB coreBX hpe
  obtain ⟨union⟩ := (baseB.parallel hpe).2.2
  intro v hv
  apply coreBX
  rw [union.vertexSet]
  exact Finset.mem_union_right _ hv

private theorem helper_hbetaY_1908.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let mu : PartialEdgeColoring E k := P.coloring;
  HierarchyPathNumber H = (1 : ℕ) →
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  Incident G y f →
  ∀ (beta : Fin k),
  mu f = some beta →
  alpha ≠ beta →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), e ≠ f → sigma e = mu e) →
  beta ∈ MissingColors G sigma y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H mu hp trans hlenT B r f y hyf
      beta hbetaF hab sigma fixed
  simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro hp
  obtain ⟨edge, hi, hc⟩ := (Finset.mem_filter.mp hp).2
  by_cases hef : edge = f
  · subst edge
    have he : alpha = beta := by simpa [sigma] using hc
    exact hab he
  · have hcOld : mu edge = some beta := (fixed edge hef).symm.trans hc
    exact P.minimumContext.proper hef ⟨y, hi, hyf⟩ hcOld hbetaF

private theorem helper_parallelBase_5019.{u_1, u_2} :
    SharedFacts.ShorteningTransport.parallelBase5019Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H n Tn mu hp hlenT B X hTnX r f
      sigma missingTree minusEq positiveB aboveB strictB belowB generatingB baseB HB goodB EB
      coreBX closureBX corr bs hcore hpe hclosure baseStageK terminalStageK nestedK strictK
      coreInsideK positiveK increasingK dividerStageK KF terminalTree storedEq
  dsimp only
  intro hp
  have hpB := hpe.mpr hp
  have hcl : bs.closure = baseB.closure := (hclosure hpB).symm
  obtain ⟨hnot, hcard⟩ := goodB.parallelBase hpB
  constructor
  · change ¬ TreeColorSetMinusClosed G sigma bs.core
      ((HierarchyStoredColorsAt KF 0).biUnion (goodB.gamma 0))
    rw [← hcore, storedEq 0, minusEq baseB.core coreBX]
    exact hnot
  · exact _root_.GoldbergSeymour.EligibleIndexBound.helper_branch_2341 (@G) (@k) (@e0) (@input) (@T)
      (@phi) (@ett) (@base) (@C) (@ctx) (@P)
      (@alpha) (@hlenT) (@hTnX) (@missingTree) (@positiveB) (@aboveB) (@strictB) (@belowB)
      (@generatingB) (@baseB) (@HB) (@goodB) (@closureBX) (@corr) (@bs) (@baseStageK)
      (@terminalStageK) (@nestedK) (@strictK) (@coreInsideK) (@positiveK) (@increasingK)
      (@dividerStageK) (@terminalTree) (@storedEq) (@hpB) (@hcl) (@hcard)

private theorem helper_continuation_6826.{u_1, u_2} :
    helperContinuation6826Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H A n Tn mu hp htail trans
      hlenT B X hBlength hXlength hBT hXB hTnX r f y consecutive hyf S hSBlen beta hbetaF z hzB
      hbetaz hzy hzX hab sigma fixed missingFixed fixedB missingTree minusEq lastPositive
      positiveB aboveB strictB belowB generatingB baseB HB hcountB hstagesB goodB EB coreBX
      closureBX corr hmaximum bs hcore hpe hclosure baseStageK terminalStageK nestedK strictK
      coreInsideK positiveK increasingK dividerStageK KF starredEq stageBX allStageB terminalTree
      storedEq
  have stageMissingEq (j : Fin (HB.dividerCount + 1)) :
      HierarchyStageMissingColors KF j = HierarchyStageMissingColors HB j := by
    exact @EligibleIndexBound.helper_stageMissingEq_2235 (@V) (@E) inferInstance inferInstance
        inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@hlenT) (@hTnX) (@missingTree) (@positiveB) (@aboveB) (@strictB) (@belowB)
        (@generatingB) (@baseB) (@HB) (@corr) (@bs) (@baseStageK) (@terminalStageK) (@nestedK)
        (@strictK) (@coreInsideK) (@positiveK) (@increasingK) (@dividerStageK) (@stageBX)
        (@terminalTree) (@j)
  have earlyMissing (j : Fin (B.length + 1)) (hj : j.val < B.length) :
      MissingColors G sigma (B.vertex j) = MissingColors G mu (B.vertex j) := by
    exact _root_.GoldbergSeymour.EligibleIndexBound.helper_earlyMissing_2244 (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@hlenT) (@hBlength) (@hXlength) (@hXB) (@S) (@hSBlen) (@beta)
        (@hab) (@missingFixed) (@lastPositive) (@positiveB) (@aboveB) (@strictB) (@belowB)
        (@generatingB) (@baseB) (@HB) (@j) (@hj)
  -- Last-vertex changes preserve the totalized least missing position.
  have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
      (j : Fin (B.length + 1)) (hj : c ∈ MissingColors G psi (B.vertex j)) :
      (HierarchyFirstMissingPosition psi B c).val ≤ j.val := by
    exact TreeSequenceFirstMissingPositionLe hj
  have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition psi B c).val < B.length) :
      c ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B c)) := by
    exact TreeSequenceFirstMissingPositionMem hlt
  have firstEq (c : Fin k) : HierarchyFirstMissingPosition sigma B c =
      HierarchyFirstMissingPosition mu B c := by
    exact EligibleIndexBound.helper_firstEq_1174 G k e0 input T phi ett base C ctx P alpha hlenT
        hBlength S hSBlen
        positiveB aboveB strictB
        belowB generatingB baseB HB earlyMissing firstLe firstMem c
  have stageFixed (j : Fin (HB.dividerCount + 1)) (t : Fin (HB.stage j.succ).length) :
      sigma ((HB.stage j.succ).edge t) = mu ((HB.stage j.succ).edge t) := by
    rw [← (allStageB j.succ).2.2 t]
    exact fixedB _
  have segmentEq (j : Fin (HB.dividerCount + 1)) (c : Fin k) :
      HierarchySegmentColors KF j c = HierarchySegmentColors HB j c := by
    exact @EligibleIndexBound.helper_segmentEq_2283 (@V) (@E) inferInstance inferInstance
        inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@trans) (@hlenT) (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB)
        (@baseB) (@HB) (@corr) (@bs) (@baseStageK) (@terminalStageK) (@nestedK) (@strictK)
        (@coreInsideK) (@positiveK) (@increasingK) (@dividerStageK) (@starredEq) (@firstEq)
        (@stageFixed) (@j) (@c)
  let goodS : GoodHierarchy KF := by
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
        intro i
        exact goodB.uniqueRefresh_transport KF i i (storedEq i.succ) rfl
          (starredEq i.castSucc) (fun v hv => missingFixed v
            (TreeSequenceInitialSegmentVertexSetSubset (stageBX i.succ)
              (Finset.mem_sdiff.mp hv).1))
      parallelBase := by
        exact @helper_parallelBase_5019 (@V) (@E) inferInstance inferInstance inferInstance
            inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
            (@alpha) (@hp) (@hlenT) (@hTnX) (@missingTree) (@minusEq) (@positiveB) (@aboveB)
            (@strictB) (@belowB) (@generatingB) (@baseB) (@HB) (@goodB) (@coreBX) (@closureBX)
            (@corr) (@bs) (@hcore) (@hpe) (@hclosure) (@baseStageK) (@terminalStageK) (@nestedK)
            (@strictK) (@coreInsideK) (@positiveK) (@increasingK) (@dividerStageK)
            (@terminalTree) (@storedEq)
      minusClosed := by
        intro i
        change TreeColorSetMinusClosed G sigma (HB.stage i.succ.castSucc)
          ((HierarchyStoredColorsAt KF i.succ).biUnion (goodB.gamma i.castSucc))
        rw [storedEq i.succ, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBX
            i.succ))]
        exact goodB.minusClosed i }
  have hbetaY : beta ∈ MissingColors G sigma y := by
    exact @helper_hbetaY_1908 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hp)
        (@trans) (@hlenT) (@hyf) (@beta) (@hbetaF) (@hab) (@fixed)
  have hnotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) := by
    exact _root_.GoldbergSeymour.EligibleIndexBound.helper_hnotElementary_2365 (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@hlenT) (@beta) (@z) (@hzB) (@hbetaz) (@hzy) (@hzX)
        (@missingFixed) (@hbetaY)
  let CS : HierarchyCounterexample bs := by
    exact {
      positive := by rw [corr.rungAgreement]; exact old.positive
      hierarchy := KF
      good := goodS
      maximum := hmaximum
      notElementary := hnotElementary }
  have lastStar : HierarchyStarredStage KF (Fin.last KF.dividerCount) = A := by
    exact @_root_.GoldbergSeymour.EligibleIndexBound.helper_lastStar_2378 (@V) (@E) inferInstance
        inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hlenT)
        (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB) (@baseB) (@HB) (@hcountB)
        (@hstagesB) (@corr) (@bs) (@baseStageK) (@terminalStageK) (@nestedK) (@strictK)
        (@coreInsideK) (@positiveK) (@increasingK) (@dividerStageK) (@starredEq)
  have hpS : HierarchyPathNumber KF = 1 := by
    exact @helper_hpS_917 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@htail)
        (@hlenT) (@hBlength) (@hBT) (@consecutive) (@S) (@hSBlen) (@beta) (@hab) (@lastPositive)
        (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB) (@baseB) (@HB) (@corr) (@bs)
        (@baseStageK) (@terminalStageK) (@nestedK) (@strictK) (@coreInsideK) (@positiveK)
        (@increasingK) (@dividerStageK) (@lastStar)
  have lastOrdinary : HB.stage (Fin.last HB.dividerCount).castSucc =
      H.stage (Fin.last H.dividerCount).castSucc := by
    exact _root_.GoldbergSeymour.EligibleIndexBound.helper_lastOrdinary_2387 (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P)
        (@hlenT) (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB) (@baseB) (@HB)
        (@hcountB) (@hstagesB)
  have hlastLength : (H.stage (Fin.last H.dividerCount).castSucc).length < B.length := by
    have hh := HB.strict (Fin.last HB.dividerCount)
    simpa only [lastOrdinary, Fin.succ_last, HB.terminalStage] using hh
  -- The comparison is at the original rung and divider count.
  apply P.minimumContext.lexicographicMinimality CS corr.rungAgreement hcountB
  change HierarchyCounterexampleLess
    (HierarchyPathNumber KF, B.length - (HB.stage ⟨HB.dividerCount, by omega⟩).length)
    (HierarchyPathNumber H, T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
  rw [hpS, hp]
  right
  refine ⟨rfl, ?_⟩
  have hidx : (⟨HB.dividerCount, by omega⟩ : Fin (HB.dividerCount + 2)) =
      (Fin.last HB.dividerCount).castSucc := Fin.ext rfl
  have hidxH : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
      (Fin.last H.dividerCount).castSucc := Fin.ext rfl
  rw [hidx, hidxH, lastOrdinary]
  dsimp only
  omega

private theorem helper_continuation_7103.{u_1, u_2} :
    helperContinuation7103Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H A n Tn mu hp htail trans
      chain coreA hTnA hlenT B X hBlength hXlength hBT hAX hXB hTnX hAB r f y w consecutive hends
      hyf S hSBlen beta hbetaF z hzB hbetaz hzy hzX hab sigma fixed hsproper hsone incidentFixed
      missingFixed fixedB stable hrouteB missingTree
  have boundaryEq (U : TreeSequence G e0)
      (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) (c : Fin k) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet U) c =
        BoundaryColorEdges G mu (TreeSequenceVertexSet U) c := by
    exact _root_.GoldbergSeymour.EligibleIndexBound.helper_boundaryEq_2121 (@G) (@k) (@e0) (@input)
        (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P) (@alpha) (@hlenT) (@hends) (@incidentFixed) (@U) (@hUX) (@c)
  have minusEq (U : TreeSequence G e0)
      (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) (R : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma U R ↔ TreeColorSetMinusClosed G mu U R := by
    unfold TreeColorSetMinusClosed TreeColorSetClosed
    rw [missingTree U hUX]
    simp only [boundaryEq U hUX]
  have lastPositive (hq : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact _root_.GoldbergSeymour.EligibleIndexBound.helper_lastPositive_2137 (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@ctx) (@P)
        (@hlenT) (@S) (@hSBlen) (@hq)
  have ordinaryA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    exact _root_.GoldbergSeymour.EligibleIndexBound.helper_ordinaryA_2146 (@G) (@k) (@e0) (@input)
        (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P)
        (@chain) (@hTnA) (@hlenT) (@S) (@hSBlen) (@lastPositive) (@j)
  have starA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    refine Fin.cases coreA (fun i => ordinaryA i.succ) j
  -- Retain the old prefix data; construct the recolored ETT separately.
  obtain ⟨eb, hmaxB, hrungB, hseriesB, baseB, hcoreB, hclosureB, hsupportB,
      HB, hcountB, hstagesB, hdividersB, goodB, hcolorsB⟩ :=
    GoodHierarchyTerminalPrefixRepackage G k e0 P.corresponding.replacementInput T
      mu mu P.corresponding.replacementETT old.maximum P.replacementBase H old.good
      B hAB (by change A.length < B.length; omega) hBT
  rcases eb with ⟨roundsB, positiveB, seriesB, aboveB, strictB, belowB, generatingB⟩
  dsimp only at hrungB hseriesB
  cases hrungB
  have hs : seriesB = P.corresponding.replacementETT.series := eq_of_heq hseriesB
  cases hs
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu := by
    exact @SharedFacts.ShorteningTransport.eB1665 (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hlenT)
        (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB)
  have coreBX : TreeSequenceVertexSet baseB.core ⊆ TreeSequenceVertexSet X := by
    rw [hcoreB]
    exact TreeSequenceInitialSegmentVertexSetSubset (trans coreA hAX)
  have closureBX (hpe : EB.series.data.kind (Fin.last EB.rounds) =
      some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X := by
    exact helper_closureBX_1732 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@P)
        (@hlenT) (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB) (@baseB) (@coreBX)
        (@hpe)
  -- PE preparation rebuilds the base; SE/RE retain the exact seed.
  have hdata : ∃ corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B,
      MaximumProperty corr.replacementETT ∧
      ∃ bs : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT bs,
          SameHierarchyStages HB K := by
    exact @helper_hdata_485 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx P alpha hp trans hlenT S hSBlen hsproper hsone incidentFixed
        missingFixed stable hrouteB positiveB aboveB strictB belowB generatingB hmaxB baseB HB
        closureBX
  obtain ⟨corr, hmaximum, bs, K, hsame⟩ := hdata
  let KF := K
  rcases hsame with ⟨hcore, hcount, hstage, hposition, hpe, hclosure⟩
  rcases K with ⟨qK, stageK, baseStageK, terminalStageK, nestedK, strictK,
    positionK, positiveK, increasingK, dividerStageK, coreInsideK⟩
  change HB.dividerCount = qK at hcount
  cases hcount
  have hs : HB.stage = stageK := eq_of_heq hstage
  cases hs
  have hpos : HB.dividerPosition = positionK := eq_of_heq hposition
  cases hpos
  have starredEq (j : Fin (HB.dividerCount + 1)) :
      HierarchyStarredStage KF j = HierarchyStarredStage HB j := by
    refine Fin.cases hcore.symm (fun _ => rfl) j
  have stageBX (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HB.stage j.castSucc) X := by
    rw [(hstagesB j).1]
    exact trans (ordinaryA _) hAX
  have starBX (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceVertexSet (HierarchyStarredStage HB j) ⊆ TreeSequenceVertexSet X := by
    rw [(hstagesB j).2]
    exact TreeSequenceInitialSegmentVertexSetSubset (trans (starA _) hAX)
  have allStageB (j : Fin (HB.dividerCount + 2)) :
      TreeSequenceInitialSegment (HB.stage j) B := by
    exact Fin.reverseInduction (motive := fun j =>
      TreeSequenceInitialSegment (HB.stage j) B)
      (by rw [HB.terminalStage]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
      (fun i hi => trans (HB.nested i) hi) j
  have terminalTree : corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
    exact corr.terminalData.1
  have terminalStored : TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) = TashkinovStoredColors EB.series.data
        (Fin.last EB.rounds) := by
    exact corr.terminalData.2.2
  have storedEq (j : Fin (HB.dividerCount + 1)) :
      HierarchyStoredColorsAt KF j = HierarchyStoredColorsAt HB j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalStored, starredEq j, missingTree _ (starBX j)]
  exact @helper_continuation_6826 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@hp) (@htail) (@trans) (@hlenT) (@hBlength) (@hXlength) (@hBT) (@hXB) (@hTnX)
      (@consecutive) (@hyf) (@S) (@hSBlen) (@beta) (@hbetaF) (@z) (@hzB) (@hbetaz) (@hzy) (@hzX)
      (@hab) (@fixed) (@missingFixed) (@fixedB) (@missingTree) (@minusEq) (@lastPositive)
      (@positiveB) (@aboveB) (@strictB) (@belowB) (@generatingB) (@baseB) (@HB) (@hcountB)
      (@hstagesB) (@goodB) (@coreBX) (@closureBX) (@corr) (@hmaximum) (@bs) (@hcore) (@hpe)
      (@hclosure) (@baseStageK) (@terminalStageK) (@nestedK) (@strictK) (@coreInsideK)
      (@positiveK) (@increasingK) (@dividerStageK) (@starredEq) (@stageBX) (@allStageB)
      (@terminalTree) (@storedEq)

theorem HierarchySituationOneShorteningContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hsituation : HierarchyPathNumber C.hierarchy = 1)
    (hlast : HierarchyFullTailLength C - 1 ∈
      HierarchyEligibleCommonMissingIndices
        G k e0 input T phi ett base C ctx) : False := by
  classical
  open scoped Sym2 in
    obtain ⟨P, alpha, haB, haT⟩ := (Finset.mem_filter.mp hlast).2
    let old := P.counterexample
    let H := old.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let n := Fin.last P.corresponding.replacementETT.rounds
    let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
    let mu := P.coloring
    have sameLast : ∀ {a b : ℕ}
        (s : Fin (a + 2) → TreeSequence G e0)
        (t : Fin (b + 2) → TreeSequence G e0)
        (u v : TreeSequence G e0),
        a = b → HEq s t → u = v →
        Fin.cases (motive := fun _ => TreeSequence G e0)
          u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) =
          Fin.cases (motive := fun _ => TreeSequence G e0)
            v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
      exact @SharedFacts.OutsideAdvancement.sameLast (@V) (@E) (@G) (@e0)
    have hAold : HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A :=
      sameLast _ _ _ _ P.sameGood.1.2.1 P.sameGood.1.2.2.1 P.sameGood.1.1
    have hp : HierarchyPathNumber H = 1 := by
      unfold HierarchyPathNumber at hsituation ⊢
      dsimp only at hsituation ⊢
      rw [hAold] at hsituation
      exact hsituation
    have htail : 2 ≤ T.length - A.length :=
      HierarchyCounterexampleTailAtLeastTwo G k e0 P.corresponding.replacementInput
        T mu P.corresponding.replacementETT P.replacementBase old
        P.minimumContext.proper P.minimumContext.oneEdgeUncolored
        P.minimumContext.lowerRung P.minimumContext.fewerDividers
        P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
    have trans {X Y Z : TreeSequence G e0}
        (hXY : TreeSequenceInitialSegment X Y)
        (hYZ : TreeSequenceInitialSegment Y Z) :
        TreeSequenceInitialSegment X Z := by
      exact SharedFacts.ShorteningTransport.trans (@G) (@e0) (@hXY) (@hYZ)
    have chain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
        (i : Fin (H.dividerCount + 2)), i.val ≤ j →
        TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
      intro j hj i hi
      exact H.stageInitialSegmentOfLE i ⟨j, hj⟩ hi
    have starNext (j : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H j) (H.stage j.succ) := by
      refine Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) j
    have hAT : TreeSequenceInitialSegment A T := by
      have hh := starNext (Fin.last H.dividerCount)
      simpa only [Fin.succ_last, H.terminalStage] using hh
    have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
      exact EligibleIndexBound.helper_hTnCore_1684 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett)
          (@base) (@C) (@ctx) (@P)
    have coreA : TreeSequenceInitialSegment P.replacementBase.core A := by
      exact @EligibleIndexBound.helper_coreA_200 V E inferInstance inferInstance inferInstance
          inferInstance G k e0
          input T phi ett base C ctx P trans chain
    have hTnA := trans hTnCore coreA
    have hlenT : 3 ≤ T.length := by have := A.positive; omega
    let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
    let X := TreeSequencePrefix T (T.length - 2) (by omega) (by omega)
    have hBlength : B.length = T.length - 1 := rfl
    have hXlength : X.length = T.length - 2 := rfl
    have hBT : TreeSequenceInitialSegment B T := ⟨by omega,
      fun _ => rfl, fun _ => rfl⟩
    have hXT : TreeSequenceInitialSegment X T := ⟨by omega,
      fun _ => rfl, fun _ => rfl⟩
    have common {S U W : TreeSequence G e0}
        (hSW : TreeSequenceInitialSegment S W)
        (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
        TreeSequenceInitialSegment S U := by
      exact @EligibleIndexBound.helper_common_1702 (@V) (@E) (@G) (@e0) (@trans) (@S) (@U) (@W)
          (@hSW) (@hUW) (@hlen)
    have hAX : TreeSequenceInitialSegment A X := common hAT hXT (by omega)
    have hXB : TreeSequenceInitialSegment X B := common hXT hBT (by omega)
    have hTnX := trans hTnA hAX
    have hAB := trans hAX hXB
    have hfull : HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1) = B := by
      exact _root_.GoldbergSeymour.EligibleIndexBound.helper_hfull_1715 (@G) (@k) (@e0) (@input)
          (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@hAold) (@htail)
          (@hlenT)
    have halphaB : alpha ∈ MissingColors G mu (B.vertex (Fin.last B.length)) := by
      rw [hfull] at haB
      exact haB
    let r : Fin T.length := ⟨T.length - 1, by omega⟩
    let f := T.edge r
    let y := B.vertex (Fin.last B.length)
    let w := T.vertex (Fin.last T.length)
    have hy : T.vertex r.castSucc = y := by rfl
    have hw : T.vertex r.succ = w := by
      apply congrArg T.vertex
      apply Fin.ext
      dsimp [r]
      omega
    have consecutive (t : Fin T.length) (ht : A.length + 1 ≤ t.val) :
        G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
      exact helper_consecutive_824 G k e0 input T phi ett base C ctx P hp htail hlenT t ht
    have hends : G.ends f = s(y, w) :=
      (consecutive r (by dsimp [r]; omega)).trans (by rw [hy, hw])
    have hyf : Incident G y f := by rw [Incident, hends]; exact Sym2.mem_mk_left _ _
    have hwf : Incident G w f := by rw [Incident, hends]; exact Sym2.mem_mk_right _ _
    have hsource : ∃ S : TreeSequence G e0,
        S.length ≤ B.length ∧ TashkinovAugmentationSequence mu S T := by
      exact _root_.GoldbergSeymour.EligibleIndexBound.helper_hsource_1746 (@G) (@k) (@e0) (@input)
          (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@hlenT) (@hBlength) (@hXlength) (@hTnX)
    obtain ⟨S, hSBlen, hseq⟩ := hsource
    obtain ⟨hlen, hpre, beta, hbetaColor, hbetaMissing⟩ :=
      (TashkinovAugmentationSequencePosition mu S T hseq r
        (by simpa only [B, TreeSequencePrefix, r] using hSBlen)).1
    have hbetaF : mu f = some beta := by
      convert hbetaColor using 1
      congr 2
    have hbetaB : beta ∈ TreeMissingColors mu B := hbetaMissing
    obtain ⟨z, hzB, hbetaz⟩ := Finset.mem_biUnion.mp hbetaB
    have hzy : z ≠ y := by
      exact _root_.GoldbergSeymour.EligibleIndexBound.helper_hzy_1763 (@G) (@k) (@e0) (@input) (@T)
          (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@hlenT) (@hyf)
          (@beta) (@hbetaF) (@z) (@hzB) (@hbetaz)
    have hzX : z ∈ TreeSequenceVertexSet X := by
      exact @_root_.GoldbergSeymour.EligibleIndexBound.helper_hzX_1770 (@V) (@E) inferInstance
          inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@trans) (@hlenT)
          (@hBlength) (@hXlength) (@S) (@hSBlen) (@z) (@hzB) (@hzy)
    have hab : alpha ≠ beta := by
      intro he
      have halphaPresent : alpha ∈ PresentColors G mu y := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hyf, by rw [he]; exact hbetaF⟩
      exact (Finset.mem_sdiff.mp halphaB).2 halphaPresent
    let sigma : PartialEdgeColoring E k := fun e => if e = f then some alpha else mu e
    have fixed (e : E) (hef : e ≠ f) : sigma e = mu e := by simp [sigma, hef]
    have hsproper : IsProperEdgeColoring G sigma := by
      exact SharedFacts.ShorteningProofs.properRecoloring P.minimumContext.proper
        f alpha y w hends halphaB haT (by simp [sigma]) fixed
    have hfe0 : f ≠ e0 := by
      exact @helper_hfe0_1615 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@trans)
          (@hlenT) (@S) (@hSBlen) (@beta) (@hab)
    have hsone : IsOneEdgeUncolored sigma e0 := by
      exact _root_.GoldbergSeymour.EligibleIndexBound.helper_hsone_1794 (@G) (@k) (@e0) (@input)
          (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@alpha) (@hlenT)
          (@fixed) (@hfe0)
    have noInc (v : V) (hv : v ∈ TreeSequenceVertexSet X) : ¬ Incident G v f := by
      exact @_root_.GoldbergSeymour.EligibleIndexBound.helper_noInc_930 V E inferInstance
          inferInstance inferInstance inferInstance G k e0
          input T phi ett base C ctx P alpha trans hlenT hXlength hXT hy hends S hSBlen beta hab
          v hv
    have incidentFixed (e : E) (he : TreeIncidentEdge X e) : sigma e = mu e := by
      apply fixed
      intro hef
      obtain ⟨v, hv, hi⟩ := he
      exact noInc v hv (hef ▸ hi)
    have missingFixed (v : V) (hv : v ∈ TreeSequenceVertexSet X) :
        MissingColors G sigma v = MissingColors G mu v := by
      exact @_root_.GoldbergSeymour.EligibleIndexBound.helper_missingFixed_1810 (@V) (@E)
          inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@trans) (@hlenT) (@incidentFixed) (@v) (@hv)
    have fixedB (t : Fin B.length) : sigma (B.edge t) = mu (B.edge t) := by
      exact @helper_fixedB_1646 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@trans)
          (@hlenT) (@hBlength) (@hBT) (@S) (@hSBlen) (@fixed) (@t)
    have stable : StableColoring Tn
        (TashkinovStoredColors P.corresponding.replacementETT.series.data n)
        (P.corresponding.replacementETT.series.data.coloring n) sigma := by
      exact _root_.GoldbergSeymour.EligibleIndexBound.helper_stable_2096 (@G) (@k) (@e0) (@input)
          (@T) (@phi) (@ett) (@base) (@C) (@ctx)
          (@P) (@alpha) (@hlenT)
          (@hTnX) (@incidentFixed) (@missingFixed)
    have hrouteB :
        (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn B) ∨
        ((P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
            P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (edge : E) (seed : TreeSequence G e0),
            P.corresponding.replacementETT.series.data.connectingEdges n = {edge} ∧
            TreeSequenceAdjoinEdge Tn edge seed ∧
            TashkinovAugmentationSequence sigma seed B) := by
      exact @_root_.GoldbergSeymour.EligibleIndexBound.helper_hrouteB_979 V E inferInstance
          inferInstance inferInstance inferInstance G k
          e0 input T phi ett base C ctx P alpha trans hlenT hBlength hXlength hBT common hXB hTnX
          S hSBlen hseq hpre beta hab missingFixed fixedB
    have missingTree (U : TreeSequence G e0)
        (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X) :
        TreeMissingColors sigma U = TreeMissingColors mu U := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv => missingFixed v (hUX hv))
    exact @helper_continuation_7103 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@hp) (@htail) (@trans) (@chain) (@coreA) (@hTnA) (@hlenT) (@hBlength)
        (@hXlength) (@hBT) (@hAX) (@hXB) (@hTnX) (@hAB) (@consecutive) (@hends) (@hyf) (@S)
        (@hSBlen) (@beta) (@hbetaF) (@z) (@hzB) (@hbetaz) (@hzy) (@hzX) (@hab) (@fixed)
        (@hsproper) (@hsone) (@incidentFixed) (@missingFixed) (@fixedB) (@stable) (@hrouteB)
        (@missingTree)
end GoldbergSeymour

end
