/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

/-!
# Shared facts for HierarchySituationOneShorteningContradiction

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ShorteningTransport

/-- Shared dependent data used by more than one proof branch. -/
noncomputable abbrev eB1665.{u_1, u_2} :
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
  let mu : PartialEdgeColoring E k := P.coloring;
  (hlenT : (3 : ℕ) ≤ T.length) →
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega);
  (1 : ℕ) ≤ P.corresponding.replacementETT.rounds →
  TreeSequenceInitialSegment
      (P.corresponding.replacementETT.series.data.tree
        (⟨P.corresponding.replacementETT.rounds,
            by
            have :=
              GoldbergSeymour.TreeSequence.positive T
            omega⟩ :
          Fin
            (P.corresponding.replacementETT.rounds +
              (2 : ℕ))))
      B →
  (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have :=
                GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin
              (P.corresponding.replacementETT.rounds +
                (2 : ℕ)))).length <
      B.length →
  TreeSequenceInitialSegment B
      (P.corresponding.replacementETT.series.data.tree
        (Fin.last
          (P.corresponding.replacementETT.rounds +
            (1 : ℕ)))) →
  mu =
      P.corresponding.replacementETT.series.data.coloring
        (Fin.last
          P.corresponding.replacementETT.rounds) →
  ExtendedTashkinovTree G k e0
    P.corresponding.replacementInput B mu := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P mu hlenT B positiveB aboveB strictB
      belowB generatingB
  exact {
    rounds := P.corresponding.replacementETT.rounds
    roundsPositive := positiveB
    series := P.corresponding.replacementETT.series
    abovePenultimate := aboveB
    strictAbovePenultimate := strictB
    belowFinal := belowB
    generatingColoring := generatingB }

/-- Shared dependent data used by more than one proof branch. -/
abbrev parallelBase5019Conditions.{u_1, u_2} : Prop :=
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
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
   Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hp : HierarchyPathNumber H = (1 : ℕ)) (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (by omega) (by omega);
  let X : TreeSequence G e0 := TreeSequencePrefix T (T.length - (2 : ℕ)) (by omega) (by omega);
  ∀ (hTnX : TreeSequenceInitialSegment Tn X),
  let r : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀
   (missingTree :
    ∀ (U : TreeSequence G e0) (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X),
     TreeMissingColors sigma U = TreeMissingColors mu U)
   (minusEq :
    ∀ (U : TreeSequence G e0) (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X)
     (R : Finset (Fin k)),
     TreeColorSetMinusClosed G sigma U R ↔ TreeColorSetMinusClosed G mu U R)
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
   (terminalTree :
    corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc = Tn)
   (storedEq :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HierarchyStoredColorsAt KF j = HierarchyStoredColorsAt HB j),
  let n : Fin (corr.replacementETT.rounds + (1 : ℕ)) := Fin.last corr.replacementETT.rounds;
  let Tn : TreeSequence G e0 := corr.replacementETT.series.data.tree n.castSucc;
  corr.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE →
  ¬TreeColorSetMinusClosed G sigma bs.core
     ((HierarchyStoredColorsAt KF (0 : Fin (KF.dividerCount + (1 : ℕ)))).biUnion
      (goodB.gamma (0 : Fin (KF.dividerCount + (1 : ℕ))))) ∧
   (4 : ℕ) ≤
    ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma bs.closure : Finset (Fin k)) \
      (HierarchyStoredColorsAt KF (0 : Fin (KF.dividerCount + (1 : ℕ)))).biUnion
       (goodB.gamma (0 : Fin (KF.dividerCount + (1 : ℕ))))).card

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev transStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {X Y Z : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
    TreeSequenceInitialSegment Y Z →
    TreeSequenceInitialSegment X Z

/-- A common proof used by the branches of this transport or construction argument. -/
theorem trans.{u_1, u_2} : transStatement.{u_1, u_2} := by
  classical
  intro V E G e0 X Y Z hXY hYZ
  refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
  · intro i
    exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
  · intro i
    exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)

end GoldbergSeymour.SharedFacts.ShorteningTransport

end
