/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyTerminalPrefixRepackage
public import LeanPool.GoldbergSeymour.GoodHierarchyNewMissingClosed
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyLEMStable
public import LeanPool.GoldbergSeymour.HierarchyPathNumber
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HkuTreeColorsControlled
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.SameHierarchyStages
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeVertexOrder
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSpanningPath
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorComponentsDisjoint
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent
public import LeanPool.GoldbergSeymour.ParallelInterchangeability
public import LeanPool.GoldbergSeymour.HierarchyOrderedExitReduction
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.HierarchyStageInterchangeability
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Preparatory lemmas for hierarchy normalization

Extracted from Wesley Pegden’s Trellis formalization of the Goldberg–Seymour
theorem at 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas establish
properties used in the computed hierarchy records of `ChangeLemmaMixedNoClosed`.
-/

@[expose] public section

namespace GoldbergSeymour.MixedNoClosedTransport

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperParallelBase4040Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (alpha beta : Fin k),
   let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
   let vb : V := T.vertex ib;
   ∀ (coreToA : TreeSequenceInitialSegment base.core A) (TnToA : TreeSequenceInitialSegment Tn A)
    (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
     TreeSequencePrefix T (↑ib : ℕ)
      (have this : (1 : ℕ) ≤ A.length := A.positive;
      Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
      (Nat.le_of_lt_succ ib.isLt);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
     (aboveB :
      TreeSequenceInitialSegment (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ))))
       B)
     (strictB :
      (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length < B.length)
     (belowB : TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
     (genB : phi = ett.series.data.coloring (Fin.last ett.1))
     (baseB :
      HierarchyBase
       {
        rounds := ett.1, roundsPositive := rpB, series := ett.series, abovePenultimate := aboveB,
        strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := genB :
        ExtendedTashkinovTree G k e0 input B phi }
       phi)
     (hcoreB : baseB.core = base.core),
     let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      {
       rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
       abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
       generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
     let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
     ∀
      (treeMissingEq :
       ∀ (S : TreeSequence G e0) (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A),
        TreeMissingColors sigma S = TreeMissingColors phi S)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma)
      (closureBToA :
       ∀ (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE),
        TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A)
      (minusEq :
       ∀ (S : TreeSequence G e0) (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A)
        (D : Finset (Fin k)) (haD : alpha ∈ D),
        TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D)
      (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
       stages (0 : Fin (count + (2 : ℕ))) =
        {
         rounds := ett.1, roundsPositive := rpB, series := ett.series, abovePenultimate := aboveB,
           strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := genB :
           ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
         (Fin.last
           {
            rounds := ett.1, roundsPositive := rpB, series := ett.series,
             abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
             generatingColoring := genB :
             ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc)
      (hbterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hbnested :
       ∀ (j : Fin (count + (1 : ℕ))),
        TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hbstrict :
       ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (positions : Fin count → Fin (B.length + (1 : ℕ)))
      (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ))
      (hbincreasing :
       ∀ (i j : Fin count), (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
       ∀ (i : Fin count),
        stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
         TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i)
          (Nat.le_of_lt_succ (positions i).isLt))
      (hbcore :
       TreeSequenceInitialSegment baseB.core (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
      (goodB :
       GoodHierarchy
        {
         dividerCount := count, stage := stages, baseStage := hbbase, terminalStage := hbterminal,
         nested := hbnested, strict := hbstrict, dividerPosition := positions,
         dividerPositive := hbpositive, dividerIncreasing := hbincreasing,
         dividerStage := hbdivider, coreInsideFirst := hbcore :
         TashkinovHierarchy
          {
           rounds := ett.1, roundsPositive := rpB, series := ett.series,
           abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
           generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
          baseB })
      (reservedZeroB :
       alpha ∈
        (HierarchyStoredColorsAt
           {
            dividerCount := count, stage := stages, baseStage := hbbase,
            terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
            dividerPosition := positions, dividerPositive := hbpositive,
            dividerIncreasing := hbincreasing, dividerStage := hbdivider,
            coreInsideFirst := hbcore :
            TashkinovHierarchy
             {
              rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
              generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
             baseB }
           (0 :
            Fin
             ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                 {
                  rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                 baseB }.dividerCount +
              (1 : ℕ)))).biUnion
         (goodB.gamma
          (0 :
           Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
               terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
               dividerPosition := positions, dividerPositive := hbpositive,
               dividerIncreasing := hbincreasing, dividerStage := hbdivider,
               coreInsideFirst := hbcore :
               TashkinovHierarchy
                {
                 rounds := ett.1, roundsPositive := rpB, series := ett.series,
                 abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                 belowFinal := belowB, generatingColoring := genB :
                 ExtendedTashkinovTree G k e0 input B phi }
                baseB }.dividerCount +
             (1 : ℕ)))))
      (hcore : baseB.core = baseS.core)
      (hpe :
       { rounds := ett.1, roundsPositive := rpB, series := ett.series, abovePenultimate := aboveB,
            strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }.series.data.kind
          (Fin.last
           {
            rounds := ett.1, roundsPositive := rpB, series := ett.series,
             abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
             generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }.rounds) =
         some TashkinovExtensionKind.PE ↔
        corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
         some TashkinovExtensionKind.PE)
      (hclosure :
       {
        rounds := ett.1, roundsPositive := rpB, series := ett.series, abovePenultimate := aboveB,
            strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }.series.data.kind
          (Fin.last
           { rounds := ett.1, roundsPositive := rpB, series := ett.series,
             abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
             generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }.rounds) =
         some TashkinovExtensionKind.PE →
        baseB.closure = baseS.closure)
      (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
       ∀ (i j : Fin count), (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
       stages (0 : Fin (count + (2 : ℕ))) =
        corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
       ∀ (j : Fin (count + (1 : ℕ))),
        TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
       ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
       ∀ (i : Fin count),
        stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
         TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i)
          (Nat.le_of_lt_succ (positionsS i).isLt))
      (hscore :
       TreeSequenceInitialSegment baseS.core
        (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
      let HB : TashkinovHierarchy ettB baseB :=
       {
        dividerCount := count, stage := stages, baseStage := hbbase, terminalStage := hbterminal,
        nested := hbnested, strict := hbstrict, dividerPosition := positions,
        dividerPositive := hbpositive, dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
      let HS : TashkinovHierarchy corr.replacementETT baseS :=
       {
        dividerCount := count, stage := stages, baseStage := hsbase, terminalStage := hsterminal,
        nested := hsnested, strict := hsstrict, dividerPosition := positionsS,
        dividerPositive := hspositive, dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
      ∀
       (storedEq :
        ∀ (j : Fin (count + (1 : ℕ))), HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j),
       let n : Fin (corr.replacementETT.rounds + (1 : ℕ)) := Fin.last corr.replacementETT.rounds;
       let Tn : TreeSequence G e0 := corr.replacementETT.series.data.tree n.castSucc;
       corr.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE →
        ¬TreeColorSetMinusClosed G sigma baseS.core
           ((HierarchyStoredColorsAt HS (0 : Fin (HS.dividerCount + (1 : ℕ)))).biUnion
            (goodB.gamma (0 : Fin (HS.dividerCount + (1 : ℕ))))) ∧
         (4 : ℕ) ≤
          ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma baseS.closure : Finset (Fin k)) \
            (HierarchyStoredColorsAt HS (0 : Fin (HS.dividerCount + (1 : ℕ)))).biUnion
             (goodB.gamma (0 : Fin (HS.dividerCount + (1 : ℕ))))).card

theorem helper_parallelBase_4040.{u_1, u_2} :
    helperParallelBase4040Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb coreToA TnToA hAib
      B rpB aboveB strictB belowB genB baseB hcoreB ettB sigma treeMissingEq corr baseS
      closureBToA minusEq count stages hbbase hbterminal hbnested hbstrict positions hbpositive
      hbincreasing hbdivider hbcore goodB reservedZeroB hcore hpe hclosure positionsS hspositive
      hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS storedEq
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
    minusEq _ (by rw [hcoreB]; exact TreeSequenceInitialSegmentVertexSetSubset coreToA)
      _ reservedZeroB]
  exact goodB.parallelBase hpOld

end GoldbergSeymour.MixedNoClosedTransport

end
