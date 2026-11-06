/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.HierarchyCounterexample

/-!
# Shared facts for ChangeLemmaMixedLargestClosed

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.LargestClosedTransport

/-- Shared dependent data used by more than one proof branch. -/
abbrev storedEq7501Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (alpha beta : Fin k)
   (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
  let vb : V := T.vertex ib;
  ∀ (hAib : A.length < (↑ib : ℕ)),
  let B : TreeSequence G e0 := TreeSequencePrefix T (↑ib : ℕ) (by omega) (by omega);
  ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (ett.series.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))) B)
   (strictB :
    (ett.series.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
   (genB : phi = ett.series.data.coloring (Fin.last ett.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
      abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
     phi),
  let ettB : ExtendedTashkinovTree G k e0 input B phi :=
   {
    rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
    abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
    generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
  let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
  ∀
   (treeMissingEq :
    ∀ (S : TreeSequence G e0),
     TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
      TreeMissingColors sigma S = TreeMissingColors phi S)
   (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
   (baseS : HierarchyBase corr.replacementETT sigma)
   (storedS :
    TashkinovStoredColors corr.replacementETT.series.data (Fin.last corr.replacementETT.rounds) =
     Dn)
   (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
   (hbbase :
    stages (0 : Fin (count + (2 : ℕ))) =
     { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
      (Fin.last
        { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
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
   (starBToA :
    ∀
     (j :
      Fin
       ({ dividerCount := count, stage := stages, baseStage := hbbase,
          terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
          dividerPosition := positions, dividerPositive := hbpositive,
          dividerIncreasing := hbincreasing, dividerStage := hbdivider,
          coreInsideFirst := hbcore :
          TashkinovHierarchy
           {
            rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
            generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
           baseB }.dividerCount +
        (1 : ℕ))),
     TreeSequenceInitialSegment
      (HierarchyStarredStage
       {
        dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider, coreInsideFirst := hbcore :
        TashkinovHierarchy
         {
          rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
         baseB }
       j)
      A)
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
   (starEq :
    ∀ (j : Fin (count + (1 : ℕ))), HierarchyStarredStage HS j = HierarchyStarredStage HB j)
   (j : Fin (count + (1 : ℕ))),
  HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j

end GoldbergSeymour.SharedFacts.LargestClosedTransport

end
