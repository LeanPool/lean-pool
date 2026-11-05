/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChangeLemmaBothOutside.Preparation4

/-!
# ChangeLemmaBothOutside: supporting constructions, part 5

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.ChangeLemmaBothOutsidePreparation

/-- Dependent contract shared by the outside change lemma proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperRefreshEq5234Conditions.{u_1, u_2} : Prop :=
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
   let ell : ℕ := T.length - A.length;
   let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
   let Y : TreeSequence G e0 :=
    TreeSequencePrefix T yLength
     (have hA : (1 : ℕ) ≤ A.length := A.positive;
     have hT : (1 : ℕ) ≤ T.length := T.positive;
     have this : (1 : ℕ) ≤ T.length := T.positive;
     have this : (1 : ℕ) ≤ A.length := A.positive;
     by
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive A
     omega)
     (have this : (1 : ℕ) ≤ T.length := T.positive;
     have this : (1 : ℕ) ≤ A.length := A.positive;
     by
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive A
     omega);
   ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
     TreeSequencePrefix T (↑ib : ℕ)
      (have this : (1 : ℕ) ≤ A.length := A.positive;
      have this_1 : (1 : ℕ) ≤ T.length := T.positive;
      Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
      (have this : (1 : ℕ) ≤ T.length := T.positive;
      have this : (1 : ℕ) ≤ A.length := A.positive;
      by
      have := GoldbergSeymour.TreeSequence.positive T
      omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
     (aboveB :
      TreeSequenceInitialSegment
       (ett.series.data.tree
        (⟨ett.rounds,
          have this : (1 : ℕ) ≤ T.length := T.positive;
          have this : (1 : ℕ) ≤ A.length := A.positive;
          have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
          have this : (1 : ℕ) ≤ Y.length := Y.positive;
          have this : (1 : ℕ) ≤ B.length := B.positive;
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
         Fin (ett.rounds + (2 : ℕ))))
       B)
     (strictB :
      (ett.series.data.tree
         (⟨ett.rounds,
           have this : (1 : ℕ) ≤ T.length := T.positive;
           have this : (1 : ℕ) ≤ A.length := A.positive;
           have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
           have this : (1 : ℕ) ≤ Y.length := Y.positive;
           have this : (1 : ℕ) ≤ B.length := B.positive;
           by
           have := GoldbergSeymour.TreeSequence.positive T
           omega⟩ :
          Fin (ett.rounds + (2 : ℕ)))).length <
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
     (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
      ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
       (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
       (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
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
           (by
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.TreeSequence.positive A
            have := GoldbergSeymour.TreeSequence.positive B
            omega))
       (hbcore :
        TreeSequenceInitialSegment baseB.core
         (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
       (∀
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
              baseB }.stage
           j.castSucc)
          A) →
        ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
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
             (by
              have := GoldbergSeymour.TreeSequence.positive T
              have := GoldbergSeymour.TreeSequence.positive A
              have := GoldbergSeymour.TreeSequence.positive B
              omega))
         (hscore :
          TreeSequenceInitialSegment baseS.core
           (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
         let HB : TashkinovHierarchy ettB baseB :=
          {
           dividerCount := count, stage := stages, baseStage := hbbase,
           terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
           dividerPosition := positions, dividerPositive := hbpositive,
           dividerIncreasing := hbincreasing, dividerStage := hbdivider, coreInsideFirst := hbcore :
           TashkinovHierarchy ettB baseB };
         let HS : TashkinovHierarchy corr.replacementETT baseS :=
          {
           dividerCount := count, stage := stages, baseStage := hsbase,
           terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
           dividerPosition := positionsS, dividerPositive := hspositive,
           dividerIncreasing := hsincreasing, dividerStage := hsdivider, coreInsideFirst := hscore :
           TashkinovHierarchy corr.replacementETT baseS };
         (∀ (j : Fin (count + (1 : ℕ))), HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
          ∀ (i : Fin count),
           ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
               TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
             fun (v : V) ↦ MissingColors G sigma v) =
            (TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
               TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
             fun (v : V) ↦ MissingColors G phi v

theorem helper_refreshEq_5234.{u_1, u_2} :
    helperRefreshEq5234Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb ell yLength Y hAib
      B rpB aboveB strictB belowB genB baseB ettB sigma missingA corr baseS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS starEq i
  exact @helper_refreshEq_3407 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@missingA) (@corr)
      (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToA)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@starEq) (@i)

theorem helper_hstarLast_5289.{u_1, u_2} :
    helperHstarLast5289Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb ell yLength Y hAib
      B rpB aboveB strictB belowB genB baseB ettB sigma corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore hcountB hstagesB
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS starEq
  exact @helper_hstarLast_3462 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@corr) (@baseS)
      (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions)
      (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@hcountB) (@hstagesB)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@starEq)

/-- Dependent contract shared by the outside change lemma proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperPathLe5303Conditions.{u_1, u_2} : Prop :=
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
   let ell : ℕ := T.length - A.length;
   let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
   let Y : TreeSequence G e0 :=
    TreeSequencePrefix T yLength
     (have hA : (1 : ℕ) ≤ A.length := A.positive;
     have hT : (1 : ℕ) ≤ T.length := T.positive;
     have this : (1 : ℕ) ≤ T.length := T.positive;
     have this : (1 : ℕ) ≤ A.length := A.positive;
     by
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive A
     omega)
     (have this : (1 : ℕ) ≤ T.length := T.positive;
     have this : (1 : ℕ) ≤ A.length := A.positive;
     by
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive A
     omega);
   TreeSequenceInitialSegment A T →
    ∀ (hAib : A.length < (↑ib : ℕ)),
     let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
       (have this : (1 : ℕ) ≤ A.length := A.positive;
       have this_1 : (1 : ℕ) ≤ T.length := T.positive;
       Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
       (have this : (1 : ℕ) ≤ T.length := T.positive;
       have this : (1 : ℕ) ≤ A.length := A.positive;
       by
       have := GoldbergSeymour.TreeSequence.positive T
       omega);
     TreeSequenceInitialSegment B T →
      A.length < B.length →
       ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
        (aboveB :
         TreeSequenceInitialSegment
          (ett.series.data.tree
           (⟨ett.rounds,
             have this : (1 : ℕ) ≤ T.length := T.positive;
             have this : (1 : ℕ) ≤ A.length := A.positive;
             have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
             have this : (1 : ℕ) ≤ Y.length := Y.positive;
             have this : (1 : ℕ) ≤ B.length := B.positive;
             by
             have := GoldbergSeymour.TreeSequence.positive T
             omega⟩ :
            Fin (ett.rounds + (2 : ℕ))))
          B)
        (strictB :
         (ett.series.data.tree
            (⟨ett.rounds,
              have this : (1 : ℕ) ≤ T.length := T.positive;
              have this : (1 : ℕ) ≤ A.length := A.positive;
              have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
              have this : (1 : ℕ) ≤ Y.length := Y.positive;
              have this : (1 : ℕ) ≤ B.length := B.positive;
              by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
             Fin (ett.rounds + (2 : ℕ)))).length <
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
        ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
         (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
         (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0),
         stages (0 : Fin (count + (2 : ℕ))) =
           { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
              generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
              { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
                generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc →
          stages (Fin.last (count + (1 : ℕ))) = B →
           (∀ (j : Fin (count + (1 : ℕ))),
             TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ)) →
            (∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length) →
             ∀ (positions : Fin count → Fin (B.length + (1 : ℕ)))
              (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ)),
              (∀ (i j : Fin count),
                (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ)) →
               (∀ (i : Fin count),
                 stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
                  TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i)
                   (by
                    have := GoldbergSeymour.TreeSequence.positive T
                    have := GoldbergSeymour.TreeSequence.positive A
                    have := GoldbergSeymour.TreeSequence.positive B
                    omega)) →
                TreeSequenceInitialSegment baseB.core
                  (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))) →
                 ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
                  (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
                  (hsincreasing :
                   ∀ (i j : Fin count),
                    (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
                  (hsbase :
                   stages (0 : Fin (count + (2 : ℕ))) =
                    corr.replacementETT.series.data.tree
                     (Fin.last corr.replacementETT.rounds).castSucc)
                  (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
                  (hsnested :
                   ∀ (j : Fin (count + (1 : ℕ))),
                    TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
                  (hsstrict :
                   ∀ (j : Fin (count + (1 : ℕ))),
                    (stages j.castSucc).length < (stages j.succ).length)
                  (hsdivider :
                   ∀ (i : Fin count),
                    stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
                     TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i)
                      (by
                       have := GoldbergSeymour.TreeSequence.positive T
                       have := GoldbergSeymour.TreeSequence.positive A
                       have := GoldbergSeymour.TreeSequence.positive B
                       omega))
                  (hscore :
                   TreeSequenceInitialSegment baseS.core
                    (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
                  let HS : TashkinovHierarchy corr.replacementETT baseS :=
                   {
                    dividerCount := count, stage := stages, baseStage := hsbase,
                    terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
                    dividerPosition := positionsS, dividerPositive := hspositive,
                    dividerIncreasing := hsincreasing, dividerStage := hsdivider,
                    coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
                  HierarchyStarredStage HS (Fin.last count) = A →
                   HierarchyPathNumber HS ≤ HierarchyPathNumber H

theorem helper_pathLe_5303.{u_1, u_2} :
    helperPathLe5303Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb ell yLength Y AToT
      hAib B BToT ABstrict rpB aboveB strictB belowB genB baseB ettB sigma corr baseS count
      stages hbbase hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider
      hbcore positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider
      hscore HS hstarLast
  exact @helper_pathLe_3476 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@AToT)
      (@hAib) (@BToT) (@ABstrict) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
      (@corr) (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@positionsS)
      (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
      (@hsdivider) (@hscore) (@hstarLast)

end GoldbergSeymour.ChangeLemmaBothOutsidePreparation

end
