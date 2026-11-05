/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyStageInterchangeability
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition
public import LeanPool.GoldbergSeymour.GoodHierarchyTerminalPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure

/-!
# Change Lemma Mixed Closed Final

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation5185Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
   (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     {other : ExtendedTashkinovTree G k e0 input' T' generating'}
     {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
     other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
       ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
         (HierarchyCounterexampleMeasure C)) →
    ∀ (alpha beta : Fin k),
     alpha ≠ beta →
      let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
      let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
      let vb : V := T.vertex ib;
      TreeSequenceInitialSegment base.core A →
       TreeSequenceInitialSegment Tn A →
        TreeSequenceInitialSegment A T →
         (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
           TreeSequenceInitialSegment (H.stage j.castSucc) A) →
          ∀ (hAib : A.length < (↑ib : ℕ)),
           let B : TreeSequence G e0 :=
            TreeSequencePrefix T (↑ib : ℕ)
             (have this : (1 : ℕ) ≤ A.length := A.positive;
             by omega)
             (by omega);
           TreeSequenceInitialSegment B T →
            A.length < B.length →
             B.length < T.length →
              ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
               (aboveB :
                TreeSequenceInitialSegment
                 (ett.series.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))) B)
               (strictB :
                (ett.series.data.tree
                   (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
                 B.length)
               (belowB :
                TreeSequenceInitialSegment B
                 (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
               (genB : phi = ett.series.data.coloring (Fin.last ett.rounds))
               (baseB :
                HierarchyBase
                 {
                  rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                 phi),
               baseB.core = base.core →
                ∀
                 (HB :
                  TashkinovHierarchy
                   {
                    rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                   baseB)
                 (hcountB : HB.dividerCount = H.dividerCount),
                 (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
                   have jo : Fin (H.dividerCount + (1 : ℕ)) := Fin.cast (by omega) j;
                   HB.stage j.castSucc = H.stage jo.castSucc ∧
                    HierarchyStarredStage HB j = HierarchyStarredStage H jo) →
                  (∀ (i : Fin HB.dividerCount),
                    (↑(HB.dividerPosition i) : ℕ) =
                     (↑(H.dividerPosition (Fin.cast hcountB i)) : ℕ)) →
                   ∀ (goodB : GoodHierarchy HB),
                    (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
                      have jo : Fin (H.dividerCount + (1 : ℕ)) := Fin.cast (by omega) j;
                      HierarchyStoredColorsAt HB j = HierarchyStoredColorsAt H jo ∧
                       HierarchyStageMissingColors HB j = HierarchyStageMissingColors H jo ∧
                        ∀ (eta : Fin k),
                         goodB.gamma j eta = C.good.gamma jo eta ∧
                          HierarchySegmentColors HB j eta ⊆ HierarchySegmentColors H jo eta) →
                     let ettB : ExtendedTashkinovTree G k e0 input B phi :=
                      {
                       rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
                       abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                       belowFinal := belowB, generatingColoring := genB :
                       ExtendedTashkinovTree G k e0 input B phi };
                     let sigma : PartialEdgeColoring E k :=
                      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
                     (∀ v ∈ TreeSequenceVertexSet B,
                       v ≠ vb → MissingColors G sigma v = MissingColors G phi v) →
                      ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) →
                       (∀ v ∈ TreeSequenceVertexSet A,
                         MissingColors G sigma v = MissingColors G phi v) →
                        (∀ (S : TreeSequence G e0),
                          TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
                           TreeMissingColors sigma S = TreeMissingColors phi S) →
                         (∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
                          (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
                           ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
                            MaximumProperty corr.replacementETT →
                             ∀ (baseS : HierarchyBase corr.replacementETT sigma)
                              (HS : TashkinovHierarchy corr.replacementETT baseS),
                              SameHierarchyStages HB HS →
                               TashkinovStoredColors corr.replacementETT.series.data
                                  (Fin.last corr.replacementETT.rounds) =
                                 Dn →
                                corr.replacementETT.rounds = ett.rounds →
                                 (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
                                   TreeSequenceInitialSegment (HB.stage j.castSucc) A) →
                                  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
                                    TreeSequenceInitialSegment (HierarchyStarredStage HB j) A) →
                                   (∀ (j : Fin (HB.dividerCount + (2 : ℕ))),
                                     TreeSequenceInitialSegment (HB.stage j) B) →
                                    False

private abbrev helperContinuation5094Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
   IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
     LowerRoundInductionHypothesis G k e0 ett.rounds →
      (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        {other : ExtendedTashkinovTree G k e0 input' T' generating'}
        {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
        other.rounds = ett.rounds →
         C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
          ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
            (HierarchyCounterexampleMeasure C)) →
       ∀ (alpha beta : Fin k),
        alpha ≠ beta →
         let H : TashkinovHierarchy ett base := C.hierarchy;
         let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
         let A : TreeSequence G e0 := HierarchyStarredStage H q;
         let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
         let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
         let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
         let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
         let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
         let va : V := T.vertex ia;
         let vb : V := T.vertex ib;
         let ell : ℕ := T.length - A.length;
         let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
         let Y : TreeSequence G e0 :=
          TreeSequencePrefix T yLength
           (have hA : (1 : ℕ) ≤ A.length := A.positive;
           have hT : (1 : ℕ) ≤ T.length := T.positive;
           by omega)
           (by omega);
         (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
          (∀ {S U W : TreeSequence G e0},
            TreeSequenceInitialSegment S U →
             TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
           (∀ {S U W : TreeSequence G e0},
             TreeSequenceInitialSegment S W →
              TreeSequenceInitialSegment U W →
               S.length ≤ U.length → TreeSequenceInitialSegment S U) →
            TreeSequenceInitialSegment base.core A →
             TreeSequenceInitialSegment Tn A →
              TreeSequenceInitialSegment A T →
               (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                 TreeSequenceInitialSegment (H.stage j.castSucc) A) →
                (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                  TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
                 ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
                  alpha ∈
                     MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
                    (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
                   beta ∈
                      MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
                     (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
                    (∀ (i : Fin (T.length + (1 : ℕ))),
                      (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
                     vb ∈ TreeSequenceVertexSet Y →
                      va ∈ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A →
                       ∀ (hAib : A.length < (↑ib : ℕ)),
                        TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T alpha))
                           (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
                          alpha ∉
                           ({c : Fin k |
                             ∃ (t : Fin T.length),
                              (HierarchyStarredStage C.hierarchy
                                  (Fin.last C.hierarchy.dividerCount)).length ≤
                                (↑t : ℕ) ∧
                               (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ∧
                                phi (T.edge t) = some c} :
                            Finset (Fin k)) →
                         va ≠ vb →
                          let B : TreeSequence G e0 :=
                           TreeSequencePrefix T (↑ib : ℕ)
                            (have this : (1 : ℕ) ≤ A.length := A.positive;
                            Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
                            (by omega);
                          TreeSequenceInitialSegment B T →
                           TreeSequenceInitialSegment A B →
                            A.length < B.length →
                             B.length < T.length →
                              ∀ (rpB : (1 : ℕ) ≤ ett.1)
                               (aboveB :
                                TreeSequenceInitialSegment
                                 (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ))))
                                 B)
                               (strictB :
                                (ett.series.data.tree
                                   (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
                                 B.length)
                               (belowB :
                                TreeSequenceInitialSegment B
                                 (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
                               (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
                               MaximumProperty
                                 {
                                  rounds := ett.1, roundsPositive := rpB, series := ett.series,
                                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                                  belowFinal := belowB, generatingColoring := genB :
                                  ExtendedTashkinovTree G k e0 input B phi } →
                                ∀
                                 (baseB :
                                  HierarchyBase
                                   {
                                    rounds := ett.1, roundsPositive := rpB, series := ett.series,
                                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                                    belowFinal := belowB, generatingColoring := genB :
                                    ExtendedTashkinovTree G k e0 input B phi }
                                   phi),
                                 baseB.core = base.core →
                                  ∀
                                   (HB :
                                    TashkinovHierarchy
                                     {
                                      rounds := ett.1, roundsPositive := rpB, series := ett.series,
                                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                                      belowFinal := belowB, generatingColoring := genB :
                                      ExtendedTashkinovTree G k e0 input B phi }
                                     baseB)
                                   (hcountB : HB.dividerCount = H.dividerCount),
                                   (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
                                     have jo : Fin (H.dividerCount + (1 : ℕ)) :=
                                      Fin.cast (by omega) j;
                                     HB.stage j.castSucc = H.stage jo.castSucc ∧
                                      HierarchyStarredStage HB j = HierarchyStarredStage H jo) →
                                    (∀ (i : Fin HB.dividerCount),
                                      (↑(HB.dividerPosition i) : ℕ) =
                                       (↑(H.dividerPosition (Fin.cast hcountB i)) : ℕ)) →
                                     ∀ (goodB : GoodHierarchy HB),
                                      (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
                                        have jo : Fin (H.dividerCount + (1 : ℕ)) :=
                                         Fin.cast (by omega) j;
                                        HierarchyStoredColorsAt HB j =
                                          HierarchyStoredColorsAt H jo ∧
                                         HierarchyStageMissingColors HB j =
                                           HierarchyStageMissingColors H jo ∧
                                          ∀ (eta : Fin k),
                                           goodB.gamma j eta = C.good.gamma jo eta ∧
                                            HierarchySegmentColors HB j eta ⊆
                                             HierarchySegmentColors H jo eta) →
                                       let _ : ExtendedTashkinovTree G k e0 input B phi :=
                                        {
                                         rounds := ett.rounds, roundsPositive := rpB,
                                         series := ett.series, abovePenultimate := aboveB,
                                         strictAbovePenultimate := strictB, belowFinal := belowB,
                                         generatingColoring := genB :
                                         ExtendedTashkinovTree G k e0 input B phi };
                                       let K : Set (V ⊕ E) :=
                                        TwoColorComponent G phi alpha beta (Sum.inl vb);
                                       let sigma : PartialEdgeColoring E k :=
                                        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
                                       (∀ v ∈ TreeSequenceVertexSet A, Sum.inl v ∉ K) →
                                        (have C : Set (V ⊕ E) :=
                                          TwoColorComponent G phi alpha beta (Sum.inl vb);
                                         have phi' : PartialEdgeColoring E k :=
                                          TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
                                         (∀ (v : V),
                                           Sum.inl v ∉ C →
                                            MissingColors G phi' v = MissingColors G phi v) ∧
                                          (∀ (v : V),
                                            Sum.inl v ∈ C →
                                             alpha ∈ MissingColors G phi v →
                                              beta ∈ MissingColors G phi' v) ∧
                                           (∀ (v : V),
                                             Sum.inl v ∈ C →
                                              beta ∈ MissingColors G phi v →
                                               alpha ∈ MissingColors G phi' v) ∧
                                            ∀ (v : V) (c : Fin k),
                                             c ≠ alpha →
                                              c ≠ beta →
                                               (c ∈ MissingColors G phi' v ↔
                                                c ∈ MissingColors G phi v)) →
                                         (∀ (f : E),
                                           phi f ≠ some alpha →
                                            phi f ≠ some beta → sigma f = phi f) →
                                          IsProperEdgeColoring G sigma →
                                           IsOneEdgeUncolored sigma e0 →
                                            va ∈ TreeSequenceVertexSet B →
                                             vb ∈ TreeSequenceVertexSet B →
                                              (∀ v ∈ TreeSequenceVertexSet B,
                                                v ≠ vb →
                                                 MissingColors G sigma v = MissingColors G phi v) →
                                               alpha ∈ MissingColors G sigma va → False

private abbrev helperContinuation5074Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
   IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
     LowerRoundInductionHypothesis G k e0 ett.rounds →
      (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (other : ExtendedTashkinovTree G k e0 input' T' generating'),
        other.rounds = ett.rounds →
         MaximumProperty other →
          ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
           (_ : GoodHierarchy K),
           K.dividerCount < C.hierarchy.dividerCount →
            ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
       (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
         {generating' : PartialEdgeColoring E k}
         {other : ExtendedTashkinovTree G k e0 input' T' generating'}
         {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
         other.rounds = ett.rounds →
          C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
           ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
             (HierarchyCounterexampleMeasure C)) →
        (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
         let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
         (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card) →
         ∀ (alpha beta : Fin k),
          alpha ≠ beta →
           (let H : TashkinovHierarchy ett base := C.hierarchy;
            let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
            let A : TreeSequence G e0 := HierarchyStarredStage H q;
            let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
            let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
            alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A →
             TreeVertexOrder T (T.vertex ia) (T.vertex ib) ∧
              alpha ∉
               ({c : Fin k |
                 ∃ (t : Fin T.length),
                  A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
                Finset (Fin k))) →
            (let H : TashkinovHierarchy ett base := C.hierarchy;
             let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
             let A : TreeSequence G e0 := HierarchyStarredStage H q;
             alpha ∈ TreeMissingColors phi A ∧
              TreeColorSetClosed G phi A ({ alpha } : Finset (Fin k))) →
             let H : TashkinovHierarchy ett base := C.hierarchy;
             let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
             let A : TreeSequence G e0 := HierarchyStarredStage H q;
             let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
             let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
             let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
             let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
             let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
             let va : V := T.vertex ia;
             let vb : V := T.vertex ib;
             let ell : ℕ := T.length - A.length;
             let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
             let Y : TreeSequence G e0 :=
              TreeSequencePrefix T yLength
               (have hA : (1 : ℕ) ≤ A.length := A.positive;
               have hT : (1 : ℕ) ≤ T.length := T.positive;
               Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
               (by omega);
             (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
              (∀ {S U W : TreeSequence G e0},
                TreeSequenceInitialSegment S U →
                 TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
               (∀ {S U W : TreeSequence G e0},
                 TreeSequenceInitialSegment S W →
                  TreeSequenceInitialSegment U W →
                   S.length ≤ U.length → TreeSequenceInitialSegment S U) →
                (H.dividerCount = (0 : ℕ) → A = base.core) →
                 (H.dividerCount ≠ (0 : ℕ) →
                   A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
                  TreeSequenceInitialSegment base.core A →
                   TreeSequenceInitialSegment Tn A →
                    TreeSequenceInitialSegment A T →
                     (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                       TreeSequenceInitialSegment (H.stage j.castSucc) A) →
                      (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                        TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
                       TreeSequenceInitialSegment Y T →
                        ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
                         alpha ∈
                            MissingColors G phi
                             (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
                           (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
                          beta ∈
                             MissingColors G phi
                              (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
                            (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
                           (∀ (i : Fin (T.length + (1 : ℕ))),
                             (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
                            va ∈ TreeSequenceVertexSet Y →
                             vb ∈ TreeSequenceVertexSet Y →
                              va ∈ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A →
                               A.length < (↑ib : ℕ) →
                                (∀ (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
                                  c ∈ MissingColors G phi (T.vertex i) →
                                   T.vertex i ∈ TreeSequenceVertexSet Y →
                                    T.vertex i ∉ TreeSequenceVertexSet A →
                                     c ∉ TreeMissingColors phi A) →
                                 let H : TashkinovHierarchy ett base := C.hierarchy;
                                 let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                                 let A : TreeSequence G e0 := HierarchyStarredStage H q;
                                 let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
                                 let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
                                 let sameComponent : Prop :=
                                  TwoColorComponent G phi alpha beta (Sum.inl va) =
                                   TwoColorComponent G phi alpha beta (Sum.inl vb);
                                 sameComponent ∧ TreeInterchangeable G A phi alpha beta

private theorem helper_segTrans_199.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S U →
    TreeSequenceInitialSegment U W →
    TreeSequenceInitialSegment S W := by
  classical
  intro V E G e0 S U W hSU hUW
  refine ⟨le_trans hSU.1 hUW.1, ?_, ?_⟩
  · intro i
    exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
  · intro i
    exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)

private theorem helper_commonPrefix_209.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S W →
    TreeSequenceInitialSegment U W →
    S.length ≤ U.length →
    TreeSequenceInitialSegment S U := by
  classical
  intro V E G e0 S U W hSW hUW hlen
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
  · intro i
    exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)

private theorem helper_stageSegment_219.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
    TreeSequenceInitialSegment (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
      (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H segRefl segTrans a d hbound
  induction d with
  | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
  | succ d ih =>
    exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)

private theorem helper_stageToT_227.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))),
    TreeSequenceInitialSegment (H.stage j) T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H stageSegment j
  have hs := stageSegment j.val (H.dividerCount + 1 - j.val) (by omega)
  have he : (⟨j.val + (H.dividerCount + 1 - j.val), by omega⟩ :
      Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
    Fin.ext (by simp only [Fin.val_last]; have := j.isLt; omega)
  simpa [he, H.terminalStage] using hs

private theorem helper_lastPositive_238.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    H.dividerCount ≠ (0 : ℕ) →
    A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hz
  obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
  · have hv := congrArg Fin.val hzero
    simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, q] at hv
    exact (hz hv).elim
  · simp only [A, HierarchyStarredStage, hi, Fin.cases_succ]
    congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hi
    simpa [q] using hv.symm

private theorem helper_coreToA_250.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment base.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A segRefl segTrans stageSegment lastZero
      lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]
    exact segRefl _
  · rw [lastPositive hz]
    have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
    have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
    simpa [he] using segTrans H.coreInsideFirst hs

private theorem helper_TnToCore_259.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    TreeSequenceInitialSegment Tn base.core := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base n Tn segRefl
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · exact (Classical.choice (base.parallel hp).2.2).leftSegment
  · rw [base.nonparallel hp]
    exact segRefl _

private theorem helper_AToT_266.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage j) T) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A segTrans stageToT lastZero lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]
    exact segTrans H.coreInsideFirst (stageToT ⟨1, by omega⟩)
  · rw [lastPositive hz]
    exact stageToT _

private theorem helper_ordinaryToA_273.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment Tn A →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (H.stage j.castSucc) A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n Tn stageSegment lastZero lastPositive
      TnToA j
  by_cases hz : H.dividerCount = 0
  · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp; omega)
    rw [hj, H.baseStage]
    exact TnToA
  · have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
    rw [lastPositive hz]
    convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;>
      simp only [Fin.val_castSucc]; omega

private theorem helper_firstMissing_293.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment Y T →
    ∀ c ∈ TreeMissingColors phi Y,
    c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
      (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ Y.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A ell yLength Y YToT c hc
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
  obtain ⟨i, hi⟩ := hv
  let it := Fin.castLE (Nat.succ_le_succ YToT.1) i
  have hci : c ∈ MissingColors G phi (T.vertex it) := by
    rw [YToT.2.1 i, hi]
    exact hcv
  let candidates := Finset.univ.filter fun j => c ∈ MissingColors G phi (T.vertex j)
  have hit : it ∈ candidates := by simp [candidates, hci]
  have hnon : candidates.Nonempty := ⟨it, hit⟩
  have hmem := Finset.min'_mem candidates hnon
  have hle := Finset.min'_le candidates it hit
  refine ⟨?_, ?_⟩
  · simpa [HierarchyFirstMissingPosition, candidates, hnon] using
      (Finset.mem_filter.mp hmem).2
  · have hiv : it.val ≤ Y.length := Nat.le_of_lt_succ i.isLt
    have hval : (candidates.min' hnon).val ≤ it.val := hle
    simpa [HierarchyFirstMissingPosition, candidates, hnon] using le_trans hval hiv

private theorem helper_outsideIndex_325.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    TreeSequenceInitialSegment A T →
    ∀ (i : Fin (T.length + (1 : ℕ))),
    T.vertex i ∉ TreeSequenceVertexSet A →
    A.length < (↑i : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A AToT i hi
  by_contra h
  have hle : i.val ≤ A.length := by omega
  apply hi
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨i.val, by omega⟩, (AToT.2.1 ⟨i.val, by omega⟩).symm⟩

private theorem helper_missingNotA_336.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    TreeSequenceInitialSegment A Y →
    ∀ (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
    c ∈ MissingColors G phi (T.vertex i) →
    T.vertex i ∈ TreeSequenceVertexSet Y →
    T.vertex i ∉ TreeSequenceVertexSet A →
    c ∉ TreeMissingColors phi A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A ell yLength Y hElementaryY
      AToY c i hmi hiy hia
  clear * - hmi hiy hia AToY hElementaryY
  intro hc
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  have hne : v ≠ T.vertex i := by intro he; exact hia (he ▸ hv)
  exact (Finset.disjoint_left.mp
    (hElementaryY (TreeSequenceInitialSegmentVertexSetSubset AToY hv) hiy hne)) hcv hmi

private theorem helper_habIndex_350.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k),
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T alpha))
          (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        alpha ∉
          ({c : Fin k |
              ∃ (t : Fin T.length),
                (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length ≤
                    (↑t : ℕ) ∧
                  (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ∧
                    phi (T.edge t) = some c} :
            Finset (Fin k)) →
    (↑ia : ℕ) < (↑ib : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta ia ib horder
  obtain ⟨i, j, hi, hj, hij⟩ := horder.1
  have hei := T.vertex_injective hi
  have hej := T.vertex_injective hj
  simpa [hei, hej] using hij

private theorem helper_BstrictT_369.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment A T →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    A.length < B.length →
    TreeSequenceInitialSegment B Y →
    B.length < T.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib ell yLength Y AToT hAib B
      ABstrict BToY
  clear * - AToT BToY ABstrict Y
  have hAT := AToT.1
  have hY : Y.length = min (A.length + (T.length - A.length - 1)) T.length := rfl
  have hBY := BToY.1
  have hAB := ABstrict
  omega

private theorem helper_branch_392.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    alpha ∈ TreeMissingColors phi A →
    TreeColorSetClosed G phi A ({ alpha } : Finset (Fin k)) →
    H.dividerCount = (0 : ℕ) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    TreeInterchangeable G base.core phi alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn Dn
      lastZero halphaA halphaClosed hz hp
  have hs : CombinedStableColoring Tn base.closure Dn phi phi :=
    ⟨⟨(by intros; rfl), (by intros; rfl)⟩,
      ⟨(by intros; rfl), (by intros; rfl)⟩⟩
  exact (interchange G k e0 input T phi phi ett C.maximum C.positive
    hlower hp base hproper hone hs alpha beta).2.2.1
    (by simpa [lastZero hz] using halphaA)
    (by simpa [lastZero hz] using halphaClosed)

private theorem helper_branch_399.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    alpha ∈ TreeMissingColors phi A →
    H.dividerCount = (0 : ℕ) →
    ¬ett.series.data.kind n = some TashkinovExtensionKind.PE →
    TreeInterchangeable G base.core phi alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn
      lastZero halphaA hz hp
  rw [base.nonparallel hp]
  let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
  have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
  have hprev : StableColoring Tn
      (TashkinovStoredColors ett.series.data j.castSucc)
      (ett.series.data.coloring j.castSucc) phi := by
    have step := ett.series.certified n
    generalize hi : n = i at step
    cases step with
    | initial =>
      have hv := congrArg Fin.val hi
      simp [n] at hv
      have := C.positive
      omega
    | SE ji _ _ _ _ _ choice _ coloring stored edges kind vertex outside
        delta gamma seed adjoin closure ordered strict =>
      have hji : ji = j := Fin.ext (by
        have hv := congrArg Fin.val hi
        simp [n, j] at hv ⊢
        omega)
      subst ji
      have hc : phi = choice.selected := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simpa only [hj, Tn, hc] using choice.selectedStable
    | RE ji _ _ _ _ available coloring stored edges kind vertex outside
        delta gamma seed adjoin closure ordered strict =>
      have hji : ji = j := Fin.ext (by
        have hv := congrArg Fin.val hi
        simp [n, j] at hv ⊢
        omega)
      subst ji
      have hc : phi = ett.series.data.coloring j.castSucc := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      refine ⟨?_, ?_⟩
      · intro f _ _
        exact congrFun hc f
      · intro v _
        exact congrArg (fun psi => MissingColors G psi v) hc
    | PE ji _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper
        one stored edges kind vertex outside delta gammaEq closure ordered strict =>
      exact (hp (by simpa [← hi] using kind)).elim
  have hm : alpha ∈ TreeMissingColors phi Tn := by
    simpa only [lastZero hz, base.nonparallel hp] using halphaA
  by_cases hn : 1 < ett.rounds
  · obtain ⟨lower, hr, hmax, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T phi ett C.maximum
        (ett.rounds - 1) (by omega) (by omega)
    let nl : Fin (lower.rounds + 1) := Fin.last lower.rounds
    have hcidx : Fin.castLE (by omega) nl = j.castSucc :=
      Fin.ext (by simp [nl, j, hr])
    have htidx : Fin.castLE (by omega) (Fin.last (lower.rounds + 1)) =
        n.castSucc := Fin.ext (by simp [n, hr]; omega)
    have ht : lower.series.data.tree (Fin.last (lower.rounds + 1)) = Tn :=
      (htrees _).trans (congrArg ett.series.data.tree htidx)
    obtain ⟨hc, _, _, _, _, _, _, _, hd, _⟩ := hdata nl
    rw [hcidx] at hc hd
    have hs : StableColoring
        (lower.series.data.tree (Fin.last (lower.rounds + 1)))
        (TashkinovStoredColors lower.series.data nl)
        (lower.series.data.coloring nl) phi := by
      rw [ht, hc, hd]
      exact hprev
    have hi := (hlower lower (by omega) (by omega) hmax).2.1
      phi hproper hone hs alpha beta (Or.inl (by rw [ht]; exact hm))
    simpa only [ht] using hi
  · have hn1 : ett.rounds = 1 := by have := C.positive; omega
    have hj0 : j.castSucc = (0 : Fin (ett.rounds + 1)) :=
      Fin.ext (by simp [j, hn1])
    have ht1 : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext (by simp [n, hn1])
    have hs : StableColoring (ett.series.data.tree ⟨1, by omega⟩)
        (TashkinovStoredColors ett.series.data 0)
        (ett.series.data.coloring 0) phi := by
      simpa only [Tn, ht1, hj0] using hprev
    have hi := (TechnicalTheoremBase G k ett.rounds e0 input ett.series).2
      phi hproper hone hs alpha beta
      (Or.inl (by simpa only [Tn, ht1] using hm))
    have hTn1 : Tn = ett.series.data.tree ⟨1, by omega⟩ :=
      congrArg ett.series.data.tree ht1
    change TreeInterchangeable G Tn phi alpha beta
    rw [hTn1]
    exact hi

private theorem helper_branch_481.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (other : ExtendedTashkinovTree G k e0 input' T' generating'),
        other.rounds = ett.rounds →
          MaximumProperty other →
            ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
              (_ : GoodHierarchy K),
              K.dividerCount < C.hierarchy.dividerCount →
                ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
    (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card) →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    alpha ∈ TreeMissingColors phi A →
    TreeColorSetClosed G phi A ({ alpha } : Finset (Fin k)) →
    ¬H.dividerCount = (0 : ℕ) →
    TreeInterchangeable G A phi alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hlarge alpha beta
      hne H q A lastPositive halphaA halphaClosed hz
  let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
  have hi : i.succ.castSucc = (⟨H.dividerCount, by omega⟩ :
      Fin (H.dividerCount + 2)) := Fin.ext (by simp [i]; omega)
  rw [lastPositive hz]
  rw [← hi]
  apply step1 G k e0 input T phi ett C.maximum C.positive hproper hone
    hlower base H C.good hfewer hlarge i alpha beta
  · simpa [hi, ← lastPositive hz] using halphaA
  · exact hne
  · simpa [hi, ← lastPositive hz] using halphaClosed

private theorem helper_pathMissing_495.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
      (k : ℕ) (phi : PartialEdgeColoring E k),
    IsProperEdgeColoring G phi →
    ∀ (v : V) (c d : Fin k),
    c ≠ d →
    c ∈ MissingColors G phi v →
    TwoColorPathComponent G phi c d (Sum.inl v) := by
  classical
  intro V E _ _ G k phi hproper v c d hcd hc
  let _ := Fintype.ofFinite V
  refine ⟨hcd, Sum.inl v, rfl, ?_⟩
  intro x hx y hy
  cases x with
  | inr f =>
    cases y with
    | inr g =>
      have hfc : phi f = some d := hx.2.resolve_left (by
        intro he
        exact (Finset.mem_sdiff.mp hc).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hx.1, he⟩))
      have hgc : phi g = some d := hy.2.resolve_left (by
        intro he
        exact (Finset.mem_sdiff.mp hc).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hy.1, he⟩))
      congr 1
      by_contra hfg
      exact hproper hfg ⟨v, hx.1, hy.1⟩ hfc hgc
    | inl w => exact False.elim hy
  | inl w => exact False.elim hx

private theorem helper_pathB_520.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    TwoColorPathComponent G phi alpha beta (Sum.inl vb) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper alpha beta hne H q A ib vb ell yLength
      Y hb
  refine ⟨hne, Sum.inl vb, rfl, ?_⟩
  intro x hx y hy
  cases x with
  | inr f =>
    cases y with
    | inr g =>
      have hfc : phi f = some alpha := hx.2.resolve_right (by
        intro he
        exact (Finset.mem_sdiff.mp hb.1).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hx.1, he⟩))
      have hgc : phi g = some alpha := hy.2.resolve_right (by
        intro he
        exact (Finset.mem_sdiff.mp hb.1).2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hy.1, he⟩))
      congr 1
      by_contra hfg
      exact hproper hfg ⟨vb, hx.1, hy.1⟩ hfc hgc
    | inl w => exact False.elim hy
  | inl w => exact False.elim hx

private theorem helper_unaffected_555.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
          PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k),
      alpha ≠ beta →
        let H : TashkinovHierarchy ett base := C.hierarchy;
        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
        let A : TreeSequence G e0 := HierarchyStarredStage H q;
        let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
        let vb : V := T.vertex ib;
        let ell : ℕ := T.length - A.length;
        let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
        let Y : TreeSequence G e0 :=
          TreeSequencePrefix T yLength
            (have hA : (1 : ℕ) ≤ A.length := A.positive;
            have hT : (1 : ℕ) ≤ T.length := T.positive;
            Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
            (by omega);
        alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
            (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
          beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
              (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
            let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
            let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta
                (Sum.inl vb);
            ∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A ib vb ell yLength Y ha hb
      K sigma f c hca hcb
  clear * - hca hcb K sigma hne
  by_cases hf : Sum.inr f ∈ K
  · by_cases ha : phi f = some alpha
    · simp [sigma, TwoColorComponentSwap, K, hf, ha, hca.symm, hcb.symm]
    · by_cases hb : phi f = some beta
      · simp [sigma, TwoColorComponentSwap, K, hf, hb, hne.symm,
          hca.symm, hcb.symm]
      · simp [sigma, TwoColorComponentSwap, K, hf, ha, hb]
  · simp [sigma, TwoColorComponentSwap, K, hf]

private theorem helper_sigmaOne_572.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsOneEdgeUncolored phi e0 →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hone alpha beta hne H q A ib vb ell yLength Y
      ha hb K sigma unaffected
  clear * - hone sigma K unaffected hne
  refine ⟨?_, ?_⟩
  · simp [sigma, TwoColorComponentSwap, hone.1]
  · intro f hf
    obtain ⟨c, hc⟩ := hone.2 f hf
    by_cases ha : c = alpha
    · subst c
      by_cases hK : Sum.inr f ∈ K
      · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
      · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
    · by_cases hb : c = beta
      · subst c
        by_cases hK : Sum.inr f ∈ K
        · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, K, hK, hc, hne.symm]⟩
        · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
      · exact ⟨c, (unaffected f c ha hb).mpr hc⟩

private theorem helper_missingBefore_597.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let va : V := T.vertex ia;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    va ∈ TreeSequenceVertexSet Y →
    vb ∈ TreeSequenceVertexSet Y →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B Y →
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    Sum.inl va ∉ K →
    (have C : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
      have phi' : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G phi v) ∧
        (∀ (v : V),
            Sum.inl v ∈ C → alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v) ∧
          (∀ (v : V),
              Sum.inl v ∈ C →
                beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi' v) ∧
            ∀ (v : V) (c : Fin k),
              c ≠ alpha →
                c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G phi v)) →
    (∀ {v : V} {f : E},
        Sum.inl v ∈ K →
          Incident G v f → phi f = some alpha ∨ phi f = some beta → Sum.inr f ∈ K) →
    ∀ v ∈ TreeSequenceVertexSet B,
    v ≠ vb →
    MissingColors G sigma v = MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A ia ib va vb ell yLength Y
      hElementaryY ha hb haY hbY hAib B BToY K sigma haK behavior edgeOfVertex v hv hvb
  by_cases hvK : Sum.inl v ∈ K
  · have hva : v ≠ va := by intro he; exact haK (he ▸ hvK)
    have hvY := TreeSequenceInitialSegmentVertexSetSubset BToY hv
    have han : alpha ∉ MissingColors G phi v := fun hc =>
      Finset.disjoint_left.mp (hElementaryY hvY haY hva) hc ha.1
    have hbn : beta ∉ MissingColors G phi v := fun hc =>
      Finset.disjoint_left.mp (hElementaryY hvY hbY hvb) hc hb.1
    have hpa : ∃ f, Incident G v f ∧ phi f = some alpha := by
      simpa [MissingColors, PresentColors] using han
    have hpb : ∃ f, Incident G v f ∧ phi f = some beta := by
      simpa [MissingColors, PresentColors] using hbn
    obtain ⟨fa, hfa, hfca⟩ := hpa
    obtain ⟨fb, hfb, hfcb⟩ := hpb
    have hfaK := edgeOfVertex hvK hfa (Or.inl hfca)
    have hfbK := edgeOfVertex hvK hfb (Or.inr hfcb)
    have hnewa : sigma fb = some alpha := by
      simp [sigma, TwoColorComponentSwap, K, hfbK, hfcb, hne.symm]
    have hnewb : sigma fa = some beta := by
      simp [sigma, TwoColorComponentSwap, K, hfaK, hfca]
    have hana : alpha ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter, not_not]
      exact ⟨fb, hfb, hnewa⟩
    have hbnb : beta ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter, not_not]
      exact ⟨fa, hfa, hnewb⟩
    ext c
    by_cases hca : c = alpha
    · subst c; simp [hana, han]
    · by_cases hcb : c = beta
      · subst c; simp [hbnb, hbn]
      · exact behavior.2.2.2 v c hca hcb
  · exact behavior.1 v hvK

private theorem helper_incidentFixed_651.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet A, Sum.inl v ∉ K) →
    (∀ (f : E), phi f ≠ some alpha → phi f ≠ some beta → sigma f = phi f) →
    ∀ (f : E),
    TreeIncidentEdge A f →
    sigma f = phi f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb ell yLength Y ha hb K
      sigma avoidA fixedValue f hf
  clear * - hf sigma K avoidA fixedValue
  obtain ⟨v, hv, hvf⟩ := hf
  by_cases hK : Sum.inr f ∈ K
  · by_cases ha : phi f = some alpha
    · exact False.elim (avoidA v hv
        ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) (Sum.inr f)
            from ⟨hvf, Or.inl ha⟩)).trans hK))
    · by_cases hb : phi f = some beta
      · exact False.elim (avoidA v hv
          ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            (show (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) (Sum.inr f)
              from ⟨hvf, Or.inr hb⟩)).trans hK))
      · exact fixedValue f ha hb
  · simp [sigma, TwoColorComponentSwap, K, hK]

private theorem helper_stable_667.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    (∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
    ∀ (D : Finset (Fin k)),
    StableColoring S D phi sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb sigma missingA
      incidentFixed S hS D
  refine ⟨?_, fun v hv => missingA v (hS hv)⟩
  intro f hf _
  obtain ⟨v, hv, hvf⟩ := hf
  exact incidentFixed f ⟨v, hS hv, hvf⟩

private theorem helper_terminalRoute_680.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S W →
          TreeSequenceInitialSegment U W →
            S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment Tn B →
    Tn.length < B.length →
    TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn B ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib commonPrefix hAib B
      TnToB TnStrictB BToFinal
  clear * - ett C n Tn B BToFinal TnToB TnStrictB commonPrefix
  have step := ett.series.certified n
  generalize hi : n = i at step
  cases step with
  | initial => have hv := congrArg Fin.val hi; simp [n] at hv; have := C.positive; omega
  | SE j _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
    have hseedB : TreeSequenceInitialSegment seed B :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
        BToFinal (by
            have hl := adjoin.1
            rw [hj] at hl
            change seed.length = Tn.length + 1 at hl
            omega)
    exact Or.inr ⟨Or.inl (by simpa [hj] using kind), choice.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      TashkinovAugmentationSequenceRestrict phi seed B _ hroute hseedB BToFinal⟩
  | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
      edges kind vertex outside delta gammaEq closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    refine Or.inl ⟨by simpa [hj] using kind, ?_⟩
    apply TashkinovAugmentationSequenceRestrict phi Tn B _ _ TnToB BToFinal
    simpa [Tn, hj, hlast, ← ett.generatingColoring, n] using closure.1
  | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
    have hseedB : TreeSequenceInitialSegment seed B :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
        BToFinal (by
            have hl := adjoin.1
            rw [hj] at hl
            change seed.length = Tn.length + 1 at hl
            omega)
    exact Or.inr ⟨Or.inr (by simpa [hj] using kind), available.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      TashkinovAugmentationSequenceRestrict phi seed B _ hroute hseedB BToFinal⟩

private theorem helper_displayedIncident_729.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (S : TreeSequence G e0),
    TreeSequenceInitialSegment S A →
    ∀ (t : Fin S.length),
    TreeIncidentEdge A (S.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A S hSA t
  obtain ⟨i, hi⟩ := S.attaches t
  refine ⟨S.vertex t.succ, TreeSequenceInitialSegmentVertexSetSubset hSA
    (by simp [TreeSequenceVertexSet]), ?_⟩
  simp [Incident, hi]

private theorem helper_augmentationFixed_737.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    (∀ (i : Fin (T.length + (1 : ℕ))),
        (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
    vb ∈ TreeSequenceVertexSet Y →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T alpha))
          (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        alpha ∉
          ({c : Fin k |
              ∃ (t : Fin T.length),
                (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length ≤
                    (↑t : ℕ) ∧
                  (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ∧
                    phi (T.edge t) = some c} :
            Finset (Fin k)) →
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    TreeSequenceInitialSegment A B →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E), phi f ≠ some alpha → phi f ≠ some beta → sigma f = phi f) →
    (∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A →
          ∀ (t : Fin S.length), TreeIncidentEdge A (S.edge t)) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S B →
    ∀ (t : Fin B.length),
    S.length ≤ (↑t : ℕ) →
    sigma (B.edge t) = phi (B.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb ell yLength Y segRefl
      hElementaryY hb vertexY hbY hAib horder B BToT AToB sigma fixedValue incidentFixed
      displayedIncident S hseq t ht
  by_cases htA : t.val < A.length
  · have he := AToB.2.2 ⟨t.val, htA⟩
    have hi : Fin.castLE AToB.1 ⟨t.val, htA⟩ = t := Fin.ext rfl
    rw [hi] at he
    rw [he]
    exact incidentFixed _ (displayedIncident A (segRefl A) _)
  · have hstep := (TashkinovAugmentationSequencePosition phi S B hseq t ht).1
    obtain ⟨hl, hinit, c, hcol, hm⟩ := hstep
    have hcolB : phi (B.edge t) = some c := by
      convert hcol using 1
      congr 2
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨iv, hiv⟩ := hv
    let ivT : Fin (T.length + 1) := ⟨iv.val, by
      have htB := BToT.1
      have := iv.isLt
      simp only [TreeSequencePrefix] at this
      omega⟩
    have hcvT : c ∈ MissingColors G phi (T.vertex ivT) := by
      have he : (TreeSequencePrefix B t.val (le_trans S.positive ht)
          (Nat.le_of_lt t.isLt)).vertex iv = T.vertex ivT := rfl
      rw [← he, hiv]
      exact hcv
    have hnotA : c ≠ alpha := by
      intro he
      subst c
      apply horder.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.castLE BToT.1 t,
        by change A.length ≤ t.val; omega, t.isLt,
        by rw [BToT.2.2 t]; exact hcolB⟩
    have hnotB : c ≠ beta := by
      intro he
      subst c
      have hivB : ivT.val < ib.val := by
        have := iv.isLt
        simp only [TreeSequencePrefix] at this
        have htB : t.val < ib.val := t.isLt
        dsimp [ivT]
        omega
      have hvY := vertexY ivT (by omega)
      have hneV : T.vertex ivT ≠ vb := by
        intro he
        have hi := congrArg Fin.val (T.vertex_injective he)
        omega
      exact Finset.disjoint_left.mp (hElementaryY hvY hbY hneV) hcvT hb.1
    exact fixedValue _ (fun hc => hnotA (Option.some.inj (hcolB.symm.trans hc)))
      (fun hc => hnotB (Option.some.inj (hcolB.symm.trans hc)))

private theorem helper_seedFixed_790.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
    ∀ (f : E) (seed : TreeSequence G e0),
    TreeSequenceAdjoinEdge Tn f seed →
    sigma f = phi f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb TnToA sigma
      incidentFixed f seed hadjoin
  obtain ⟨i, hi⟩ := seed.attaches (Fin.cast hadjoin.1.symm (Fin.last Tn.length))
  let j : Fin (Tn.length + 1) := ⟨i.val, by have := i.isLt; simpa using this⟩
  have hv : seed.vertex (Fin.castLT i
      (Nat.lt_trans i.isLt (Nat.succ_lt_succ
        (Fin.cast hadjoin.1.symm (Fin.last Tn.length)).isLt))) = Tn.vertex j :=
    hadjoin.2.1.2.1 j
  apply incidentFixed
  refine ⟨Tn.vertex j, TreeSequenceInitialSegmentVertexSetSubset TnToA
    (by simp [TreeSequenceVertexSet]), ?_⟩
  rw [← hadjoin.2.2, Incident, hi]
  simp [← hv]

private theorem helper_edgesFixed_804.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
    TreeSequenceInitialSegment Tn B →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed B) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A →
          ∀ (t : Fin S.length), TreeIncidentEdge A (S.edge t)) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B →
          ∀ (t : Fin B.length), S.length ≤ (↑t : ℕ) → sigma (B.edge t) = phi (B.edge t)) →
    (∀ (f : E) (seed : TreeSequence G e0),
        TreeSequenceAdjoinEdge Tn f seed → sigma f = phi f) →
    ∀ (t : Fin B.length),
    sigma (B.edge t) = phi (B.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb TnToA hAib B sigma
      incidentFixed TnToB terminalRoute displayedIncident augmentationFixed seedFixed t
  by_cases ht : t.val < Tn.length
  · have he := TnToB.2.2 ⟨t.val, ht⟩
    have hi : Fin.castLE TnToB.1 ⟨t.val, ht⟩ = t := Fin.ext rfl
    rw [hi] at he
    rw [he]
    exact incidentFixed _ (displayedIncident Tn TnToA _)
  · rcases terminalRoute with ⟨hp, hs⟩ | ⟨hk, f, seed, hedges, hadjoin, hs⟩
    · exact augmentationFixed Tn hs t (by omega)
    · by_cases he : t.val = Tn.length
      · have hSB := TashkinovAugmentationSequenceInitialSegment phi seed B hs
        have hi := hSB.2.2 (Fin.cast hadjoin.1.symm (Fin.last Tn.length))
        have hj : Fin.castLE hSB.1 (Fin.cast hadjoin.1.symm (Fin.last Tn.length)) = t :=
          Fin.ext (by simpa using he.symm)
        rw [hj, hadjoin.2.2] at hi
        simpa [hi] using seedFixed f seed hadjoin
      · exact augmentationFixed seed hs t (by have := hadjoin.1; omega)

private theorem helper_routeTransport_823.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet B,
        v ≠ vb → MissingColors G sigma v = MissingColors G phi v) →
    (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S B →
    TashkinovAugmentationSequence sigma S B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb segTrans hAib B BToT
      sigma missingBefore edgesFixed S hs
  unfold TashkinovAugmentationSequence at hs ⊢
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head U W hstep htail ih =>
    have hWB := TashkinovAugmentationSequenceInitialSegment phi W B htail
    obtain ⟨hlen, hUW, c, hcol, hm⟩ := hstep
    have hUB := segTrans hUW hWB
    have hlt : U.length < B.length := by have := hWB.1; omega
    refine Relation.ReflTransGen.head ⟨hlen, hUW, c, ?_, ?_⟩ ih
    · have hf := edgesFixed (Fin.castLE hWB.1 (Fin.cast hlen.symm (Fin.last U.length)))
      rw [hWB.2.2] at hf
      exact hf.trans hcol
    · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      have hvB := TreeSequenceInitialSegmentVertexSetSubset hUB hv
      have hvb : v ≠ vb := by
        intro he
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
        obtain ⟨i, hi⟩ := hv
        have ht := hUB.2.1 i
        have htT := BToT.2.1 (Fin.castLE (Nat.succ_le_succ hUB.1) i)
        have eqv : T.vertex (Fin.castLE (Nat.succ_le_succ BToT.1)
            (Fin.castLE (Nat.succ_le_succ hUB.1) i)) = T.vertex ib := htT.trans (ht.trans
                (hi.trans he))
        have hh := congrArg Fin.val (T.vertex_injective eqv)
        have := i.isLt
        change i.val = ib.val at hh
        change U.length < ib.val at hlt
        omega
      exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [missingBefore v hvB hvb]; exact hcv⟩

private theorem helper_replacement_855.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment base.core A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    MaximumProperty
        { rounds := ett.1, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB,
          belowFinal := belowB, generatingColoring := genB :
          ExtendedTashkinovTree G k e0 input B phi } →
    ∀
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    baseB.core = base.core →
    ∀
      (HB :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          ∀ (D : Finset (Fin k)), StableColoring S D phi sigma) →
    StableColoring Tn Dn phi sigma →
    TreeSequenceInitialSegment Tn B →
    Tn.length < B.length →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed B) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B → TashkinovAugmentationSequence sigma S B) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    MaximumProperty corr.replacementETT ∧
      ∃ (baseS : HierarchyBase corr.replacementETT sigma) (HS :
        TashkinovHierarchy corr.replacementETT baseS), SameHierarchyStages HB HS := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn Dn ib
      vb coreToA hAib B rpB aboveB strictB belowB genB hMPB baseB hcoreB HB ettB sigma
      sigmaProper sigmaOne stable stableTn TnToB TnStrictB terminalRoute routeTransport
  by_cases hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · have closureSubset : TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
      obtain ⟨_, _, ⟨u⟩⟩ := baseB.parallel hPE
      intro v hv
      apply TreeSequenceInitialSegmentVertexSetSubset coreToA
      rw [← hcoreB, u.vertexSet]
      exact Finset.mem_union_right _ hv
    have hcombined : CombinedStableColoring Tn baseB.closure Dn phi sigma :=
      ⟨stableTn, stable baseB.closure closureSubset ∅⟩
    have hseq : TashkinovAugmentationSequence sigma Tn B := by
      rcases terminalRoute with ⟨_, hs⟩ | ⟨hk, _⟩
      · exact routeTransport Tn hs
      · rcases hk with hk | hk <;> rw [hPE] at hk <;> cases hk
    exact HierarchySplitter G k e0 input B phi sigma ettB hMPB C.positive
      hlower baseB HB hPE hproper hone sigmaProper sigmaOne hcombined hseq
  · have hmod : ModColoring ettB sigma :=
      Td G k e0 input B phi ettB hMPB C.positive hlower sigma sigmaProper sigmaOne
        (by simpa only [ettB, ← ett.generatingColoring, n, Tn, Dn] using stableTn)
    have hroute :
        ((ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn B) ∨
        ((ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.SE ∨
          ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ettB.series.data.connectingEdges (Fin.last ettB.rounds) = {f} ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed B)) := by
      rcases terminalRoute with ⟨hp, _⟩ | ⟨hk, f, seed, hedges, hadjoin, hs⟩
      · exact (hPE hp).elim
      · exact Or.inr ⟨hk, f, seed, hedges, hadjoin, routeTransport seed hs⟩
    obtain ⟨corr⟩ := hmod.2.2 B TnToB TnStrictB hroute
    have hMP := MaximumPropertyTransport G k e0 ettB sigma hmod B corr hMPB
    refine ⟨corr, hMP, ?_⟩
    rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
      hedges, hkinds, hproperSeries, honeSeries, hstableSeries⟩
    rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
    cases hr
    have heq : series = newSeries := eq_of_heq hs
    cases heq
    let rep : ExtendedTashkinovTree G k e0 newInput B sigma :=
      ⟨ett.rounds, rp, newSeries, above, strict, below, gen⟩
    let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
    have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
    have htree : newSeries.data.tree n.castSucc = Tn := by simpa [hj, ettB, Tn] using htrees j
    have hkind := hkinds n
    let pos : Fin ((newSeries.data.tree n.castSucc).length + 1) :=
      Fin.cast (congrArg (fun S : TreeSequence G e0 => S.length + 1) htree.symm)
        baseB.supportPosition
    let baseS : HierarchyBase rep sigma :=
      { core := baseB.core
        closure := baseB.closure
        supportPosition := pos
        supportPositive := by simpa [pos] using baseB.supportPositive
        terminalMissingColors := rfl
        parallel := by
          dsimp only [rep]
          intro hp
          exact (hPE (hkind.symm.trans hp)).elim
        nonparallel := by
          dsimp only [rep]
          intro hp
          exact (baseB.nonparallel hPE).trans htree.symm }
    let HS : TashkinovHierarchy rep baseS :=
      { dividerCount := HB.dividerCount
        stage := HB.stage
        baseStage := HB.baseStage.trans htree.symm
        terminalStage := HB.terminalStage
        nested := HB.nested
        strict := HB.strict
        dividerPosition := HB.dividerPosition
        dividerPositive := HB.dividerPositive
        dividerIncreasing := HB.dividerIncreasing
        dividerStage := HB.dividerStage
        coreInsideFirst := HB.coreInsideFirst }
    refine ⟨baseS, HS, ?_⟩
    refine ⟨rfl, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
    · exact ⟨fun hp => (hPE hp).elim, fun hp => (hPE (hkind.symm.trans hp)).elim⟩
    · intro hp; exact (hPE hp).elim

private theorem helper_storedS_942.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds) =
      Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn Dn ib vb TnToA hAib B rpB
      aboveB strictB belowB genB ettB sigma treeMissingEq corr
  rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
    hedges, hkinds, hproperSeries, honeSeries, hstableSeries⟩
  rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
  cases hr
  have heq : series = newSeries := eq_of_heq hs
  cases heq
  let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
  have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
  have htree : newSeries.data.tree n.castSucc = Tn := by simpa [hj, ettB, Tn] using htrees j
  have hm := treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA)
  unfold Dn TashkinovStoredColors
  simp only [ettB, hstored, ← hgen, ← ett.generatingColoring, htree, hm, n, Tn]

private theorem helper_stageBToB_968.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (HB :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB)
      (j : Fin (HB.dividerCount + (2 : ℕ))),
    TreeSequenceInitialSegment (HB.stage j) B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib segRefl segTrans hAib B rpB
      aboveB strictB belowB genB baseB HB j
  clear * - HB j B segRefl segTrans
  exact Fin.reverseInduction
    (motive := fun j => TreeSequenceInitialSegment (HB.stage j) B)
    (by simpa only [HB.terminalStage] using segRefl B)
    (fun i hi => segTrans (HB.nested i) hi) j

private theorem helper_closureBToA_975.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    TreeSequenceInitialSegment base.core A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    baseB.core = base.core →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n ib coreToA hAib B rpB aboveB
      strictB belowB genB baseB hcoreB hp
  clear * - hp baseB coreToA hcoreB
  obtain ⟨_, _, ⟨u⟩⟩ := baseB.parallel hp
  intro v hv
  apply TreeSequenceInitialSegmentVertexSetSubset coreToA
  rw [← hcoreB, u.vertexSet]
  exact Finset.mem_union_right _ hv

private theorem helper_minusEq_983.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    (∀ (f : E), TreeIncidentEdge A f → sigma f = phi f) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
    ∀ (D : Finset (Fin k)),
    TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb sigma treeMissingEq
      incidentFixed S hS D
  unfold TreeColorSetMinusClosed TreeColorSetClosed
  rw [treeMissingEq S hS]
  have boundaryEq (c : Fin k) (hc : c ∈ TreeMissingColors phi S) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet S) c =
        BoundaryColorEdges G phi (TreeSequenceVertexSet S) c := by
    ext f
    simp only [BoundaryColorEdges, Finset.mem_filter]
    apply and_congr_right
    intro hf
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨u, hu, v, hv, he⟩ := hf
    have hfix : sigma f = phi f := incidentFixed f ⟨u, hS hu, by simp [Incident, he]⟩
    rw [hfix]
  exact ⟨fun hs c hc => (boundaryEq c (Finset.mem_sdiff.mp hc).1).symm.trans (hs c hc),
    fun hs c hc => (boundaryEq c (Finset.mem_sdiff.mp hc).1).trans (hs c hc)⟩

private theorem helper_storedEq_1020.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma),
    TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) =
        Dn →
    ∀ (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          (HierarchyStarredStage
            { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }
            j)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Dn ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma treeMissingEq corr baseS storedS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore starBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS starEq j
  change TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) \ TreeMissingColors sigma (HierarchyStarredStage HS
          j) =
    Dn \ TreeMissingColors phi (HierarchyStarredStage HB j)
  rw [storedS, starEq, treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (starBToA j))]

private theorem helper_missingEq_1027.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb TnToA hAib B rpB
      aboveB strictB belowB genB baseB ettB sigma treeMissingEq corr baseS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS j
  refine Fin.cases ?_ (fun i => ?_) j
  · change TreeMissingColors sigma (corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
    have htree : corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc = Tn :=
      hsbase.symm.trans hbbase
    rw [htree, treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset TnToA)]
  · exact treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ))

private theorem helper_firstLe_1038.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (psi : PartialEdgeColoring E k) (eta : Fin k) (i : Fin (B.length + (1 : ℕ))),
    eta ∈ MissingColors G psi (B.vertex i) →
    (↑(HierarchyFirstMissingPosition psi B eta) : ℕ) ≤ (↑i : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib hAib B psi eta i hc
  clear * - psi eta i hc
  let candidates := Finset.univ.filter fun j => eta ∈ MissingColors G psi (B.vertex j)
  have hi : i ∈ candidates := by simp [candidates, hc]
  have hn : candidates.Nonempty := ⟨i, hi⟩
  simpa [HierarchyFirstMissingPosition, candidates, hn] using
    (show (candidates.min' hn).val ≤ i.val from Finset.min'_le candidates i hi)

private theorem helper_firstStrict_1047.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (psi : PartialEdgeColoring E k) (eta : Fin k),
    (↑(HierarchyFirstMissingPosition psi B eta) : ℕ) < B.length →
    eta ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B eta)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib hAib B psi eta h
  clear * - psi eta h
  unfold HierarchyFirstMissingPosition at h ⊢
  dsimp only at h ⊢
  split_ifs with hn
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hn)).2
  · simp only [dite_eq_right hn, Fin.val_last] at h
    omega

private theorem helper_firstEq_1057.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet B,
        v ≠ vb → MissingColors G sigma v = MissingColors G phi v) →
    (∀ (psi : PartialEdgeColoring E k) (eta : Fin k) (i : Fin (B.length + (1 : ℕ))),
        eta ∈ MissingColors G psi (B.vertex i) →
          (↑(HierarchyFirstMissingPosition psi B eta) : ℕ) ≤ (↑i : ℕ)) →
    (∀ (psi : PartialEdgeColoring E k) (eta : Fin k),
        (↑(HierarchyFirstMissingPosition psi B eta) : ℕ) < B.length →
          eta ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B eta))) →
    ∀ (eta : Fin k),
    HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B BToT sigma
      missingBefore firstLe firstStrict eta
  have beforeLast (i : Fin (B.length + 1)) (hi : i.val < B.length) :
      MissingColors G sigma (B.vertex i) = MissingColors G phi (B.vertex i) := by
    apply missingBefore
    · simp [TreeSequenceVertexSet]
    · intro he
      have heT := (BToT.2.1 i).trans he
      have heval := congrArg Fin.val (T.vertex_injective heT)
      have hbLen : B.length = ib.val := rfl
      change i.val = ib.val at heval
      omega
  apply Fin.ext
  apply Nat.le_antisymm
  · by_cases h : (HierarchyFirstMissingPosition phi B eta).val < B.length
    · apply firstLe sigma eta
      rw [beforeLast _ h]
      exact firstStrict phi eta h
    · have := (HierarchyFirstMissingPosition sigma B eta).isLt
      omega
  · by_cases h : (HierarchyFirstMissingPosition sigma B eta).val < B.length
    · apply firstLe phi eta
      rw [← beforeLast _ h]
      exact firstStrict sigma eta h
    · have := (HierarchyFirstMissingPosition phi B eta).isLt
      omega

private theorem helper_segmentEq_1084.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (2 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j)
          B) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    (∀ (eta : Fin k),
        HierarchyFirstMissingPosition sigma B eta =
          HierarchyFirstMissingPosition phi B eta) →
    ∀ (j : Fin (count + (1 : ℕ))) (eta : Fin k),
    HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma edgesFixed corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
      firstEq j eta
  have hedge (t : Fin (stages j.succ).length) :
      sigma ((stages j.succ).edge t) = phi ((stages j.succ).edge t) := by
    have hSB := stageBToB j.succ
    have hf := edgesFixed (Fin.castLE hSB.1 t)
    rw [hSB.2.2] at hf
    exact hf
  unfold HierarchySegmentColors
  simp only [starEq, firstEq eta, HS, HB, hedge]

private theorem helper_refreshEq_1096.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (i : Fin count),
    ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G sigma v) =
      (TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma missingA corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq i
  rw [starEq]
  apply Finset.biUnion_congr rfl
  intro v hv
  exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ)
    (Finset.mem_sdiff.mp hv).1)

private theorem helper_hstarLast_1150.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let _ : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
      (hcountB :
        { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }.dividerCount =
          H.dividerCount),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        have jo : Fin (H.dividerCount + (1 : ℕ)) := Fin.cast (by omega) j;
        { dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.stage
              j.castSucc =
            H.stage jo.castSucc ∧
          HierarchyStarredStage
              { dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }
              j =
            HierarchyStarredStage H jo) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    HierarchyStarredStage HS (Fin.last count) = A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma corr baseS count stages hbbase hbterminal hbnested
      hbstrict positions hbpositive hbincreasing hbdivider hbcore hcountB hstagesB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
  rw [starEq]
  have hs := (hstagesB (Fin.last count)).2
  have hj : Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB) (Fin.last count) = q :=
    Fin.ext (by simp [q])
  simpa only [hj] using hs

private theorem helper_pathLe_1162.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let _ : ℕ := T.length - A.length;
    TreeSequenceInitialSegment A T →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    A.length < B.length →
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    HierarchyStarredStage HS (Fin.last count) = A →
    HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb ell AToT hAib B BToT
      ABstrict rpB aboveB strictB belowB genB ettB sigma corr baseS count stages positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HS hstarLast
  let tailB := B.length - A.length
  let candidatesT := (Finset.Icc 1 ell).filter fun i =>
    ∀ t : Fin T.length, A.length + i ≤ t.val →
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
  let candidatesB := (Finset.Icc 1 tailB).filter fun i =>
    ∀ t : Fin B.length, A.length + i ≤ t.val →
      G.ends (B.edge t) = s(B.vertex t.castSucc, B.vertex t.succ)
  have htail : 1 ≤ tailB := by dsimp [tailB]; omega
  have htailT : 1 ≤ ell := by dsimp [ell]; omega
  have htmem : ell ∈ candidatesT := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htailT, le_rfl⟩, ?_⟩
    intro t ht
    have hAT := AToT.1
    have := t.isLt
    dsimp [ell] at ht
    omega
  have hbmem : tailB ∈ candidatesB := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htail, le_rfl⟩, ?_⟩
    intro t ht
    have := t.isLt
    dsimp [tailB] at ht
    omega
  have hnT : candidatesT.Nonempty := ⟨ell, htmem⟩
  have hnB : candidatesB.Nonempty := ⟨tailB, hbmem⟩
  have hmT := Finset.min'_mem candidatesT hnT
  have hbounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hmT).1
  have hminB : candidatesB.min' hnB ≤ candidatesT.min' hnT := by
    by_cases ht : candidatesT.min' hnT ≤ tailB
    · apply Finset.min'_le
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbounds.1, ht⟩, ?_⟩
      intro t hpos
      have he := (Finset.mem_filter.mp hmT).2 (Fin.castLE BToT.1 t) hpos
      have hv0 := BToT.2.1 t.castSucc
      have hv1 := BToT.2.1 t.succ
      have hi0 : (Fin.castLE BToT.1 t).castSucc =
          Fin.castLE (Nat.succ_le_succ BToT.1) t.castSucc := Fin.ext rfl
      have hi1 : (Fin.castLE BToT.1 t).succ =
          Fin.castLE (Nat.succ_le_succ BToT.1) t.succ := Fin.ext rfl
      simpa only [BToT.2.2, hi0, hi1, hv0, hv1] using he
    · exact le_trans (Finset.min'_le candidatesB tailB hbmem) (by omega)
  unfold HierarchyPathNumber
  rw [hstarLast]
  change (if h : candidatesB.Nonempty then candidatesB.min' h else tailB) ≤
    (if h : candidatesT.Nonempty then candidatesT.min' h else ell)
  rw [dite_eq_left hnB, dite_eq_left hnT]
  exact hminB

private theorem helper_hinter_3043.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (other : ExtendedTashkinovTree G k e0 input' T' generating'),
        other.rounds = ett.rounds →
          MaximumProperty other →
            ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
              (_ : GoodHierarchy K),
              K.dividerCount < C.hierarchy.dividerCount →
                ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
    (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card) →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    alpha ∈ TreeMissingColors phi A →
    TreeColorSetClosed G phi A ({ alpha } : Finset (Fin k)) →
    TreeInterchangeable G A phi alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hlarge alpha beta
      hne H q A n Tn Dn lastZero lastPositive halphaA halphaClosed
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact @helper_branch_392 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
        (@hone) (@hlower) (@alpha) (@beta) (@lastZero) (@halphaA) (@halphaClosed) (@hz) (@hp)
    · exact @helper_branch_399 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
        (@hone) (@hlower) (@alpha) (@beta) (@lastZero) (@halphaA) (@hz) (@hp)
  · exact @helper_branch_481 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone) (@hlower)
      (@hfewer) (@hlarge) (@alpha) (@beta) (@hne) (@lastPositive) (@halphaA) (@halphaClosed) (@hz)

private theorem helper_replacement_3186.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment base.core A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    MaximumProperty
        { rounds := ett.1, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB,
          belowFinal := belowB, generatingColoring := genB :
          ExtendedTashkinovTree G k e0 input B phi } →
    ∀
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    baseB.core = base.core →
    ∀
      (HB :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          ∀ (D : Finset (Fin k)), StableColoring S D phi sigma) →
    StableColoring Tn Dn phi sigma →
    TreeSequenceInitialSegment Tn B →
    Tn.length < B.length →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed B) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B → TashkinovAugmentationSequence sigma S B) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    MaximumProperty corr.replacementETT ∧
      ∃ (baseS : HierarchyBase corr.replacementETT sigma) (HS :
        TashkinovHierarchy corr.replacementETT baseS), SameHierarchyStages HB HS := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn Dn ib
      vb coreToA hAib B rpB aboveB strictB belowB genB hMPB baseB hcoreB HB ettB sigma
      sigmaProper sigmaOne stable stableTn TnToB TnStrictB terminalRoute routeTransport
  exact @helper_replacement_855 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@alpha) (@beta) (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB)
      (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@sigmaProper) (@sigmaOne) (@stable) (@stableTn)
      (@TnToB) (@TnStrictB) (@terminalRoute) (@routeTransport)

private theorem helper_storedEq_3248.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma),
    TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) =
        Dn →
    ∀ (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          (HierarchyStarredStage
            { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }
            j)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Dn ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma treeMissingEq corr baseS storedS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore starBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS starEq j
  exact @helper_storedEq_1020 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hAib) (@rpB)
      (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@treeMissingEq) (@corr) (@baseS)
      (@storedS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@starBToA)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@starEq) (@j)

private theorem helper_missingEq_3257.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb TnToA hAib B rpB
      aboveB strictB belowB genB baseB ettB sigma treeMissingEq corr baseS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS j
  exact @helper_missingEq_1027 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@TnToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@treeMissingEq)
      (@corr) (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToA)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@j)

private theorem helper_segmentEq_3284.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (2 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j)
          B) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    (∀ (eta : Fin k),
        HierarchyFirstMissingPosition sigma B eta =
          HierarchyFirstMissingPosition phi B eta) →
    ∀ (j : Fin (count + (1 : ℕ))) (eta : Fin k),
    HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma edgesFixed corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
      firstEq j eta
  exact @helper_segmentEq_1084 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@edgesFixed) (@corr)
      (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions)
      (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToB) (@positionsS)
      (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
      (@hsdivider) (@hscore) (@starEq) (@firstEq) (@j) (@eta)

private theorem helper_refreshEq_3294.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (i : Fin count),
    ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G sigma v) =
      (TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma missingA corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq i
  exact @helper_refreshEq_1096 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@missingA) (@corr)
      (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions)
      (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToA) (@positionsS)
      (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
      (@hsdivider) (@hscore) (@starEq) (@i)

private theorem helper_hstarLast_3349.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
      (hcountB :
        { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }.dividerCount =
          H.dividerCount),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        have jo : Fin (H.dividerCount + (1 : ℕ)) := Fin.cast (by omega) j;
        { dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.stage
              j.castSucc =
            H.stage jo.castSucc ∧
          HierarchyStarredStage
              { dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }
              j =
            HierarchyStarredStage H jo) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    HierarchyStarredStage HS (Fin.last count) = A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma corr baseS count stages hbbase hbterminal hbnested
      hbstrict positions hbpositive hbincreasing hbdivider hbcore hcountB hstagesB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
  exact @helper_hstarLast_1150 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@corr) (@baseS) (@count)
      (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions) (@hbpositive)
      (@hbincreasing) (@hbdivider) (@hbcore) (@hcountB) (@hstagesB) (@positionsS) (@hspositive)
      (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict) (@hsdivider) (@hscore)
      (@starEq)

private theorem helper_pathLe_3363.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment A T →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    A.length < B.length →
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    HierarchyStarredStage HS (Fin.last count) = A →
    HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb AToT hAib B BToT
      ABstrict rpB aboveB strictB belowB genB ettB sigma corr baseS count stages positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HS hstarLast
  exact @helper_pathLe_1162 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@AToT) (@hAib)
      (@BToT) (@ABstrict) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@corr) (@baseS)
      (@count) (@stages) (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal)
      (@hsnested) (@hsstrict) (@hsdivider) (@hscore) (@hstarLast)

private theorem helper_replacement_4227.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment base.core A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    MaximumProperty
        { rounds := ett.1, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB,
          belowFinal := belowB, generatingColoring := genB :
          ExtendedTashkinovTree G k e0 input B phi } →
    ∀
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    baseB.core = base.core →
    ∀
      (HB :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          ∀ (D : Finset (Fin k)), StableColoring S D phi sigma) →
    StableColoring Tn Dn phi sigma →
    TreeSequenceInitialSegment Tn B →
    Tn.length < B.length →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed B) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B → TashkinovAugmentationSequence sigma S B) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    MaximumProperty corr.replacementETT ∧
      ∃ (baseS : HierarchyBase corr.replacementETT sigma) (HS :
        TashkinovHierarchy corr.replacementETT baseS), SameHierarchyStages HB HS := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn Dn ib
      vb coreToA hAib B rpB aboveB strictB belowB genB hMPB baseB hcoreB HB ettB sigma
      sigmaProper sigmaOne stable stableTn TnToB TnStrictB terminalRoute routeTransport
  exact @helper_replacement_3186 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@alpha) (@beta) (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB)
      (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@sigmaProper) (@sigmaOne) (@stable) (@stableTn)
      (@TnToB) (@TnStrictB) (@terminalRoute) (@routeTransport)

private theorem helper_storedEq_4289.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma),
    TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) =
        Dn →
    ∀ (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          (HierarchyStarredStage
            { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }
            j)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Dn ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma treeMissingEq corr baseS storedS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore starBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS starEq j
  exact @helper_storedEq_3248 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hAib) (@rpB)
      (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@treeMissingEq) (@corr) (@baseS)
      (@storedS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@starBToA)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@starEq) (@j)

private theorem helper_missingEq_4298.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb TnToA hAib B rpB
      aboveB strictB belowB genB baseB ettB sigma treeMissingEq corr baseS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS j
  exact @helper_missingEq_3257 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@TnToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@treeMissingEq)
      (@corr) (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToA)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@j)

private theorem helper_segmentEq_4325.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (2 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j)
          B) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    (∀ (eta : Fin k),
        HierarchyFirstMissingPosition sigma B eta =
          HierarchyFirstMissingPosition phi B eta) →
    ∀ (j : Fin (count + (1 : ℕ))) (eta : Fin k),
    HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma edgesFixed corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
      firstEq j eta
  exact @helper_segmentEq_3284 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@edgesFixed) (@corr)
      (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions)
      (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToB) (@positionsS)
      (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
      (@hsdivider) (@hscore) (@starEq) (@firstEq) (@j) (@eta)

private theorem helper_refreshEq_4335.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
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
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (i : Fin count),
    ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G sigma v) =
      (TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma missingA corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq i
  exact @helper_refreshEq_3294 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@missingA) (@corr)
      (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions)
      (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToA) (@positionsS)
      (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
      (@hsdivider) (@hscore) (@starEq) (@i)

private theorem helper_hstarLast_4390.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
      (hcountB :
        { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }.dividerCount =
          H.dividerCount),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        have jo : Fin (H.dividerCount + (1 : ℕ)) := Fin.cast (by omega) j;
        { dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.stage
              j.castSucc =
            H.stage jo.castSucc ∧
          HierarchyStarredStage
              { dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }
              j =
            HierarchyStarredStage H jo) →
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    HierarchyStarredStage HS (Fin.last count) = A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma corr baseS count stages hbbase hbterminal hbnested
      hbstrict positions hbpositive hbincreasing hbdivider hbcore hcountB hstagesB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
  exact @helper_hstarLast_3349 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@corr) (@baseS) (@count)
      (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions) (@hbpositive)
      (@hbincreasing) (@hbdivider) (@hbcore) (@hcountB) (@hstagesB) (@positionsS) (@hspositive)
      (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict) (@hsdivider) (@hscore)
      (@starEq)

private theorem helper_pathLe_4404.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment A T →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    A.length < B.length →
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
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
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    HierarchyStarredStage HS (Fin.last count) = A →
    HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb AToT hAib B BToT
      ABstrict rpB aboveB strictB belowB genB ettB sigma corr baseS count stages positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HS hstarLast
  exact @helper_pathLe_3363 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@AToT) (@hAib)
      (@BToT) (@ABstrict) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@corr) (@baseS)
      (@count) (@stages) (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal)
      (@hsnested) (@hsstrict) (@hsdivider) (@hscore) (@hstarLast)

private theorem helper_continuation_5185.{u_1, u_2} :
    helperContinuation5185Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hminimal alpha beta hne H q A n Tn Dn ib vb
      coreToA TnToA AToT ordinaryToA hAib B BToT ABstrict BstrictT rpB aboveB strictB belowB genB
      baseB hcoreB HB hcountB hstagesB hdividersB goodB hgoodB ettB sigma missingBefore
      sigmaNotElementary missingA treeMissingEq incidentFixed edgesFixed corr hMPS baseS HS hsame
      storedS hrS stageBToA starBToA stageBToB
  have closureBToA (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
    exact @helper_closureBToA_975 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@hcoreB) (@hp)
  have minusEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) (D : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D := by
    exact @helper_minusEq_983 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@treeMissingEq) (@incidentFixed) (@S) (@hS) (@D)
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
    exact @helper_storedEq_4289 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hAib) (@rpB)
        (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@treeMissingEq) (@corr) (@baseS)
        (@storedS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
        (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@starBToA)
        (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
        (@hsstrict) (@hsdivider) (@hscore) (@starEq) (@j)
  have missingEq (j : Fin (count + 1)) :
      HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
    exact @helper_missingEq_4298 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@TnToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@treeMissingEq)
        (@corr) (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
        (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToA)
        (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
        (@hsstrict) (@hsdivider) (@hscore) (@j)
  -- A change only at the last vertex leaves the totalized first position unchanged.
  have firstLe (psi : PartialEdgeColoring E k) (eta : Fin k)
      (i : Fin (B.length + 1)) (hc : eta ∈ MissingColors G psi (B.vertex i)) :
      (HierarchyFirstMissingPosition psi B eta).val ≤ i.val := by
    exact @helper_firstLe_1038 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hAib) (@psi)
        (@eta) (@i) (@hc)
  have firstStrict (psi : PartialEdgeColoring E k) (eta : Fin k)
      (h : (HierarchyFirstMissingPosition psi B eta).val < B.length) :
      eta ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B eta)) := by
    exact @helper_firstStrict_1047 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@psi) (@eta) (@h)
  have firstEq (eta : Fin k) :
      HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta := by
    exact @helper_firstEq_1057 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hAib) (@BToT)
        (@missingBefore) (@firstLe) (@firstStrict) (@eta)
  have segmentEq (j : Fin (count + 1)) (eta : Fin k)
      (he : eta ∈ HierarchyStoredColorsAt HB j) :
      HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
    exact @helper_segmentEq_4325 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@edgesFixed) (@corr)
        (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions)
        (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToB) (@positionsS)
        (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
        (@hsdivider) (@hscore) (@starEq) (@firstEq) (@j) (@eta)
  have refreshEq (i : Fin count) :
      ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
          fun v => MissingColors G sigma v) =
      ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
          fun v => MissingColors G phi v) := by
    exact @helper_refreshEq_4335 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@missingA) (@corr)
        (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions)
        (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToA) (@positionsS)
        (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
        (@hsdivider) (@hscore) (@starEq) (@i)
  let goodS : GoodHierarchy HS :=
    { gamma := goodB.gamma
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
  let CS : HierarchyCounterexample baseS :=
    { positive := by rw [hrS]; exact C.positive
      hierarchy := HS
      good := goodS
      maximum := hMPS
      notElementary := sigmaNotElementary }
  have hstarLast : HierarchyStarredStage HS (Fin.last count) = A := by
    exact @helper_hstarLast_4390 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@corr) (@baseS) (@count)
        (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions) (@hbpositive)
        (@hbincreasing) (@hbdivider) (@hbcore) (@hcountB) (@hstagesB) (@positionsS) (@hspositive)
        (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict) (@hsdivider) (@hscore)
        (@starEq)
  have hlastOrd : HS.stage (Fin.last count).castSucc = H.stage q.castSucc := by
    have hs := (hstagesB (Fin.last count)).1
    have hj : Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB) (Fin.last count) = q :=
      Fin.ext (by simp [q])
    simpa only [hj] using hs
  -- Path candidates restrict to the shorter prefix; the second measure decreases strictly.
  have pathLe : HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
    exact @helper_pathLe_4404 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@AToT) (@hAib)
        (@BToT) (@ABstrict) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@corr) (@baseS)
        (@count) (@stages) (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal)
        (@hsnested) (@hsstrict) (@hsdivider) (@hscore) (@hstarLast)
  have tailLess : B.length - (HS.stage (Fin.last count).castSucc).length <
      T.length - (H.stage q.castSucc).length := by
    clear * - hlastOrd ordinaryToA BstrictT ABstrict AToT
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

private theorem helper_continuation_5094.{u_1, u_2} :
    helperContinuation5094Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hminimal alpha beta hne H q
      A n Tn Dn ia ib va vb ell yLength Y segRefl segTrans commonPrefix coreToA TnToA AToT
      ordinaryToA starredToA hElementaryY ha hb vertexY hbY hout hAib horder havb B BToT AToB
      ABstrict BstrictT rpB aboveB strictB belowB genB hMPB baseB hcoreB HB hcountB hstagesB
      hdividersB goodB hgoodB ettB K sigma avoidA behavior fixedValue sigmaProper sigmaOne haB
      hbB missingBefore hnewa
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
    clear * - hS missingA
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv => missingA v (hS hv))
  have incidentFixed (f : E) (hf : TreeIncidentEdge A f) : sigma f = phi f := by
    exact @helper_incidentFixed_651 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@ha) (@hb) (@avoidA) (@fixedValue) (@f) (@hf)
  have stable (S : TreeSequence G e0) (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A)
      (D : Finset (Fin k)) : StableColoring S D phi sigma := by
    exact @helper_stable_667 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@missingA)
        (@incidentFixed) (@S) (@hS) (@D)
  have stableTn : StableColoring Tn Dn phi sigma :=
    stable Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA) Dn
  have TnToB := segTrans TnToA AToB
  have TnStrictB : Tn.length < B.length := lt_of_le_of_lt TnToA.1 ABstrict
  have BToFinal := segTrans BToT ett.belowFinal
  -- Nonparallel extensions retain the certified connecting edge and one-edge seed.
  have terminalRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn B) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence phi seed B) := by
    exact @helper_terminalRoute_680 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@commonPrefix) (@hAib) (@TnToB) (@TnStrictB) (@BToFinal)
  have displayedIncident (S : TreeSequence G e0)
      (hSA : TreeSequenceInitialSegment S A) (t : Fin S.length) :
      TreeIncidentEdge A (S.edge t) := by
    exact @helper_displayedIncident_729 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@S) (@hSA) (@t)
  have augmentationFixed (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S B) (t : Fin B.length)
      (ht : S.length ≤ t.val) : sigma (B.edge t) = phi (B.edge t) := by
    exact @helper_augmentationFixed_737 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@segRefl) (@hElementaryY) (@hb) (@vertexY) (@hbY) (@hAib) (@horder) (@BToT) (@AToB)
        (@fixedValue) (@incidentFixed) (@displayedIncident) (@S) (@hseq) (@t) (@ht)
  have seedFixed (f : E) (seed : TreeSequence G e0)
      (hadjoin : TreeSequenceAdjoinEdge Tn f seed) : sigma f = phi f := by
    exact @helper_seedFixed_790 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@TnToA)
        (@incidentFixed) (@f) (@seed) (@hadjoin)
  have edgesFixed (t : Fin B.length) : sigma (B.edge t) = phi (B.edge t) := by
    exact @helper_edgesFixed_804 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@TnToA) (@hAib) (@incidentFixed) (@TnToB) (@terminalRoute) (@displayedIncident)
        (@augmentationFixed) (@seedFixed) (@t)
  have routeTransport (S : TreeSequence G e0) (hs : TashkinovAugmentationSequence phi S B) :
      TashkinovAugmentationSequence sigma S B := by
    exact @helper_routeTransport_823 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@segTrans) (@hAib) (@BToT) (@missingBefore) (@edgesFixed) (@S) (@hs)
  have replacement :
      ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B,
        MaximumProperty corr.replacementETT ∧
        ∃ baseS : HierarchyBase corr.replacementETT sigma,
          ∃ HS : TashkinovHierarchy corr.replacementETT baseS,
            SameHierarchyStages HB HS := by
    exact @helper_replacement_4227 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
        (@hlower) (@alpha) (@beta) (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB)
        (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@sigmaProper) (@sigmaOne) (@stable) (@stableTn)
        (@TnToB) (@TnStrictB) (@terminalRoute) (@routeTransport)
  obtain ⟨corr, hMPS, baseS, HS, hsame⟩ := replacement
  have storedS : TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) = Dn := by
    exact @helper_storedS_942 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@TnToA)
        (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@treeMissingEq) (@corr)
  have hrS : corr.replacementETT.rounds = ett.rounds := corr.rungAgreement
  have stageBToA (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HB.stage j.castSucc) A := by
    clear * - hstagesB ordinaryToA j
    rw [(hstagesB j).1]
    exact ordinaryToA _
  have starBToA (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage HB j) A := by
    clear * - hstagesB starredToA j
    rw [(hstagesB j).2]
    exact starredToA _
  have stageBToB (j : Fin (HB.dividerCount + 2)) :
      TreeSequenceInitialSegment (HB.stage j) B := by
    exact @helper_stageBToB_968 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@segRefl)
        (@segTrans) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB) (@j)
  exact @helper_continuation_5185 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hminimal) (@alpha)
      (@beta) (@hne) (@coreToA) (@TnToA) (@AToT) (@ordinaryToA) (@hAib) (@BToT) (@ABstrict)
      (@BstrictT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@hcoreB) (@HB)
      (@hcountB) (@hstagesB) (@hdividersB) (@goodB) (@hgoodB) (@missingBefore)
      (@sigmaNotElementary) (@missingA) (@treeMissingEq) (@incidentFixed) (@edgesFixed) (@corr)
      (@hMPS) (@baseS) (@HS) (@hsame) (@storedS) (@hrS) (@stageBToA) (@starBToA) (@stageBToB)
private theorem helper_continuation_5074.{u_1, u_2} :
    helperContinuation5074Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      alpha beta hne horderedUnused hbranch H q A n Tn Dn ia ib va vb ell yLength Y segRefl
      segTrans commonPrefix lastZero lastPositive coreToA TnToA AToT ordinaryToA starredToA YToT
      hElementaryY ha hb vertexY haY hbY hout hAib missingNotA
  have halphaA : alpha ∈ TreeMissingColors phi A := hbranch.1
  have halphaClosed : TreeColorSetClosed G phi A {alpha} := hbranch.2
  have hbetaA : beta ∉ TreeMissingColors phi A := missingNotA beta ib hb.1 hbY hout.2
  have horder := horderedUnused (Or.inr hbetaA)
  have habIndex : ia.val < ib.val := by
    exact @helper_habIndex_350 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@horder)
  have havb : va ≠ vb := by
    clear * - habIndex
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
    exact @helper_BstrictT_369 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
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
  have hinter : TreeInterchangeable G A phi alpha beta := by
    exact @helper_hinter_3043 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone) (@hlower)
        (@hfewer) (@hlarge) (@alpha) (@beta) (@hne) (@lastZero) (@lastPositive) (@halphaA)
        (@halphaClosed)
  refine ⟨?_, hinter⟩
  by_contra hcomponents
  let K := TwoColorComponent G phi alpha beta (Sum.inl vb)
  let sigma := TwoColorComponentSwap G phi alpha beta (Sum.inl vb)
  have pathMissing (v : V) (c d : Fin k) (hcd : c ≠ d)
      (hc : c ∈ MissingColors G phi v) :
      TwoColorPathComponent G phi c d (Sum.inl v) := by
    exact @helper_pathMissing_495 (@V) (@E) inferInstance inferInstance (@G) (@k)
        (@phi) (@hproper) (@v) (@c) (@d) (@hcd) (@hc)
  have pathA : TwoColorPathComponent G phi alpha beta (Sum.inl va) :=
    pathMissing va alpha beta hne ha.1
  have pathB : TwoColorPathComponent G phi alpha beta (Sum.inl vb) := by
    exact @helper_pathB_520 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@alpha) (@beta)
        (@hne) (@hb)
  have avoidA (v : V) (hv : v ∈ TreeSequenceVertexSet A) : Sum.inl v ∉ K := by
    clear * - hcomponents hinter hout pathA pathB K hv
    intro hK
    exact hcomponents (hinter _ _ pathA pathB ⟨va, hout.1, rfl⟩ ⟨v, hv, hK⟩)
  have haK : Sum.inl va ∉ K := avoidA va hout.1
  have behavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper
    (Sum.inl vb)
  have edgeOfVertex {v : V} {f : E} (hv : Sum.inl v ∈ K)
      (hf : Incident G v f) (hc : phi f = some alpha ∨ phi f = some beta) :
      Sum.inr f ∈ K := by
    clear * - hv hf hc K
    have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr f) (Sum.inl v) :=
      ⟨hf, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      sigma f = some c ↔ phi f = some c := by
    exact @helper_unaffected_555 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@ha) (@hb) (@f) (@c) (@hca) (@hcb)
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    clear * - ha hb sigma
    simp [sigma, TwoColorComponentSwap, ha, hb]
  have sigmaProper : IsProperEdgeColoring G sigma :=
    TwoColorComponentSwapProper G phi alpha beta hne hproper _
  have sigmaOne : IsOneEdgeUncolored sigma e0 := by
    exact @helper_sigmaOne_572 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hone) (@alpha) (@beta) (@hne)
        (@ha) (@hb) (@unaffected)
  have vertexB (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
      T.vertex i ∈ TreeSequenceVertexSet B := by
    clear * - i hi B
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haB : va ∈ TreeSequenceVertexSet B := vertexB ia (le_of_lt habIndex)
  have hbB : vb ∈ TreeSequenceVertexSet B := vertexB ib le_rfl
  -- Elementarity fixes missing sets before the swapped endpoint, even inside its component.
  have missingBefore (v : V) (hv : v ∈ TreeSequenceVertexSet B) (hvb : v ≠ vb) :
      MissingColors G sigma v = MissingColors G phi v := by
    exact @helper_missingBefore_597 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@hElementaryY) (@ha) (@hb) (@haY) (@hbY) (@hAib) (@BToY) (@haK) (@behavior)
        (@edgeOfVertex) (@v) (@hv) (@hvb)
  have hnewa : alpha ∈ MissingColors G sigma va := by
    rw [behavior.1 va haK]
    exact ha.1
  exact @helper_continuation_5094 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@hminimal) (@alpha) (@beta) (@hne) (@segRefl) (@segTrans) (@commonPrefix)
      (@coreToA) (@TnToA) (@AToT) (@ordinaryToA) (@starredToA) (@hElementaryY) (@ha) (@hb)
      (@vertexY) (@hbY) (@hout) (@hAib) (@horder) (@havb) (@BToT) (@AToB) (@ABstrict) (@BstrictT)
      (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@hcountB)
      (@hstagesB) (@hdividersB) (@goodB) (@hgoodB) (@avoidA) (@behavior) (@fixedValue)
      (@sigmaProper) (@sigmaOne) (@haB) (@hbB) (@missingBefore) (@hnewa)
theorem ChangeLemmaMixedClosedFinal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hminimal : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      alpha ∈ TreeMissingColors phi Ty ∧
        beta ∈ TreeMissingColors phi Ty)
    (horderedUnused :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let ia := HierarchyFirstMissingPosition phi T alpha
      let ib := HierarchyFirstMissingPosition phi T beta
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T (T.vertex ia) (T.vertex ib) ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              A.length ≤ t.val ∧ t.val < ib.val ∧
                phi (T.edge t) = some c))
    (hlocation :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
      va ∈ TreeSequenceVertexSet A ∧
        vb ∉ TreeSequenceVertexSet A)
    (hbranch :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      alpha ∈ TreeMissingColors phi A ∧
        TreeColorSetClosed G phi A {alpha})
 :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
    let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
    let sameComponent :=
      TwoColorComponent G phi alpha beta (Sum.inl va) =
        TwoColorComponent G phi alpha beta (Sum.inl vb)
    sameComponent ∧ TreeInterchangeable G A phi alpha beta := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  let ia := HierarchyFirstMissingPosition phi T alpha
  let ib := HierarchyFirstMissingPosition phi T beta
  let va := T.vertex ia
  let vb := T.vertex ib
  let ell := T.length - A.length
  let yLength := min (A.length + (ell - 1)) T.length
  let Y := TreeSequencePrefix T yLength
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    exact @helper_segTrans_199 (@V) (@E) (@G) (@e0) (@S) (@U) (@W) (@hSU) (@hUW)
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    exact @helper_commonPrefix_209 (@V) (@E) (@G) (@e0) (@S) (@U) (@W) (@hSW) (@hUW) (@hlen)
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    exact @helper_stageSegment_219 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@segRefl)
        (@segTrans) (@a) (@d) (@hbound)
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    exact @helper_stageToT_227 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@stageSegment) (@j)
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    clear * - hz A q
    simp [A, q, HierarchyStarredStage, hz, Fin.last]
  have lastPositive (hz : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact @helper_lastPositive_238 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hz)
  have coreToA : TreeSequenceInitialSegment base.core A := by
    exact @helper_coreToA_250 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@segRefl) (@segTrans)
        (@stageSegment) (@lastZero) (@lastPositive)
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    exact @helper_TnToCore_259 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@segRefl)
  have TnToA := segTrans TnToCore coreToA
  have AToT : TreeSequenceInitialSegment A T := by
    exact @helper_AToT_266 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@segTrans) (@stageToT) (@lastZero)
        (@lastPositive)
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    exact @helper_ordinaryToA_273 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@stageSegment)
        (@lastZero) (@lastPositive) (@TnToA) (@j)
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    exact Fin.cases coreToA (fun i => ordinaryToA i.succ) j
  have YToT : TreeSequenceInitialSegment Y T :=
    ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
  have hmissingY : alpha ∈ TreeMissingColors phi Y ∧ beta ∈ TreeMissingColors phi Y :=
    hmissingPrefix
  have hElementaryY : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) :=
    hprefixElementary
  have firstMissing (c : Fin k) (hc : c ∈ TreeMissingColors phi Y) :
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
        (HierarchyFirstMissingPosition phi T c).val ≤ Y.length := by
    exact @helper_firstMissing_293 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@YToT) (@c) (@hc)
  have ha := firstMissing alpha hmissingY.1
  have hb := firstMissing beta hmissingY.2
  have vertexY (i : Fin (T.length + 1)) (hi : i.val ≤ Y.length) :
      T.vertex i ∈ TreeSequenceVertexSet Y := by
    clear * - i hi Y
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haY : va ∈ TreeSequenceVertexSet Y := vertexY ia ha.2
  have hbY : vb ∈ TreeSequenceVertexSet Y := vertexY ib hb.2
  have hout : va ∈ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A := hlocation
  have outsideIndex (i : Fin (T.length + 1))
      (hi : T.vertex i ∉ TreeSequenceVertexSet A) : A.length < i.val := by
    exact @helper_outsideIndex_325 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@AToT) (@i) (@hi)
  have hAib := outsideIndex ib hout.2
  have AToY : TreeSequenceInitialSegment A Y :=
    commonPrefix AToT YToT (by omega)
  have missingNotA (c : Fin k) (i : Fin (T.length + 1))
      (hmi : c ∈ MissingColors G phi (T.vertex i))
      (hiy : T.vertex i ∈ TreeSequenceVertexSet Y)
      (hia : T.vertex i ∉ TreeSequenceVertexSet A) : c ∉ TreeMissingColors phi A := by
    exact @helper_missingNotA_336 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@hElementaryY) (@AToY) (@c) (@i) (@hmi) (@hiy) (@hia)
  exact @helper_continuation_5074 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@hfewer) (@hminimal) (@hlarge) (@alpha) (@beta) (@hne) (@horderedUnused)
      (@hbranch) (@segRefl) (@segTrans) (@commonPrefix) (@lastZero) (@lastPositive) (@coreToA)
      (@TnToA) (@AToT) (@ordinaryToA) (@starredToA) (@YToT) (@hElementaryY) (@ha) (@hb)
      (@vertexY) (@haY) (@hbY) (@hout) (@hAib) (@missingNotA)
end GoldbergSeymour

end
