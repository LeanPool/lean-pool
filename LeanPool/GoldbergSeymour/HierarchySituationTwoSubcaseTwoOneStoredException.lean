/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module




public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseTwoData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseTwoExclusions
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseOneOne

/-!
# Hierarchy Situation Two Subcase Two One Stored Exception

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperSwapStep439Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx) (eta : Fin k),
   (∀ {X Y : TreeSequence G e0},
     TreeSequenceInitialSegment X Y →
      ∀ (col : PartialEdgeColoring E k), TreeMissingColors col X ⊆ TreeMissingColors col Y) →
    (∀ (col : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
      c ∈ MissingColors G col (T.vertex i) →
       c ∈ MissingColors G col (T.vertex (HierarchyFirstMissingPosition col T c)) ∧
        (↑(HierarchyFirstMissingPosition col T c) : ℕ) ≤ (↑i : ℕ)) →
     let H : TashkinovHierarchy ett base := C.hierarchy;
     let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
     let A : TreeSequence G e0 := HierarchyStarredStage H q;
     let ell : ℕ := HierarchyFullTailLength C;
     let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
     TreeSequenceInitialSegment A T →
      ell = T.length - A.length →
       X.length = T.length - (1 : ℕ) →
        (↑D.penultimateVertexIndex : ℕ) = X.length →
         (↑D.lastEdgeIndex : ℕ) = X.length →
          X.length + (1 : ℕ) = T.length →
           X.length = A.length + (ell - (1 : ℕ)) →
            (1 : ℕ) ≤ ell - (1 : ℕ) →
             ell - (1 : ℕ) < ell →
              TreeSequenceInitialSegment X T →
               TreeSequenceInitialSegment A X →
                T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X →
                 HierarchyFirstMissingPosition phi T eta = D.penultimateVertexIndex →
                  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                    HierarchyStarredStage P.counterexample.hierarchy
                       (Fin.last P.counterexample.hierarchy.dividerCount) =
                      A ∧
                     HierarchyFullTailLength P.counterexample = ell ∧
                      HierarchyFullTailPrefix P.counterexample (ell - (1 : ℕ)) = X ∧
                       HierarchyPathNumber P.counterexample.hierarchy = HierarchyPathNumber H) →
                   ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
                    (a b : Fin k),
                    a ≠ b →
                     a ∈ TreeMissingColors P.coloring A →
                      a ∈
                        HierarchyStageMissingColors P.counterexample.hierarchy
                         (Fin.last P.counterexample.hierarchy.dividerCount) →
                       (∀ (t : Fin T.length),
                         A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) ≠ some a) →
                        b ∈ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
                         a ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∨
                           b ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) →
                          P.coloring (T.edge D.lastEdgeIndex) = some D.theta →
                           D.theta ∉
                             MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
                            ∃ (P' :
                             HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                             P'.coloring =
                               TwoColorComponentSwap G P.coloring a b
                                (Sum.inl (T.vertex D.terminalVertexIndex)) ∧
                              (∀ v ∈ TreeSequenceVertexSet X,
                                MissingColors G P'.coloring v = MissingColors G P.coloring v) ∧
                               ∀ (t : Fin T.length),
                                A.length ≤ (↑t : ℕ) → P'.coloring (T.edge t) = P.coloring (T.edge t)

private abbrev helperContinuation1279Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
   ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
    eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     let H : TashkinovHierarchy ett base := C.hierarchy;
     let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
     let A : TreeSequence G e0 := HierarchyStarredStage H q;
     let ell : ℕ := HierarchyFullTailLength C;
     let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
     (2 : ℕ) ≤ ell →
      TreeSequenceInitialSegment A X →
       T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X →
        ∀ (gamma : Fin k),
         D.theta ≠ gamma →
          gamma ∈ HierarchyStageMissingColors C.hierarchy q ∧
            gamma ∉ HierarchySegmentColors C.hierarchy q eta →
           gamma ∈ TreeMissingColors phi A →
            gamma ≠ D.alpha →
             (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some gamma) →
              (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                HierarchyStarredStage P.counterexample.hierarchy
                   (Fin.last P.counterexample.hierarchy.dividerCount) =
                  A ∧
                 HierarchyFullTailLength P.counterexample = ell ∧
                  HierarchyFullTailPrefix P.counterexample (ell - (1 : ℕ)) = X ∧
                   HierarchyPathNumber P.counterexample.hierarchy = HierarchyPathNumber H) →
               ∀
                (seriesProper :
                 ∀ (j : Fin (ett.rounds + (1 : ℕ))),
                  IsProperEdgeColoring G (ett.series.data.coloring j))
                (seriesOne :
                 ∀ (j : Fin (ett.rounds + (1 : ℕ))),
                  IsOneEdgeUncolored (ett.series.data.coloring j) e0),
                let selfCorr : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
                 {
                  replacementInput := input, replacementSeries := ett.series,
                  replacementETT := ett, rungAgreement := rfl, seriesPresentation := HEq.rfl,
                  finalGeneratingColoring := ett.generatingColoring,
                  ladderTreesAgree := fun (x : Fin ett.rounds) ↦ rfl,
                  storedColorsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
                  connectingEdgesAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
                  extensionKindsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
                  replacementProper := seriesProper, replacementOneUncolored := seriesOne,
                  replacementStable := fun (x : Fin ett.rounds) ↦
                   (⟨fun (x_1 : E)
                      (x_2 : TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) x_1)
                      (x_3 :
                       ∃
                        c ∈
                         TreeMissingColors (ett.series.data.coloring x.succ)
                           (ett.series.data.tree x.succ.castSucc) ∪
                          TashkinovStoredColors ett.series.data x.succ,
                        ett.series.data.coloring x.succ x_1 = some c) ↦
                     rfl,
                     fun (x_1 : V)
                      (x_2 : x_1 ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc)) ↦
                     rfl⟩ :
                    (∀ (f : E),
                      TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) f →
                       (∃
                         c ∈
                          TreeMissingColors (ett.series.data.coloring x.succ)
                            (ett.series.data.tree x.succ.castSucc) ∪
                           TashkinovStoredColors ett.series.data x.succ,
                         ett.series.data.coloring x.succ f = some c) →
                        ett.series.data.coloring x.succ f = ett.series.data.coloring x.succ f) ∧
                     ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc),
                      MissingColors G (ett.series.data.coloring x.succ) v =
                       MissingColors G (ett.series.data.coloring x.succ) v) :
                  CorrespondingExtendedTashkinovTree G k e0 ett phi T };
                let P0 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
                 {
                  coloring := phi, corresponding := selfCorr, maximum := C.maximum,
                  replacementBase := base, counterexample := C,
                  sameGood :=
                   (⟨(⟨rfl,
                       (⟨by
                         have := GoldbergSeymour.TreeSequence.positive T
                         omega,
                         (⟨HEq.rfl,
                           (⟨HEq.rfl,
                             (⟨Iff.rfl,
                               fun
                                (x :
                                 ett.series.data.kind (Fin.last ett.rounds) =
                                  some TashkinovExtensionKind.PE) ↦
                               rfl⟩ :
                              (ett.series.data.kind (Fin.last ett.rounds) =
                                 some TashkinovExtensionKind.PE ↔
                                selfCorr.replacementETT.series.data.kind
                                  (Fin.last selfCorr.replacementETT.rounds) =
                                 some TashkinovExtensionKind.PE) ∧
                               (ett.series.data.kind (Fin.last ett.rounds) =
                                 some TashkinovExtensionKind.PE →
                                base.closure = base.closure))⟩ :
                            C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                             (ett.series.data.kind (Fin.last ett.rounds) =
                                some TashkinovExtensionKind.PE ↔
                               selfCorr.replacementETT.series.data.kind
                                 (Fin.last selfCorr.replacementETT.rounds) =
                                some TashkinovExtensionKind.PE) ∧
                              (ett.series.data.kind (Fin.last ett.rounds) =
                                some TashkinovExtensionKind.PE →
                               base.closure = base.closure))⟩ :
                          C.hierarchy.stage ≍ C.hierarchy.stage ∧
                           C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                            (ett.series.data.kind (Fin.last ett.rounds) =
                               some TashkinovExtensionKind.PE ↔
                              selfCorr.replacementETT.series.data.kind
                                (Fin.last selfCorr.replacementETT.rounds) =
                               some TashkinovExtensionKind.PE) ∧
                             (ett.series.data.kind (Fin.last ett.rounds) =
                               some TashkinovExtensionKind.PE →
                              base.closure = base.closure))⟩ :
                        C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
                         C.hierarchy.stage ≍ C.hierarchy.stage ∧
                          C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                           (ett.series.data.kind (Fin.last ett.rounds) =
                              some TashkinovExtensionKind.PE ↔
                             selfCorr.replacementETT.series.data.kind
                               (Fin.last selfCorr.replacementETT.rounds) =
                              some TashkinovExtensionKind.PE) ∧
                            (ett.series.data.kind (Fin.last ett.rounds) =
                              some TashkinovExtensionKind.PE →
                             base.closure = base.closure))⟩ :
                      base.core = base.core ∧
                       C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
                        C.hierarchy.stage ≍ C.hierarchy.stage ∧
                         C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                          (ett.series.data.kind (Fin.last ett.rounds) =
                             some TashkinovExtensionKind.PE ↔
                            selfCorr.replacementETT.series.data.kind
                              (Fin.last selfCorr.replacementETT.rounds) =
                             some TashkinovExtensionKind.PE) ∧
                           (ett.series.data.kind (Fin.last ett.rounds) =
                             some TashkinovExtensionKind.PE →
                            base.closure = base.closure)),
                     Exists.intro
                      (by
                       have := GoldbergSeymour.TreeSequence.positive T
                       omega)
                      fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) ↦
                      (⟨rfl, fun (x_1 : Fin k) (x_2 : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) ↦
                        rfl⟩ :
                       HierarchyStoredColorsAt C.hierarchy x =
                         HierarchyStoredColorsAt C.hierarchy
                          (Fin.cast
                           (by
                            have :=
                             GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
                              selfCorr
                            have := GoldbergSeymour.TreeSequence.positive T
                            omega)
                           x) ∧
                        ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
                         C.good.gamma x eta =
                          C.good.gamma
                           (Fin.cast
                            (by
                             have :=
                              GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
                               selfCorr
                             have := GoldbergSeymour.TreeSequence.positive T
                             omega)
                            x)
                           eta)⟩ :
                    SameHierarchyStages C.hierarchy C.hierarchy ∧
                     ∃ (hcount : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
                      ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
                       have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
                        Fin.cast
                         (by
                          have :=
                           GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement selfCorr
                          have := GoldbergSeymour.TreeSequence.positive T
                          omega)
                         j;
                       HierarchyStoredColorsAt C.hierarchy j =
                         HierarchyStoredColorsAt C.hierarchy j₂ ∧
                        ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j,
                         C.good.gamma j eta = C.good.gamma j₂ eta),
                  minimumContext := ctx :
                  HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
                (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
                  (a b : Fin k),
                  a ≠ b →
                   a ∈ TreeMissingColors P.coloring A →
                    a ∈
                      HierarchyStageMissingColors P.counterexample.hierarchy
                       (Fin.last P.counterexample.hierarchy.dividerCount) →
                     (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) ≠ some a) →
                      b ∈ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
                       a ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∨
                         b ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) →
                        P.coloring (T.edge D.lastEdgeIndex) = some D.theta →
                         D.theta ∉ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
                          ∃ (P' :
                           HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                           P'.coloring =
                             TwoColorComponentSwap G P.coloring a b
                              (Sum.inl (T.vertex D.terminalVertexIndex)) ∧
                            (∀ v ∈ TreeSequenceVertexSet X,
                              MissingColors G P'.coloring v = MissingColors G P.coloring v) ∧
                             ∀ (t : Fin T.length),
                              A.length ≤ (↑t : ℕ) →
                               P'.coloring (T.edge t) = P.coloring (T.edge t)) →
                 A.length ≤ (↑D.lastEdgeIndex : ℕ) →
                  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                    eta ∈
                      HierarchyStoredColorsAt P.counterexample.hierarchy
                       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
                     P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                       eta =
                      (insert D.theta ({ gamma } : Finset (Fin k)) : Finset (Fin k))) →
                   False

private abbrev helperContinuation834Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx) (eta : Fin k),
   (∀ (col : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
     c ∈ MissingColors G col (T.vertex i) →
      c ∈ MissingColors G col (T.vertex (HierarchyFirstMissingPosition col T c)) ∧
       (↑(HierarchyFirstMissingPosition col T c) : ℕ) ≤ (↑i : ℕ)) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (hAT : TreeSequenceInitialSegment A T),
     X.length = T.length - (1 : ℕ) →
      (↑D.penultimateVertexIndex : ℕ) = X.length →
       (↑D.lastEdgeIndex : ℕ) = X.length →
        X.length + (1 : ℕ) = T.length →
         X.length = A.length + (ell - (1 : ℕ)) →
          TreeSequenceInitialSegment X T →
           T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X →
            HierarchyFirstMissingPosition phi T eta = D.penultimateVertexIndex →
             ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
              (a b : Fin k),
              a ≠ b →
               a ∈ TreeMissingColors P.coloring A →
                b ∈ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
                 a ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∨
                   b ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) →
                  let J :
                   ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
                   P.corresponding.replacementETT;
                  let C' : HierarchyCounterexample P.replacementBase := P.counterexample;
                  let col : PartialEdgeColoring E k := P.coloring;
                  let H' : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
                   C'.hierarchy;
                  let q' : Fin (H'.dividerCount + (1 : ℕ)) := Fin.last H'.dividerCount;
                  let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
                  let mu : PartialEdgeColoring E k := TwoColorComponentSwap G col a b z;
                  HierarchyStarredStage C'.hierarchy (Fin.last C'.hierarchy.dividerCount) = A →
                   HierarchyStarredStage H' q' = A →
                    HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - (1 : ℕ)) = X →
                     ColoredVertexSetElementary G col (TreeSequenceVertexSet X) →
                      HierarchyFirstMissingPosition col T b = D.penultimateVertexIndex →
                       ∀ v ∈ TreeSequenceVertexSet A,
                        ∀ (i : Fin (A.length + (1 : ℕ))),
                         a ∈
                            MissingColors G col (T.vertex (HierarchyFirstMissingPosition col T a)) ∧
                           (↑(HierarchyFirstMissingPosition col T a) : ℕ) ≤
                            (↑(Fin.castLE (Nat.succ_le_succ hAT.1) i) : ℕ) →
                          let va : V := T.vertex (HierarchyFirstMissingPosition col T a);
                          let vb : V := T.vertex D.penultimateVertexIndex;
                          let vt : V := T.vertex D.terminalVertexIndex;
                          va ∈ TreeSequenceVertexSet X →
                           (↑(HierarchyFirstMissingPosition col T a) : ℕ) <
                             (↑D.penultimateVertexIndex : ℕ) →
                            a ∈
                               TreeMissingColors col
                                (HierarchyFullTailPrefix C'
                                 (HierarchyFullTailLength C' - (1 : ℕ))) ∧
                              b ∈
                               TreeMissingColors col
                                (HierarchyFullTailPrefix C'
                                 (HierarchyFullTailLength C' - (1 : ℕ))) →
                             (∀ (w : V ⊕ E), w ∈ TwoColorComponent G col a b w) →
                              Disjoint (TwoColorComponent G col a b z)
                                (TwoColorComponent G col a b (Sum.inl va)) →
                               TwoColorPathComponent G col a b z →
                                (0 : ℕ) < H'.dividerCount ∧
                                   a ∈
                                    TreeMissingColors col
                                     (H'.stage
                                      (⟨H'.dividerCount,
                                        by
                                        have := GoldbergSeymour.TreeSequence.positive T
                                        omega⟩ :
                                       Fin (H'.dividerCount + (2 : ℕ)))) ∨
                                  H'.dividerCount = (0 : ℕ) ∧
                                   (a ∈
                                     TreeMissingColors col
                                      (J.series.data.tree (Fin.last J.rounds).castSucc) ∨
                                    a ∈ TreeMissingColors col (HierarchyStarredStage H' q') ∧
                                     a ∉ TashkinovStoredColors J.series.data (Fin.last J.rounds) ∧
                                      b ∉ TashkinovStoredColors J.series.data (Fin.last J.rounds)) →
                                 (have C : Set (V ⊕ E) := TwoColorComponent G col a b z;
                                  have phi' : PartialEdgeColoring E k :=
                                   TwoColorComponentSwap G col a b z;
                                  (∀ (v : V),
                                    Sum.inl v ∉ C →
                                     MissingColors G phi' v = MissingColors G col v) ∧
                                   (∀ (v : V),
                                     Sum.inl v ∈ C →
                                      a ∈ MissingColors G col v → b ∈ MissingColors G phi' v) ∧
                                    (∀ (v : V),
                                      Sum.inl v ∈ C →
                                       b ∈ MissingColors G col v → a ∈ MissingColors G phi' v) ∧
                                     ∀ (v : V) (c : Fin k),
                                      c ≠ a →
                                       c ≠ b →
                                        (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G col v)) →
                                  (∀ u ∈ TreeSequenceVertexSet X,
                                    MissingColors G mu u = MissingColors G col u) →
                                   (∀ (t : Fin T.length),
                                     A.length ≤ (↑t : ℕ) → mu (T.edge t) = col (T.edge t)) →
                                    ∃ (P' :
                                     HierarchyReplacementPresentation G k e0 input T phi ett base C
                                      ctx),
                                     P'.coloring =
                                       TwoColorComponentSwap G P.coloring a b
                                        (Sum.inl (T.vertex D.terminalVertexIndex)) ∧
                                      (∀ v ∈ TreeSequenceVertexSet X,
                                        MissingColors G P'.coloring v =
                                         MissingColors G P.coloring v) ∧
                                       ∀ (t : Fin T.length),
                                        A.length ≤ (↑t : ℕ) →
                                         P'.coloring (T.edge t) = P.coloring (T.edge t)

private abbrev helperBranch993Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
   ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
    eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     let H : TashkinovHierarchy ett base := C.hierarchy;
     let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
     let A : TreeSequence G e0 := HierarchyStarredStage H q;
     let ell : ℕ := HierarchyFullTailLength C;
     let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
     TreeSequenceInitialSegment A X →
      T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X →
       ∀ gamma ∈ TreeMissingColors phi A,
        (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some gamma) →
         ∀
          (seriesProper :
           ∀ (j : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (ett.series.data.coloring j))
          (seriesOne :
           ∀ (j : Fin (ett.rounds + (1 : ℕ))), IsOneEdgeUncolored (ett.series.data.coloring j) e0),
          let selfCorr : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
           {
            replacementInput := input, replacementSeries := ett.series, replacementETT := ett,
            rungAgreement := rfl, seriesPresentation := HEq.rfl,
            finalGeneratingColoring := ett.generatingColoring,
            ladderTreesAgree := fun (x : Fin ett.rounds) ↦ rfl,
            storedColorsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
            connectingEdgesAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
            extensionKindsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
            replacementProper := seriesProper, replacementOneUncolored := seriesOne,
            replacementStable := fun (x : Fin ett.rounds) ↦
             (⟨fun (x_1 : E) (_ : TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) x_1)
                (_ :
                 ∃
                  c ∈
                   TreeMissingColors (ett.series.data.coloring x.succ)
                     (ett.series.data.tree x.succ.castSucc) ∪
                    TashkinovStoredColors ett.series.data x.succ,
                  ett.series.data.coloring x.succ x_1 = some c) ↦
               rfl,
               fun (x_1 : V)
                (_ : x_1 ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc)) ↦
               rfl⟩ :
              (∀ (f : E),
                TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) f →
                 (∃
                   c ∈
                    TreeMissingColors (ett.series.data.coloring x.succ)
                      (ett.series.data.tree x.succ.castSucc) ∪
                     TashkinovStoredColors ett.series.data x.succ,
                   ett.series.data.coloring x.succ f = some c) →
                  ett.series.data.coloring x.succ f = ett.series.data.coloring x.succ f) ∧
               ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc),
                MissingColors G (ett.series.data.coloring x.succ) v =
                 MissingColors G (ett.series.data.coloring x.succ) v) :
            CorrespondingExtendedTashkinovTree G k e0 ett phi T };
          let P0 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
           {
            coloring := phi, corresponding := selfCorr, maximum := C.maximum,
            replacementBase := base, counterexample := C,
            sameGood :=
             (⟨(⟨rfl,
                 (⟨rfl,
                   (⟨HEq.rfl,
                     (⟨HEq.rfl,
                       (⟨Iff.rfl,
                         fun
                          (_ :
                           ett.series.data.kind (Fin.last ett.rounds) =
                            some TashkinovExtensionKind.PE) ↦
                         rfl⟩ :
                        (ett.series.data.kind (Fin.last ett.rounds) =
                           some TashkinovExtensionKind.PE ↔
                          selfCorr.replacementETT.series.data.kind
                            (Fin.last selfCorr.replacementETT.rounds) =
                           some TashkinovExtensionKind.PE) ∧
                         (ett.series.data.kind (Fin.last ett.rounds) =
                           some TashkinovExtensionKind.PE →
                          base.closure = base.closure))⟩ :
                      C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                       (ett.series.data.kind (Fin.last ett.rounds) =
                          some TashkinovExtensionKind.PE ↔
                         selfCorr.replacementETT.series.data.kind
                           (Fin.last selfCorr.replacementETT.rounds) =
                          some TashkinovExtensionKind.PE) ∧
                        (ett.series.data.kind (Fin.last ett.rounds) =
                          some TashkinovExtensionKind.PE →
                         base.closure = base.closure))⟩ :
                    C.hierarchy.stage ≍ C.hierarchy.stage ∧
                     C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                        selfCorr.replacementETT.series.data.kind
                          (Fin.last selfCorr.replacementETT.rounds) =
                         some TashkinovExtensionKind.PE) ∧
                       (ett.series.data.kind (Fin.last ett.rounds) =
                         some TashkinovExtensionKind.PE →
                        base.closure = base.closure))⟩ :
                  C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
                   C.hierarchy.stage ≍ C.hierarchy.stage ∧
                    C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                       selfCorr.replacementETT.series.data.kind
                         (Fin.last selfCorr.replacementETT.rounds) =
                        some TashkinovExtensionKind.PE) ∧
                      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                       base.closure = base.closure))⟩ :
                base.core = base.core ∧
                 C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
                  C.hierarchy.stage ≍ C.hierarchy.stage ∧
                   C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                      selfCorr.replacementETT.series.data.kind
                        (Fin.last selfCorr.replacementETT.rounds) =
                       some TashkinovExtensionKind.PE) ∧
                     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                      base.closure = base.closure)),
               Exists.intro rfl fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) ↦
                (⟨rfl, fun (x_1 : Fin k) (_ : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) ↦ rfl⟩ :
                 HierarchyStoredColorsAt C.hierarchy x =
                   HierarchyStoredColorsAt C.hierarchy (Fin.cast (by omega) x) ∧
                  ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
                   C.good.gamma x eta = C.good.gamma (Fin.cast (by omega) x) eta)⟩ :
              SameHierarchyStages C.hierarchy C.hierarchy ∧
               ∃ (_ : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
                ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
                 have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) := Fin.cast (by omega) j;
                 HierarchyStoredColorsAt C.hierarchy j = HierarchyStoredColorsAt C.hierarchy j₂ ∧
                  ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j,
                   C.good.gamma j eta = C.good.gamma j₂ eta),
            minimumContext := ctx :
            HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
          (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (a b : Fin k),
            a ≠ b →
             a ∈ TreeMissingColors P.coloring A →
              a ∈
                HierarchyStageMissingColors P.counterexample.hierarchy
                 (Fin.last P.counterexample.hierarchy.dividerCount) →
               (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) ≠ some a) →
                b ∈ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
                 a ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∨
                   b ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) →
                  P.coloring (T.edge D.lastEdgeIndex) = some D.theta →
                   D.theta ∉ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
                    ∃ (P' : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                     P'.coloring =
                       TwoColorComponentSwap G P.coloring a b
                        (Sum.inl (T.vertex D.terminalVertexIndex)) ∧
                      (∀ v ∈ TreeSequenceVertexSet X,
                        MissingColors G P'.coloring v = MissingColors G P.coloring v) ∧
                       ∀ (t : Fin T.length),
                        A.length ≤ (↑t : ℕ) → P'.coloring (T.edge t) = P.coloring (T.edge t)) →
           A.length ≤ (↑D.lastEdgeIndex : ℕ) →
            (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
              eta ∈
                HierarchyStoredColorsAt P.counterexample.hierarchy
                 (Fin.last P.counterexample.hierarchy.dividerCount) ∧
               P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta =
                { D.theta, gamma }) →
             (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
               (∀ v ∈ TreeSequenceVertexSet X,
                 MissingColors G P.coloring v = MissingColors G phi v) →
                (∀ (t : Fin T.length),
                  A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) = phi (T.edge t)) →
                 eta ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) → False) →
              ∀ (P1 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
               (∀ v ∈ TreeSequenceVertexSet X,
                 MissingColors G P1.coloring v = MissingColors G P0.coloring v) →
                (∀ (t : Fin T.length),
                  A.length ≤ (↑t : ℕ) → P1.coloring (T.edge t) = P0.coloring (T.edge t)) →
                 gamma ∈ MissingColors G P1.coloring (T.vertex D.terminalVertexIndex) → False

private theorem helper_hgammaTail_297.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
      (eta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    X.length = T.length - (1 : ℕ) →
    (↑D.penultimateVertexIndex : ℕ) = X.length →
    (↑D.lastEdgeIndex : ℕ) = X.length →
    X.length + (1 : ℕ) = T.length →
    X.length = A.length + (ell - (1 : ℕ)) →
    HierarchyFirstMissingPosition phi T eta = D.penultimateVertexIndex →
    ∀ (gamma : Fin k),
    D.theta ≠ gamma →
    gamma ∈ HierarchyStageMissingColors C.hierarchy q ∧
        gamma ∉ HierarchySegmentColors C.hierarchy q eta →
    ∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) →
    phi (T.edge t) ≠ some gamma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D eta H q A ell X hXlen hPenVal hLastVal
      hTlen hXexact hetaFirst gamma hthetaGamma hgammaAvoid t ht hc
  by_cases hlast : t = D.lastEdgeIndex
  · have htg : D.theta = gamma :=
      Option.some.inj (D.thetaOnLastEdge.symm.trans (hlast ▸ hc))
    exact hthetaGamma htg
  · have hpos : t.val < D.penultimateVertexIndex.val := by
      have hp := D.penultimateVertexPosition
      have he := D.lastEdgePosition
      have htlt := t.isLt
      have hneq : t.val ≠ D.lastEdgeIndex.val := fun h => hlast (Fin.ext h)
      omega
    apply hgammaAvoid.2
    unfold HierarchySegmentColors
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hend : H.stage q.succ = T := H.terminalStage
    let r : Fin (H.stage q.succ).length :=
      Fin.cast (congrArg TreeSequence.length hend.symm) t
    refine ⟨r, ht, ?_, ?_⟩
    · simp only [hetaFirst]
      dsimp [r]
      rw [hend]
      omega
    · have edgeCast (U W : TreeSequence G e0) (h : U = W)
          (i : Fin W.length) :
          U.edge (Fin.cast (congrArg TreeSequence.length h.symm) i) = W.edge i := by
        cases h
        rfl
      change phi ((H.stage q.succ).edge r) = some gamma
      rw [edgeCast _ _ hend t]
      exact hc

private theorem helper_continuation_834.{u_1, u_2} :
    helperContinuation834Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D eta firstMissing H q A ell X hAT hXlen
      hPenVal hLastVal hTlen hXexact hXT hyp hetaFirst P a b hne haA hb hterminal J C' col H' q'
      z mu hstar hstar' hXeq hxElem hbFirst v hv i haFirst va vb vt hvaX horder hmissingP rootMem
      hdis hpath hcase hbehavior hprefix htailEdges
  have hbNew : b ∈ MissingColors G mu (T.vertex D.penultimateVertexIndex) := by
    rw [hprefix _ hyp]
    exact hb
  have hbNewFirst : HierarchyFirstMissingPosition mu T b =
      D.penultimateVertexIndex := by
    have hm := firstMissing mu b D.penultimateVertexIndex hbNew
    let i : Fin (X.length + 1) := ⟨(HierarchyFirstMissingPosition mu T b).val, by
      exact Nat.lt_succ_of_le (hm.2.trans (Nat.le_of_eq hPenVal))⟩
    have hv : T.vertex (HierarchyFirstMissingPosition mu T b) ∈
        TreeSequenceVertexSet X :=
      (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hmOld : b ∈ MissingColors G col
        (T.vertex (HierarchyFirstMissingPosition mu T b)) := by
      rw [← hprefix _ hv]
      exact hm.1
    by_contra hn
    exact Finset.disjoint_left.mp
      (hxElem hv hyp (fun he => hn (T.vertex_injective he))) hmOld hb
  have hstoredFirst : ∀ c, c ∈ HierarchyStoredColorsAt H' q' →
      HierarchyFirstMissingPosition mu T c = HierarchyFirstMissingPosition col T c := by
    intro c hc
    have hca : c ≠ a := by
      intro he
      have hnot := (Finset.mem_sdiff.mp hc).2
      apply hnot
      change c ∈ TreeMissingColors col (HierarchyStarredStage H' q')
      rw [hstar', he]
      exact haA
    by_cases hcb : c = b
    · subst c
      exact hbNewFirst.trans hbFirst.symm
    · have hcandidates :
          (Finset.univ.filter fun i : Fin (T.length + 1) =>
            c ∈ MissingColors G mu (T.vertex i)) =
          (Finset.univ.filter fun i : Fin (T.length + 1) =>
            c ∈ MissingColors G col (T.vertex i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hbehavior.2.2.2 _ c hca hcb
      unfold HierarchyFirstMissingPosition
      simp only [hcandidates]
  have hfull := StableChangeCasesOneTwoFullTail G k e0
    P.corresponding.replacementInput T col J P.replacementBase C' P.minimumContext
    a b hne hmissingP
    z hpath mu rfl hcase hdis
    (by dsimp only; intro t ht
        exact htailEdges t (by simpa only [hstar] using ht))
    (by intro v hv; rw [hXeq] at hv; exact hprefix v hv) hstoredFirst
  obtain ⟨corr, hmax, baseNew, Hnew, goodNew, hsameGood⟩ := hfull.2.2.2.2
  have hnonElem : ¬ ColoredVertexSetElementary G mu (TreeSequenceVertexSet T) := by
    intro he
    have htMem : vt ∈ TreeSequenceVertexSet T :=
      (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨D.terminalVertexIndex, Finset.mem_univ _, rfl⟩
    rcases hterminal with hta | htb
    · have hbTerminal : b ∈ MissingColors G mu vt := hbehavior.2.1 vt (rootMem z) hta
      have hpMem := TreeSequenceInitialSegmentVertexSetSubset hXT hyp
      have hnept : vb ≠ vt := by
        intro heq
        have hi := congrArg Fin.val (T.vertex_injective heq)
        have hpp := D.penultimateVertexPosition
        have htp := D.terminalVertexPosition
        omega
      exact Finset.disjoint_left.mp (he hpMem htMem hnept) hbNew hbTerminal
    · have haTerminal : a ∈ MissingColors G mu vt := hbehavior.2.2.1 vt (rootMem z) htb
      have hvaNot : Sum.inl va ∉ TwoColorComponent G col a b z := by
        intro hva
        exact Set.disjoint_left.mp hdis hva (rootMem (Sum.inl va))
      have haNew : a ∈ MissingColors G mu va := by
        rw [hbehavior.1 va hvaNot]
        exact haFirst.1
      have haMem := TreeSequenceInitialSegmentVertexSetSubset hXT hvaX
      have hneat : va ≠ vt := by
        intro heq
        have hi := congrArg Fin.val (T.vertex_injective heq)
        have htp := D.terminalVertexPosition
        omega
      exact Finset.disjoint_left.mp (he haMem htMem hneat) haNew haTerminal
  let Cnew : HierarchyCounterexample baseNew := {
    positive := by rw [corr.rungAgreement]; exact C'.positive
    hierarchy := Hnew
    good := goodNew
    maximum := hmax
    notElementary := hnonElem }
  obtain ⟨Pnew, hcolor⟩ := HierarchyReplacementPresentationTrans
    G k e0 input T phi ett base C ctx P mu corr baseNew Cnew hsameGood
  refine ⟨Pnew, hcolor, ?_, ?_⟩
  · simpa [hcolor] using hprefix
  · simpa [hcolor] using htailEdges

private theorem helper_hdis_835.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
      (eta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (hAT : TreeSequenceInitialSegment A T),
    X.length = T.length - (1 : ℕ) →
    (↑D.penultimateVertexIndex : ℕ) = X.length →
    (↑D.lastEdgeIndex : ℕ) = X.length →
    X.length + (1 : ℕ) = T.length →
    X.length = A.length + (ell - (1 : ℕ)) →
    HierarchyFirstMissingPosition phi T eta = D.penultimateVertexIndex →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (a b : Fin k),
    b ∈ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
    a ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∨
        b ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) →
    let col : PartialEdgeColoring E k := P.coloring;
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    IsProperEdgeColoring G col →
    HierarchyFirstMissingPosition col T b = D.penultimateVertexIndex →
    ∀ (i : Fin (A.length + (1 : ℕ))),
    a ∈ MissingColors G col (T.vertex (HierarchyFirstMissingPosition col T a)) ∧
        (↑(HierarchyFirstMissingPosition col T a) : ℕ) ≤
          (↑(Fin.castLE (Nat.succ_le_succ hAT.1) i) : ℕ) →
    let va : V := T.vertex (HierarchyFirstMissingPosition col T a);
    let vb : V := T.vertex D.penultimateVertexIndex;
    let _ : V := T.vertex D.terminalVertexIndex;
    (↑(HierarchyFirstMissingPosition col T a) : ℕ) < (↑D.penultimateVertexIndex : ℕ) →
    TwoColorComponent G col a b (Sum.inl va) = TwoColorComponent G col a b (Sum.inl vb) →
    (∀ (w : V ⊕ E), w ∈ TwoColorComponent G col a b w) →
    (∀ (w : V),
        a ∈ MissingColors G col w ∨ b ∈ MissingColors G col w →
          ((TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl w)).Subsingleton) →
    Disjoint (TwoColorComponent G col a b z) (TwoColorComponent G col a b (Sum.inl va)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D eta H q A ell X hAT hXlen hPenVal
      hLastVal hTlen hXexact hetaFirst P a b hb hterminal col z hp hbFirst i haFirst va vb vt
      horder hsame rootMem leaf
  rcases TwoColorComponentsDisjoint G col a b z (Sum.inl va) with heq | hd
  · obtain ⟨u, w, p, hpPath, hsupp⟩ :=
      TwoColorComponentSpanningPath G col a b hp z
    have endpoint (y : V)
        (hy : Sum.inl y ∈ TwoColorComponent G col a b z)
        (hm : a ∈ MissingColors G col y ∨ b ∈ MissingColors G col y) :
        Sum.inl y = u ∨ Sum.inl y = w := by
      have hySupp : Sum.inl y ∈ p.support := by
        change Sum.inl y ∈ {x | x ∈ p.support}
        rw [hsupp]
        exact hy
      by_contra hn
      push Not at hn
      exact hpPath.isTrail.notMem_support_of_subsingleton_neighborSet
        hn.1 hn.2 (leaf y hm) hySupp
    have haEnd := endpoint va (heq.symm ▸ rootMem (Sum.inl va)) (Or.inl haFirst.1)
    have hbEnd := endpoint vb
      (heq.symm ▸ hsame.symm ▸ rootMem (Sum.inl vb)) (Or.inr hb)
    have htEnd := endpoint vt (rootMem z) hterminal
    have hab : (Sum.inl va : Sum V E) ≠ Sum.inl vb := by
      intro h
      have hi := congrArg Fin.val (T.vertex_injective (Sum.inl.inj h))
      omega
    have hat : (Sum.inl va : Sum V E) ≠ Sum.inl vt := by
      intro h
      have hi := congrArg Fin.val (T.vertex_injective (Sum.inl.inj h))
      have ht := D.terminalVertexPosition
      omega
    have hbt : (Sum.inl vb : Sum V E) ≠ Sum.inl vt := by
      intro h
      have hi := congrArg Fin.val (T.vertex_injective (Sum.inl.inj h))
      have hbp := D.penultimateVertexPosition
      have htp := D.terminalVertexPosition
      omega
    rcases haEnd with haEnd | haEnd <;>
      rcases hbEnd with hbEnd | hbEnd <;>
      rcases htEnd with htEnd | htEnd
    · exact (hab (haEnd.trans hbEnd.symm)).elim
    · exact (hab (haEnd.trans hbEnd.symm)).elim
    · exact (hat (haEnd.trans htEnd.symm)).elim
    · exact (hbt (hbEnd.trans htEnd.symm)).elim
    · exact (hbt (hbEnd.trans htEnd.symm)).elim
    · exact (hat (haEnd.trans htEnd.symm)).elim
    · exact (hab (haEnd.trans hbEnd.symm)).elim
    · exact (hab (haEnd.trans hbEnd.symm)).elim
  · exact hd

private theorem helper_hprefix_914.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (hAT : TreeSequenceInitialSegment A T),
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (a b : Fin k),
    a ≠ b →
    b ∈ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
    let col : PartialEdgeColoring E k := P.coloring;
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let mu : PartialEdgeColoring E k := TwoColorComponentSwap G col a b z;
    ColoredVertexSetElementary G col (TreeSequenceVertexSet X) →
    ∀ (i : Fin (A.length + (1 : ℕ))),
    a ∈ MissingColors G col (T.vertex (HierarchyFirstMissingPosition col T a)) ∧
        (↑(HierarchyFirstMissingPosition col T a) : ℕ) ≤
          (↑(Fin.castLE (Nat.succ_le_succ hAT.1) i) : ℕ) →
    let va : V := T.vertex (HierarchyFirstMissingPosition col T a);
    let vb : V := T.vertex D.penultimateVertexIndex;
    va ∈ TreeSequenceVertexSet X →
    TwoColorComponent G col a b (Sum.inl va) = TwoColorComponent G col a b (Sum.inl vb) →
    (∀ (w : V ⊕ E), w ∈ TwoColorComponent G col a b w) →
    Disjoint (TwoColorComponent G col a b z) (TwoColorComponent G col a b (Sum.inl va)) →
    (have C : Set (V ⊕ E) := TwoColorComponent G col a b z;
      have phi' : PartialEdgeColoring E k := TwoColorComponentSwap G col a b z;
      (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G col v) ∧
        (∀ (v : V),
            Sum.inl v ∈ C → a ∈ MissingColors G col v → b ∈ MissingColors G phi' v) ∧
          (∀ (v : V),
              Sum.inl v ∈ C → b ∈ MissingColors G col v → a ∈ MissingColors G phi' v) ∧
            ∀ (v : V) (c : Fin k),
              c ≠ a → c ≠ b → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G col v)) →
    (∀ {u : V} {e : E},
        Sum.inl u ∈ TwoColorComponent G col a b z →
          Incident G u e →
            col e = some a ∨ col e = some b → Sum.inr e ∈ TwoColorComponent G col a b z) →
    ∀ u ∈ TreeSequenceVertexSet X,
    MissingColors G mu u = MissingColors G col u := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell X hAT hyp P a b hne hb col z mu
      hxElem i haFirst va vb hvaX hsame rootMem hdis hbehavior edgeIn u hu
  by_cases huQ : Sum.inl u ∈ TwoColorComponent G col a b z
  · have haNot : a ∉ MissingColors G col u := by
      intro hau
      have huv : u = va := by
        by_contra hn
        exact Finset.disjoint_left.mp (hxElem hu hvaX hn) hau haFirst.1
      exact Set.disjoint_left.mp hdis huQ (huv.symm ▸ rootMem (Sum.inl va))
    have hbNot : b ∉ MissingColors G col u := by
      intro hbu
      have huv : u = vb := by
        by_contra hn
        exact Finset.disjoint_left.mp (hxElem hu hyp hn) hbu hb
      exact Set.disjoint_left.mp hdis huQ
        (huv.symm ▸ hsame.symm ▸ rootMem (Sum.inl vb))
    obtain ⟨ea, hea, hca⟩ : ∃ e, Incident G u e ∧ col e = some a := by
      simpa [MissingColors, PresentColors] using haNot
    obtain ⟨eb, heb, hcb⟩ : ∃ e, Incident G u e ∧ col e = some b := by
      simpa [MissingColors, PresentColors] using hbNot
    have hnewa : mu eb = some a := by
      simp [mu, TwoColorComponentSwap, edgeIn huQ heb (Or.inr hcb), hcb, hne.symm]
    have hnewb : mu ea = some b := by
      simp [mu, TwoColorComponentSwap, edgeIn huQ hea (Or.inl hca), hca]
    have haNewNot : a ∉ MissingColors G mu u := by
      simpa [MissingColors, PresentColors] using
        (show ∃ e, Incident G u e ∧ mu e = some a from ⟨eb, heb, hnewa⟩)
    have hbNewNot : b ∉ MissingColors G mu u := by
      simpa [MissingColors, PresentColors] using
        (show ∃ e, Incident G u e ∧ mu e = some b from ⟨ea, hea, hnewb⟩)
    apply Finset.ext
    intro c
    by_cases hca : c = a
    · simp [hca, haNot, haNewNot]
    · by_cases hcb : c = b
      · simp [hcb, hbNot, hbNewNot]
      · exact hbehavior.2.2.2 u c hca hcb
  · exact hbehavior.1 u huQ

private theorem helper_continuation_404.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
      (eta : Fin k),
    (∀ (col : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
        c ∈ MissingColors G col (T.vertex i) →
          c ∈ MissingColors G col (T.vertex (HierarchyFirstMissingPosition col T c)) ∧
            (↑(HierarchyFirstMissingPosition col T c) : ℕ) ≤ (↑i : ℕ)) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    ∀ (hAT : TreeSequenceInitialSegment A T),
    ell = T.length - A.length →
    X.length = T.length - (1 : ℕ) →
    (↑D.penultimateVertexIndex : ℕ) = X.length →
    (↑D.lastEdgeIndex : ℕ) = X.length →
    X.length + (1 : ℕ) = T.length →
    X.length = A.length + (ell - (1 : ℕ)) →
    (1 : ℕ) ≤ ell - (1 : ℕ) →
    ell - (1 : ℕ) < ell →
    TreeSequenceInitialSegment X T →
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X →
    HierarchyFirstMissingPosition phi T eta = D.penultimateVertexIndex →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (a b : Fin k),
    a ≠ b →
    a ∈ TreeMissingColors P.coloring A →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) ≠ some a) →
    b ∈ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
    a ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∨
        b ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) →
    P.coloring (T.edge D.lastEdgeIndex) = some D.theta →
    D.theta ∉ MissingColors G P.coloring (T.vertex D.penultimateVertexIndex) →
    let J : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
      P.corresponding.replacementETT;
    let C' : HierarchyCounterexample P.replacementBase := P.counterexample;
    let col : PartialEdgeColoring E k := P.coloring;
    let H' : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
      C'.hierarchy;
    let q' : Fin (H'.dividerCount + (1 : ℕ)) := Fin.last H'.dividerCount;
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G col a b z;
    HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A ∧
        HierarchyFullTailLength P.counterexample = ell ∧
          HierarchyFullTailPrefix P.counterexample (ell - (1 : ℕ)) = X ∧
            HierarchyPathNumber P.counterexample.hierarchy = HierarchyPathNumber H →
    HierarchyStarredStage C'.hierarchy (Fin.last C'.hierarchy.dividerCount) = A →
    HierarchyStarredStage H' q' = A →
    HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - (1 : ℕ)) = X →
    IsProperEdgeColoring G col →
    ColoredVertexSetElementary G col (TreeSequenceVertexSet X) →
    HierarchyFirstMissingPosition col T b = D.penultimateVertexIndex →
    ∀ v ∈ TreeSequenceVertexSet A,
    ∀ (i : Fin (A.length + (1 : ℕ))),
    a ∈ MissingColors G col (T.vertex (HierarchyFirstMissingPosition col T a)) ∧
        (↑(HierarchyFirstMissingPosition col T a) : ℕ) ≤
          (↑(Fin.castLE (Nat.succ_le_succ hAT.1) i) : ℕ) →
    let va : V := T.vertex (HierarchyFirstMissingPosition col T a);
    let vb : V := T.vertex D.penultimateVertexIndex;
    let _ : V := T.vertex D.terminalVertexIndex;
    va ∈ TreeSequenceVertexSet X →
    (↑(HierarchyFirstMissingPosition col T a) : ℕ) < (↑D.penultimateVertexIndex : ℕ) →
    (0 : ℕ) < H'.dividerCount ∧
          a ∈
            TreeMissingColors col
              (H'.stage
                (⟨H'.dividerCount,
                    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega⟩ :
                  Fin (H'.dividerCount + (2 : ℕ)))) ∨
        H'.dividerCount = (0 : ℕ) ∧
          a ∈ TreeMissingColors col (J.series.data.tree (Fin.last J.rounds).castSucc) →
    a ∈
          TreeMissingColors col
            (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - (1 : ℕ))) ∧
        b ∈
          TreeMissingColors col
            (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - (1 : ℕ))) →
    ColoredVertexSetElementary G col
        (TreeSequenceVertexSet
          (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - (1 : ℕ)))) →
    TwoColorComponent G col a b (Sum.inl va) = TwoColorComponent G col a b (Sum.inl vb) →
    (∀ (w : V ⊕ E), w ∈ TwoColorComponent G col a b w) →
    (∀ (w : V),
        a ∈ MissingColors G col w ∨ b ∈ MissingColors G col w →
          ((TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl w)).Subsingleton) →
    ∃ (P' : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    P'.coloring =
        TwoColorComponentSwap G P.coloring a b (Sum.inl (T.vertex D.terminalVertexIndex)) ∧
      (∀ v ∈ TreeSequenceVertexSet X,
          MissingColors G P'.coloring v = MissingColors G P.coloring v) ∧
        ∀ (t : Fin T.length),
          A.length ≤ (↑t : ℕ) → P'.coloring (T.edge t) = P.coloring (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D eta firstMissing H q A ell X hAT hell
      hXlen hPenVal hLastVal hTlen hXexact hEllone hElllt hXT hyp hetaFirst P a b hne haA haTail
      hb hterminal htheta hthetaPresent J C' col H' q' z mu hg hstar hstar' hXeq hp hxElem
      hbFirst v hv i haFirst va vb vt hvaX horder hnorm hmissingP helemP hsame rootMem leaf
  have hdis := @helper_hdis_835 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@eta) (@hAT) (@hXlen)
      (@hPenVal) (@hLastVal) (@hTlen) (@hXexact) (@hetaFirst) (@P) (@a) (@b) (@hb) (@hterminal)
      (@hp) (@hbFirst) (@i) (@haFirst) (@horder) (@hsame) (@rootMem) (@leaf)
  have hpath : TwoColorPathComponent G col a b z :=
    ⟨hne, z, rootMem z, leaf vt hterminal⟩
  have hcase :
      (0 < H'.dividerCount ∧
        a ∈ TreeMissingColors col (H'.stage ⟨H'.dividerCount, by omega⟩)) ∨
      (H'.dividerCount = 0 ∧
        (a ∈ TreeMissingColors col (J.series.data.tree (Fin.last J.rounds).castSucc) ∨
          (a ∈ TreeMissingColors col
              (HierarchyStarredStage H' q') ∧
            a ∉ TashkinovStoredColors J.series.data (Fin.last J.rounds) ∧
            b ∉ TashkinovStoredColors J.series.data (Fin.last J.rounds)))) := by
    rcases hnorm with h | ⟨hq, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨hq, Or.inl ha⟩
  -- Obtain weak stability before protecting the possible SE/RE seed.
  have hstable := StableChangeCasesOneTwo G k e0 P.corresponding.replacementInput
    T col J P.replacementBase C' hp P.minimumContext.oneEdgeUncolored
    P.minimumContext.lowerRung P.minimumContext.fewerDividers
    P.minimumContext.lexicographicMinimality
    helemP
    P.minimumContext.largeMissingSet a b hne
    hmissingP
    z hpath mu rfl hcase hdis
  have hbehavior := TwoColorComponentSwapMissingBehavior G col a b hne hp z
  have edgeIn {u : V} {e : E}
      (hu : Sum.inl u ∈ TwoColorComponent G col a b z)
      (he : Incident G u e) (hc : col e = some a ∨ col e = some b) :
      Sum.inr e ∈ TwoColorComponent G col a b z := by
    have hadj : (TwoColorIncidenceGraph G col a b).Adj (Sum.inr e) (Sum.inl u) :=
      ⟨he, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hu
  have hprefix := @helper_hprefix_914 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hAT)
      (@hyp) (@P) (@a) (@b) (@hne) (@hb) (@hxElem) (@i) (@haFirst) (@hvaX) (@hsame) (@rootMem)
      (@hdis) (@hbehavior) (@edgeIn)
  let Tn := J.series.data.tree (Fin.last J.rounds).castSucc
  let Dn := TashkinovStoredColors J.series.data (Fin.last J.rounds)
  have stableTn : StableColoring Tn Dn col mu := by
    let baseStable := if J.series.data.kind (Fin.last J.rounds) =
        some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn P.replacementBase.closure Dn col mu
      else StableColoring Tn Dn col mu
    have extract : ∀ j : Fin (H'.dividerCount + 1),
        HierarchyWeaklyStable H' j mu → baseStable := by
      exact Fin.cases (motive := fun j => HierarchyWeaklyStable H' j mu → baseStable)
        (fun h => h) (fun i h => h.1)
    have hs := extract q' hstable.1
    by_cases hk : J.series.data.kind (Fin.last J.rounds) =
        some TashkinovExtensionKind.PE
    · have hs' : CombinedStableColoring Tn P.replacementBase.closure Dn col mu := by
        simpa [baseStable, hk] using hs
      exact hs'.1
    · simpa [baseStable, hk] using hs
  have lastX : X.vertex (Fin.last X.length) = T.vertex D.penultimateVertexIndex := by
    change T.vertex _ = T.vertex _
    apply congrArg T.vertex
    apply Fin.ext
    change X.length = D.penultimateVertexIndex.val
    exact hPenVal.symm
  have htailEdges : ∀ t : Fin T.length, A.length ≤ t.val →
      mu (T.edge t) = col (T.edge t) := by
    let replacementHierarchy := C'.hierarchy
    have starEqual : HierarchyStarredStage replacementHierarchy
        (Fin.last replacementHierarchy.dividerCount) = A := hstar'
    have tailPrefixEqual : HierarchyTailPrefix replacementHierarchy
        (T.length - (HierarchyStarredStage replacementHierarchy
          (Fin.last replacementHierarchy.dividerCount)).length - 1) = X := by
      change HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1) = X
      rw [hg.2.1]
      exact hg.2.2.1
    have fixed := replacementHierarchy.stableComponentSwapOnTail
      (alpha := a) (beta := b) (root := z)
      (by rw [starEqual]; exact hAT) helemP
      (by change 1 ≤ HierarchyFullTailLength C' - 1; rw [hg.2.1]; exact hEllone)
      D.lastEdgeIndex (by rw [tailPrefixEqual]; exact hLastVal)
      (by rw [tailPrefixEqual, lastX]; exact hb)
      (by
        intro colored
        have equal : D.theta = b := Option.some.inj (htheta.symm.trans colored)
        exact hthetaPresent (equal.symm ▸ hb)) stableTn
      (by intro t lower; exact haTail t (by simpa only [starEqual] using lower))
    exact fun t lower => fixed t (by simpa only [starEqual] using lower)
  exact @helper_continuation_834 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@eta)
      (@firstMissing) (@hAT) (@hXlen) (@hPenVal) (@hLastVal) (@hTlen) (@hXexact) (@hXT) (@hyp)
      (@hetaFirst) (@P) (@a) (@b) (@hne) (@haA) (@hb) (@hterminal) (@hstar) (@hstar') (@hXeq)
      (@hxElem) (@hbFirst) (@v) (@hv) (@i) (@haFirst) (@hvaX) (@horder) (@hmissingP) (@rootMem)
      (@hdis) (@hpath) (@hcase) (@hbehavior) (@hprefix) (@htailEdges)
private theorem helper_swapStep_439.{u_1, u_2} :
    helperSwapStep439Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D eta missingMono firstMissing H q A ell X
      hAT hell hXlen hPenVal hLastVal hTlen hXexact hEllone hElllt hXT hAX hyp hetaFirst
      presentationGeometry P a b hne haA haStage haTail hb hterminal htheta hthetaPresent
  let J := P.corresponding.replacementETT
  let C' := P.counterexample
  let col := P.coloring
  let H' := C'.hierarchy
  let q' := Fin.last H'.dividerCount
  let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
  let mu := TwoColorComponentSwap G col a b z
  have hg := presentationGeometry P
  have hstar : HierarchyStarredStage C'.hierarchy
      (Fin.last C'.hierarchy.dividerCount) = A := hg.1
  have hstar' : HierarchyStarredStage H' q' = A := hstar
  have hXeq : HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1) = X := by
    rw [hg.2.1]
    exact hg.2.2.1
  have hp : IsProperEdgeColoring G col := P.minimumContext.proper
  have hxElem : ColoredVertexSetElementary G col (TreeSequenceVertexSet X) := by
    have he : ColoredVertexSetElementary G col
        (TreeSequenceVertexSet (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1))) :=
      HierarchyCounterexamplePenultimateElementary G k e0
      P.corresponding.replacementInput T col J P.replacementBase C'
      P.minimumContext.proper P.minimumContext.oneEdgeUncolored
      P.minimumContext.lowerRung P.minimumContext.fewerDividers
      P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
    intro u hu v hv huv
    have hu' : u ∈ TreeSequenceVertexSet
        (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) := by
      rw [hXeq]
      exact hu
    have hv' : v ∈ TreeSequenceVertexSet
        (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) := by
      rw [hXeq]
      exact hv
    exact he hu' hv' huv
  have hbFirst : HierarchyFirstMissingPosition col T b =
      D.penultimateVertexIndex := by
    have hm := firstMissing col b D.penultimateVertexIndex hb
    have hv : T.vertex (HierarchyFirstMissingPosition col T b) ∈
        TreeSequenceVertexSet X := by
      apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      refine ⟨⟨(HierarchyFirstMissingPosition col T b).val, by
        rw [hXlen]
        have hpos := D.penultimateVertexPosition
        omega⟩, Finset.mem_univ _, ?_⟩
      rfl
    by_contra hi
    exact Finset.disjoint_left.mp
      (hxElem hv hyp (fun h => hi (T.vertex_injective h))) hm.1 hb
  obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp haA
  obtain ⟨i, _, hiv⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hv
  have hai : a ∈ MissingColors G col
      (T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) i)) := by
    rw [hAT.2.1 i, hiv]
    exact hav
  have haFirst := firstMissing col a _ hai
  have haBound : (HierarchyFirstMissingPosition col T a).val ≤ A.length :=
    le_trans haFirst.2 (Nat.le_of_lt_succ i.isLt)
  let va := T.vertex (HierarchyFirstMissingPosition col T a)
  let vb := T.vertex D.penultimateVertexIndex
  let vt := T.vertex D.terminalVertexIndex
  have hvaX : va ∈ TreeSequenceVertexSet X := by
    apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    refine ⟨⟨(HierarchyFirstMissingPosition col T a).val, by
      rw [hXlen]
      omega⟩, Finset.mem_univ _, ?_⟩
    rfl
  have horder : (HierarchyFirstMissingPosition col T a).val <
      D.penultimateVertexIndex.val := by
    have hp := D.penultimateVertexPosition
    omega
  have hnorm :
      (0 < H'.dividerCount ∧
        a ∈ TreeMissingColors col (H'.stage ⟨H'.dividerCount, by omega⟩)) ∨
      (H'.dividerCount = 0 ∧ a ∈ TreeMissingColors col
        (J.series.data.tree (Fin.last J.rounds).castSucc)) := by
    change a ∈ HierarchyStageMissingColors H' q' at haStage
    by_cases hq : H'.dividerCount = 0
    · right
      refine ⟨hq, ?_⟩
      have hi : q' = 0 := by apply Fin.ext; simp [q', hq]
      simpa [HierarchyStageMissingColors, hi] using haStage
    · left
      refine ⟨Nat.pos_of_ne_zero hq, ?_⟩
      have hi : q' =
          (⟨H'.dividerCount - 1, by omega⟩ : Fin H'.dividerCount).succ := by
        apply Fin.ext
        simp [q']
        omega
      have ha := haStage
      simp only [HierarchyStageMissingColors, hi, Fin.cases] at ha
      convert ha using 1
      apply congrArg (TreeMissingColors col)
      apply congrArg H'.stage
      apply Fin.ext
      simp
      omega
  have hmissing : a ∈ TreeMissingColors col X ∧ b ∈ TreeMissingColors col X :=
    ⟨missingMono hAX col haA, Finset.mem_biUnion.mpr ⟨vb, hyp, hb⟩⟩
  have hmissingP : a ∈ TreeMissingColors col
        (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) ∧
      b ∈ TreeMissingColors col
        (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1)) := by
    rw [hXeq]
    exact hmissing
  have helemP : ColoredVertexSetElementary G col
      (TreeSequenceVertexSet (HierarchyFullTailPrefix C' (HierarchyFullTailLength C' - 1))) := by
    rw [hXeq]
    exact hxElem
  have hchange := ChangeLemma G k e0 P.corresponding.replacementInput T col
    J P.replacementBase C' hp P.minimumContext.oneEdgeUncolored
    P.minimumContext.lowerRung P.minimumContext.fewerDividers
    P.minimumContext.lexicographicMinimality
    helemP
    P.minimumContext.largeMissingSet a b hne
    hmissingP
    (by
      dsimp only
      intro hcond
      refine ⟨⟨HierarchyFirstMissingPosition col T a,
        HierarchyFirstMissingPosition col T b, rfl, rfl, ?_⟩, ?_⟩
      · simpa [hbFirst] using horder
      · intro hc
        obtain ⟨t, ht, _, hcol⟩ := (Finset.mem_filter.mp hc).2
        exact haTail t (by simpa only [hstar] using ht) hcol)
  have hsame : TwoColorComponent G col a b (Sum.inl va) =
      TwoColorComponent G col a b (Sum.inl vb) := by
    rcases hnorm with ⟨hq, ha⟩ | ⟨hq, ha⟩
    · simpa [va, vb, hbFirst] using hchange.1 ⟨hq, Or.inl ha⟩
    · simpa [va, vb, hbFirst] using hchange.2.1 ⟨hq, Or.inl ha⟩
  have rootMem (w : Sum V E) : w ∈ TwoColorComponent G col a b w := by
    change (TwoColorIncidenceGraph G col a b).connectedComponentMk w = _
    rfl
  have leaf (w : V)
      (hm : a ∈ MissingColors G col w ∨ b ∈ MissingColors G col w) :
      ((TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl w)).Subsingleton := by
    have hd : @SimpleGraph.degree _ (TwoColorIncidenceGraph G col a b)
        (Sum.inl w) (Fintype.ofFinite _) ≤ 1 := by
      rcases hm with hm | hm
      · exact MissingColorIncidenceEndpoint G col a b hne hp w hm
      · have hs : TwoColorIncidenceGraph G col b a =
            TwoColorIncidenceGraph G col a b := by
          ext x y
          cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
        rw [← hs]
        exact MissingColorIncidenceEndpoint G col b a hne.symm hp w hm
    let : Fintype ((TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl w)) :=
      Fintype.ofFinite _
    have hc : Fintype.card
        ((TwoColorIncidenceGraph G col a b).neighborSet (Sum.inl w)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hd
    intro x hx y hy
    exact congrArg Subtype.val (Fintype.card_le_one_iff.mp hc ⟨x, hx⟩ ⟨y, hy⟩)
  exact @helper_continuation_404 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@eta)
      (@firstMissing) (@hAT) (@hell) (@hXlen) (@hPenVal) (@hLastVal) (@hTlen) (@hXexact)
      (@hEllone) (@hElllt) (@hXT) (@hyp) (@hetaFirst) (@P) (@a) (@b) (@hne) (@haA) (@haTail)
      (@hb) (@hterminal) (@htheta) (@hthetaPresent) (@hg) (@hstar) (@hstar') (@hXeq) (@hp)
      (@hxElem) (@hbFirst) (@v) (@hv) (@i) (@haFirst) (@hvaX) (@horder) (@hnorm) (@hmissingP)
      (@helemP) (@hsame) (@rootMem) (@leaf)
private theorem helper_branch_993.{u_1, u_2} :
    helperBranch993Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D eta hetaStored hetaMissing H q A ell X
      hAX hyp gamma hgammaA hgammaTail seriesProper seriesOne selfCorr P0 swapStep hlastTail
      storedPair reduceCaseOne P1 hprefix1 hedges1 hgammaTerminal
  have hetaPenultimate : eta ∈ MissingColors G P1.coloring
      (T.vertex D.penultimateVertexIndex) := by
    rw [hprefix1 _ hyp]
    exact hetaMissing
  have hgammaA1 : gamma ∈ TreeMissingColors P1.coloring A := by
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hgammaA
    exact Finset.mem_biUnion.mpr ⟨v, hv, by
      rw [hprefix1 v (TreeSequenceInitialSegmentVertexSetSubset hAX hv)]
      exact hc⟩
  have hgammaEta : gamma ≠ eta := by
    intro he
    exact (Finset.mem_sdiff.mp hetaStored).2 (he ▸ hgammaA)
  have hpair1 := storedPair P1
  have hgammaMem1 : gamma ∈ P1.counterexample.good.gamma
      (Fin.last P1.counterexample.hierarchy.dividerCount) eta := by
    rw [hpair1.2]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self gamma)
  have hstage1 := (Finset.mem_sdiff.mp
    (P1.counterexample.good.avoidance _ eta hpair1.1 hgammaMem1)).1
  have hgammaTail1 : ∀ t : Fin T.length, A.length ≤ t.val →
      P1.coloring (T.edge t) ≠ some gamma := by
    intro t ht
    rw [hedges1 t ht]
    exact hgammaTail t ht
  have htheta1 := (hedges1 _ hlastTail).trans D.thetaOnLastEdge
  have hthetaPresent1 : D.theta ∉ MissingColors G P1.coloring
      (T.vertex D.penultimateVertexIndex) := by
    rw [hprefix1 _ hyp]
    exact D.thetaPresentPenultimate
  obtain ⟨P2, hmu2, hprefix2, hedges2⟩ := swapStep P1 gamma eta hgammaEta
    hgammaA1 hstage1 hgammaTail1 hetaPenultimate (Or.inl hgammaTerminal)
    htheta1 hthetaPresent1
  have hetaTerminal2 : eta ∈ MissingColors G P2.coloring
      (T.vertex D.terminalVertexIndex) := by
    rw [hmu2]
    apply (TwoColorComponentSwapMissingBehavior G P1.coloring gamma eta
      hgammaEta P1.minimumContext.proper
      (Sum.inl (T.vertex D.terminalVertexIndex))).2.1
    · change (TwoColorIncidenceGraph G P1.coloring gamma eta).connectedComponentMk _ = _
      rfl
    · exact hgammaTerminal
  exact reduceCaseOne P2 (fun v hv => (hprefix2 v hv).trans (hprefix1 v hv))
    (fun t ht => (hedges2 t ht).trans (hedges1 t ht)) hetaTerminal2

private theorem helper_continuation_1279.{u_1, u_2} :
    helperContinuation1279Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D eta hetaStored hetaMissing H q A ell X
      htail hAX hyp gamma hthetaGamma hgammaAvoid hgammaA hgammaAlpha hgammaTail
      presentationGeometry seriesProper seriesOne selfCorr P0 swapStep hlastTail storedPair
  have reduceCaseOne
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hprefix : ∀ v ∈ TreeSequenceVertexSet X,
        MissingColors G P.coloring v = MissingColors G phi v)
      (hedges : ∀ t : Fin T.length, A.length ≤ t.val →
        P.coloring (T.edge t) = phi (T.edge t))
      (hterminal : eta ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex)) :
      False := by
    have hg := presentationGeometry P
    have hsp := storedPair P
    let D1 : HierarchySituationTwoCaseOneData G k e0 P.corresponding.replacementInput
        T P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample
        P.minimumContext := {
      tailAtLeastTwo := by simpa [hg.2.1] using htail
      pathNumberFull := hg.2.2.2.trans (D.pathNumberFull.trans hg.2.1.symm)
      lastEdgeIndex := D.lastEdgeIndex
      penultimateVertexIndex := D.penultimateVertexIndex
      terminalVertexIndex := D.terminalVertexIndex
      lastEdgePosition := D.lastEdgePosition
      penultimateVertexPosition := D.penultimateVertexPosition
      terminalVertexPosition := D.terminalVertexPosition
      lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
      theta := D.theta
      thetaOnLastEdge := (hedges _ hlastTail).trans D.thetaOnLastEdge
      thetaPresentPenultimate := by rw [hprefix _ hyp]; exact D.thetaPresentPenultimate
      alpha := eta
      gammaOne := D.theta
      gammaTwo := gamma
      alphaMissingPenultimate := by rw [hprefix _ hyp]; exact hetaMissing
      alphaMissingTerminal := hterminal
      alphaStored := hsp.1
      gammaPair := hsp.2
      gammaDistinct := hthetaGamma }
    exact HierarchySituationTwoSubcaseOneOne G k e0 P.corresponding.replacementInput
      T P.coloring P.corresponding.replacementETT P.replacementBase
      P.counterexample P.minimumContext D1
  obtain ⟨P1, hmu1, hprefix1, hedges1⟩ := swapStep P0 gamma D.alpha hgammaAlpha
    hgammaA hgammaAvoid.1 hgammaTail D.alphaMissingPenultimate
    (Or.inr D.alphaMissingTerminal) D.thetaOnLastEdge D.thetaPresentPenultimate
  have hgammaTerminal : gamma ∈ MissingColors G P1.coloring
      (T.vertex D.terminalVertexIndex) := by
    rw [hmu1]
    apply (TwoColorComponentSwapMissingBehavior G phi gamma D.alpha
      hgammaAlpha ctx.proper (Sum.inl (T.vertex D.terminalVertexIndex))).2.2.1
    · change (TwoColorIncidenceGraph G phi gamma D.alpha).connectedComponentMk _ = _
      rfl
    · exact D.alphaMissingTerminal
  by_cases hetaTerminal : eta ∈ MissingColors G P1.coloring (T.vertex D.terminalVertexIndex)
  · exact reduceCaseOne P1 hprefix1 hedges1 hetaTerminal
  · exact @helper_branch_993 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx D eta hetaStored hetaMissing hAX hyp gamma hgammaA hgammaTail
      seriesProper seriesOne swapStep hlastTail storedPair reduceCaseOne P1 hprefix1 hedges1
      hgammaTerminal

private theorem helper_continuation_1111.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
    ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount),
    eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
    (∀ {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          ∀ (col : PartialEdgeColoring E k),
            TreeMissingColors col X ⊆ TreeMissingColors col Y) →
    (∀ (col : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
        c ∈ MissingColors G col (T.vertex i) →
          c ∈ MissingColors G col (T.vertex (HierarchyFirstMissingPosition col T c)) ∧
            (↑(HierarchyFirstMissingPosition col T c) : ℕ) ≤ (↑i : ℕ)) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    ell = T.length - A.length →
    (2 : ℕ) ≤ ell →
    X.length = T.length - (1 : ℕ) →
    (↑D.penultimateVertexIndex : ℕ) = X.length →
    (↑D.lastEdgeIndex : ℕ) = X.length →
    X.length + (1 : ℕ) = T.length →
    X.length = A.length + (ell - (1 : ℕ)) →
    (1 : ℕ) ≤ ell - (1 : ℕ) →
    ell - (1 : ℕ) < ell →
    TreeSequenceInitialSegment X T →
    TreeSequenceInitialSegment A X →
    TreeSequenceInitialSegment A B →
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X →
    HierarchyFirstMissingPosition phi T eta = D.penultimateVertexIndex →
    ∀ (gamma : Fin k),
    D.theta ≠ gamma →
    C.good.gamma q eta = (insert D.theta ({ gamma } : Finset (Fin k)) : Finset (Fin k)) →
    gamma ∈ HierarchyStageMissingColors C.hierarchy q ∧
        gamma ∉ HierarchySegmentColors C.hierarchy q eta →
    gamma ∈ TreeMissingColors phi A →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D eta hetaStored hetaMissing missingMono
      firstMissing H q A ell B X hAT hell htail hXlen hPenVal hLastVal hTlen hXexact hEllone
      hElllt hXT hAX hAB hyp hetaFirst gamma hthetaGamma hpair hgammaAvoid hgammaA
  have halpha := HierarchySituationTwoCaseTwoExclusions
    G k e0 input T phi ett base C ctx D
  have hgammaAlpha : gamma ≠ D.alpha := by
    intro heq
    exact halpha.1 (heq ▸ missingMono hAB phi hgammaA)
  have hgammaTail := @helper_hgammaTail_297 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C ctx D eta hXlen hPenVal hLastVal hTlen hXexact
      hetaFirst gamma hthetaGamma hgammaAvoid
  have starCongr (n m : ℕ) (coreLeft coreRight : TreeSequence G e0)
      (stageLeft : Fin (n + 2) → TreeSequence G e0)
      (stageRight : Fin (m + 2) → TreeSequence G e0)
      (hnm : n = m) (hcore : coreLeft = coreRight)
      (hstage : HEq stageLeft stageRight) :
      Fin.cases (motive := fun _ => TreeSequence G e0) coreLeft
          (fun i : Fin n => stageLeft i.succ.castSucc) (Fin.last n) =
        Fin.cases (motive := fun _ => TreeSequence G e0) coreRight
          (fun i : Fin m => stageRight i.succ.castSucc) (Fin.last m) := by
    subst m
    have hs := eq_of_heq hstage
    simp [hcore, hs]
  have presentationGeometry
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) = A ∧
        HierarchyFullTailLength P.counterexample = ell ∧
        HierarchyFullTailPrefix P.counterexample (ell - 1) = X ∧
        HierarchyPathNumber P.counterexample.hierarchy = HierarchyPathNumber H := by
    have hs := P.sameGood.1
    have hstar : HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) = A :=
      (starCongr _ _ base.core P.replacementBase.core H.stage
        P.counterexample.hierarchy.stage hs.2.1 hs.1 hs.2.2.1).symm
    refine ⟨hstar, ?_, ?_, ?_⟩
    · change T.length - _ = ell
      rw [hstar]
      rfl
    · simp only [HierarchyFullTailPrefix, hstar]
      rfl
    · simp only [HierarchyPathNumber, hstar]
      rfl
  have seriesProper : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) := by
    intro j
    exact (ett.series.coloringProperties j).1
  have seriesOne : ∀ j : Fin (ett.rounds + 1),
      IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    intro j
    exact (ett.series.coloringProperties j).2
  let selfCorr : CorrespondingExtendedTashkinovTree G k e0 ett phi T := {
    replacementInput := input
    replacementSeries := ett.series
    replacementETT := ett
    rungAgreement := rfl
    seriesPresentation := HEq.rfl
    finalGeneratingColoring := ett.generatingColoring
    ladderTreesAgree := fun _ => rfl
    storedColorsAgree := fun _ => rfl
    connectingEdgesAgree := fun _ => rfl
    extensionKindsAgree := fun _ => rfl
    replacementProper := seriesProper
    replacementOneUncolored := seriesOne
    replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  let P0 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := phi
    corresponding := selfCorr
    maximum := C.maximum
    replacementBase := base
    counterexample := C
    sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
      rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
    minimumContext := ctx }
  have swapStep := @helper_swapStep_439 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T phi ett base C ctx D eta missingMono firstMissing hAT hell hXlen hPenVal
      hLastVal hTlen hXexact hEllone hElllt hXT hAX hyp hetaFirst presentationGeometry
  have hlastTail : A.length ≤ D.lastEdgeIndex.val := by
    have hp := D.lastEdgePosition
    omega
  have storedPair (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      eta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) ∧
        P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta =
          {D.theta, gamma} := by
    obtain ⟨hcount, hslots⟩ := P.sameGood.2
    have hs := hslots q
    have hi : Fin.cast (congrArg (fun n => n + 1) hcount) q =
        Fin.last P.counterexample.hierarchy.dividerCount := by
      apply Fin.ext
      exact hcount
    rw [hi] at hs
    exact ⟨hs.1 ▸ hetaStored, (hs.2 eta hetaStored).symm.trans hpair⟩
  exact @helper_continuation_1279 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@eta)
      (@hetaStored) (@hetaMissing) (@htail) (@hAX) (@hyp) (@gamma) (@hthetaGamma) (@hgammaAvoid)
      (@hgammaA) (@hgammaAlpha) (@hgammaTail) (@presentationGeometry) (@seriesProper)
      (@seriesOne) (@swapStep) (@hlastTail) (@storedPair)
theorem HierarchySituationTwoSubcaseTwoOneStoredException {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData
      G k e0 input T phi ett base C ctx)
    (eta : Fin k)
    (hetaStored : eta ∈ HierarchyStoredColorsAt C.hierarchy
      (Fin.last C.hierarchy.dividerCount))
    (hetaMissing :
      eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex))
    (hthetaPair :
      D.theta ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta) :
    False := by
  classical
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    refine ⟨le_trans hXY.1 hYZ.1, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
  have hierarchyGeometry := @SharedFacts.StoredExceptionTransport.hierarchyGeometry V E
      inferInstance inferInstance
      inferInstance inferInstance G k e0 T segmentTrans
  have missingMono {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (col : PartialEdgeColoring E k) :
      TreeMissingColors col X ⊆ TreeMissingColors col Y := by
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXY hv, hcv⟩
  have firstMissing (col : PartialEdgeColoring E k) (c : Fin k)
      (i : Fin (T.length + 1)) (hc : c ∈ MissingColors G col (T.vertex i)) :
      c ∈ MissingColors G col
          (T.vertex (HierarchyFirstMissingPosition col T c)) ∧
        (HierarchyFirstMissingPosition col T c).val ≤ i.val := by
    let S := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G col (T.vertex j)
    have hs : S.Nonempty := ⟨i, by simp [S, hc]⟩
    have heq : HierarchyFirstMissingPosition col T c = S.min' hs := by
      simp [HierarchyFirstMissingPosition, S, hs]
    rw [heq]
    exact ⟨(Finset.mem_filter.mp (Finset.min'_mem S hs)).2,
      Finset.min'_le S i (by simp [S, hc])⟩
  let H := C.hierarchy
  let q := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let X := HierarchyFullTailPrefix C (ell - 1)
  have hAT : TreeSequenceInitialSegment A T := (hierarchyGeometry H).1
  have hell : ell = T.length - A.length := rfl
  have htail : 2 ≤ ell := D.tailAtLeastTwo
  have hBlen : B.length = T.length - 2 := by
    change min (A.length + (ell - 2)) T.length = T.length - 2
    rw [hell]
    omega
  have hXlen : X.length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    rw [hell]
    omega
  have hPenVal : D.penultimateVertexIndex.val = X.length := by
    rw [hXlen]
    have hp := D.penultimateVertexPosition
    omega
  have hLastVal : D.lastEdgeIndex.val = X.length := by
    rw [hXlen]
    have hp := D.lastEdgePosition
    omega
  have hTlen : X.length + 1 = T.length := by
    rw [hXlen]
    have hp := T.positive
    omega
  have hXexact : X.length = A.length + (ell - 1) := by
    rw [hXlen]
    omega
  have hEllone : 1 ≤ ell - 1 := by omega
  have hElllt : ell - 1 < ell := by omega
  have hXT : TreeSequenceInitialSegment X T :=
    ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
  have hAX : TreeSequenceInitialSegment A X :=
    commonPrefix hAT hXT (by rw [hXlen]; omega)
  have hAB : TreeSequenceInitialSegment A B :=
    commonPrefix hAT
      ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
      (by rw [hBlen]; omega)
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet X) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hyp : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet X := by
    apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    refine ⟨Fin.last X.length, Finset.mem_univ _, ?_⟩
    change T.vertex _ = T.vertex _
    apply congrArg T.vertex
    apply Fin.ext
    change X.length = D.penultimateVertexIndex.val
    rw [hXlen]
    have hp := D.penultimateVertexPosition
    omega
  have uniquePenultimate (c : Fin k)
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      HierarchyFirstMissingPosition phi T c = D.penultimateVertexIndex := by
    have hm := firstMissing phi c D.penultimateVertexIndex hc
    have hv : T.vertex (HierarchyFirstMissingPosition phi T c) ∈
        TreeSequenceVertexSet X := by
      apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      refine ⟨⟨(HierarchyFirstMissingPosition phi T c).val, by
        have hp := D.penultimateVertexPosition
        rw [hXlen]
        omega⟩, Finset.mem_univ _, ?_⟩
      rfl
    by_contra hi
    have hn : T.vertex (HierarchyFirstMissingPosition phi T c) ≠
        T.vertex D.penultimateVertexIndex := fun h => hi (T.vertex_injective h)
    exact Finset.disjoint_left.mp (helem hv hyp hn) hm.1 hc
  have hetaFirst := uniquePenultimate eta hetaMissing
  have hcard : (C.good.gamma q eta).card = 2 :=
    C.good.twoColors q eta hetaStored
  obtain ⟨gamma, hgamma, hthetaGamma⟩ :
      ∃ gamma, gamma ∈ C.good.gamma q eta ∧ D.theta ≠ gamma := by
    by_contra hn
    push Not at hn
    have hsubset : C.good.gamma q eta ⊆ {D.theta} := by
      intro c hc
      simp only [Finset.mem_singleton]
      exact (hn c hc).symm
    have hle := Finset.card_le_card hsubset
    simp only [Finset.card_singleton] at hle
    omega
  have hpair : C.good.gamma q eta = {D.theta, gamma} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact hthetaPair
      · exact hgamma
    · simp [hthetaGamma, hcard]
  have hgammaAvoid := Finset.mem_sdiff.mp
    (C.good.avoidance q eta hetaStored hgamma)
  have hgammaA : gamma ∈ TreeMissingColors phi A := by
    by_cases hq : H.dividerCount = 0
    · have hz : q = 0 := by apply Fin.ext; simp [q, hq]
      have hm : gamma ∈ TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
        simpa [HierarchyStageMissingColors, hz] using hgammaAvoid.1
      exact missingMono (hierarchyGeometry H).2 phi hm
    · have hpos : 0 < H.dividerCount := Nat.pos_of_ne_zero hq
      have hi : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
        apply Fin.ext
        simp [q]
        omega
      simpa [A, HierarchyStarredStage, HierarchyStageMissingColors, hi]
        using hgammaAvoid.1
  exact @helper_continuation_1111 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@eta)
      (@hetaStored) (@hetaMissing) (@missingMono) (@firstMissing) (@hAT) (@hell) (@htail)
      (@hXlen) (@hPenVal) (@hLastVal) (@hTlen) (@hXexact) (@hEllone) (@hElllt) (@hXT) (@hAX)
      (@hAB) (@hyp) (@hetaFirst) (@gamma) (@hthetaGamma) (@hpair) (@hgammaAvoid) (@hgammaA)
end GoldbergSeymour

end
