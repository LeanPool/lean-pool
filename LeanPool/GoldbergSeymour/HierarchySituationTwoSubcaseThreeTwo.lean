/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.SecondSituationTransport

public import LeanPool.GoldbergSeymour.SharedFacts.FirstSubcaseTransport

public import LeanPool.GoldbergSeymour.TwoColorComponentColoringFacts


public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeTwoData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoSubcaseTwoOne
public import LeanPool.GoldbergSeymour.StableChangeCaseThree

/-!
# Hierarchy Situation Two Subcase Three Two

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperRecolor1219Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  TreeSequenceInitialSegment B T →
  ((0 : ℕ) < H.dividerCount →
    A =
     H.stage
      (⟨H.dividerCount, by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
       Fin (H.dividerCount + (2 : ℕ)))) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  Bshort.length + (2 : ℕ) = T.length →
  TreeSequenceInitialSegment Bshort T →
  TreeSequenceInitialSegment Bshort B →
  (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ c ∈ TreeMissingColors rho X,
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
       (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (v : V),
       a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
        ((TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl v)).Subsingleton) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (u v w : V),
       u ≠ w →
        v ≠ w →
         a ∈ MissingColors G rho u →
          b ∈ MissingColors G rho v →
           a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
            TwoColorComponent G rho a b (Sum.inl u) =
              TwoColorComponent G rho a b (Sum.inl v) →
             Disjoint (TwoColorComponent G rho a b (Sum.inl w))
              (TwoColorComponent G rho a b (Sum.inl u))) →
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
       ∀ (u v : V),
        u ∈ TreeSequenceVertexSet B →
         v ∈ TreeSequenceVertexSet B →
          a ∈ MissingColors G rho u →
           b ∈ MissingColors G rho v →
            Sum.inl u ∉ TwoColorComponent G rho a b z →
             Sum.inl v ∉ TwoColorComponent G rho a b z →
              ∀ w ∈ TreeSequenceVertexSet B,
               MissingColors G (TwoColorComponentSwap G rho a b z) w =
                MissingColors G rho w) →
  (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
     (∀ v ∈ TreeSequenceVertexSet B,
       MissingColors G sigma v = MissingColors G rho v) →
      c ∈ TreeMissingColors rho B →
       HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) →
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      c ≠ a →
       c ≠ b →
        HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
         HierarchyFirstMissingPosition rho T c) →
  ∀
   (seriesFacts :
    ∀ (j : Fin (ett.rounds + (1 : ℕ))),
     IsProperEdgeColoring G (ett.series.data.coloring j) ∧
      IsOneEdgeUncolored (ett.series.data.coloring j) e0),
  let corrRefl : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
   {
    replacementInput := input, replacementSeries := ett.series,
    replacementETT := ett, rungAgreement := rfl, seriesPresentation := HEq.rfl,
    finalGeneratingColoring := ett.generatingColoring,
    ladderTreesAgree := fun (x : Fin ett.rounds) ↦ rfl,
    storedColorsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    connectingEdgesAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    extensionKindsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    replacementProper := fun (j : Fin (ett.rounds + (1 : ℕ))) ↦
     (seriesFacts j).left,
    replacementOneUncolored := fun (j : Fin (ett.rounds + (1 : ℕ))) ↦
     (seriesFacts j).right,
    replacementStable := fun (x : Fin ett.rounds) ↦
     (⟨fun (x_1 : E)
        (_ : TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) x_1)
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
  let _ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
   {
    coloring := phi, corresponding := corrRefl, maximum := C.maximum,
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
                  (_ :
                   ett.series.data.kind (Fin.last ett.rounds) =
                    some TashkinovExtensionKind.PE) ↦
                 rfl⟩ :
                (ett.series.data.kind (Fin.last ett.rounds) =
                   some TashkinovExtensionKind.PE ↔
                  corrRefl.replacementETT.series.data.kind
                    (Fin.last corrRefl.replacementETT.rounds) =
                   some TashkinovExtensionKind.PE) ∧
                 (ett.series.data.kind (Fin.last ett.rounds) =
                   some TashkinovExtensionKind.PE →
                  base.closure = base.closure))⟩ :
              C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
               (ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.PE ↔
                 corrRefl.replacementETT.series.data.kind
                   (Fin.last corrRefl.replacementETT.rounds) =
                  some TashkinovExtensionKind.PE) ∧
                (ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.PE →
                 base.closure = base.closure))⟩ :
            C.hierarchy.stage ≍ C.hierarchy.stage ∧
             C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
              (ett.series.data.kind (Fin.last ett.rounds) =
                 some TashkinovExtensionKind.PE ↔
                corrRefl.replacementETT.series.data.kind
                  (Fin.last corrRefl.replacementETT.rounds) =
                 some TashkinovExtensionKind.PE) ∧
               (ett.series.data.kind (Fin.last ett.rounds) =
                 some TashkinovExtensionKind.PE →
                base.closure = base.closure))⟩ :
          C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
           C.hierarchy.stage ≍ C.hierarchy.stage ∧
            C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
             (ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE ↔
               corrRefl.replacementETT.series.data.kind
                 (Fin.last corrRefl.replacementETT.rounds) =
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
              corrRefl.replacementETT.series.data.kind
                (Fin.last corrRefl.replacementETT.rounds) =
               some TashkinovExtensionKind.PE) ∧
             (ett.series.data.kind (Fin.last ett.rounds) =
               some TashkinovExtensionKind.PE →
              base.closure = base.closure)),
       Exists.intro
        (by
         have := GoldbergSeymour.TreeSequence.positive T
         omega)
        fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) ↦
        (⟨rfl,
          fun (x_1 : Fin k) (_ : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) ↦
          rfl⟩ :
         HierarchyStoredColorsAt C.hierarchy x =
           HierarchyStoredColorsAt C.hierarchy
            (Fin.cast
             (by
              have :=
               GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
                corrRefl
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
                 corrRefl
               have := GoldbergSeymour.TreeSequence.positive T
               omega)
              x)
             eta)⟩ :
      SameHierarchyStages C.hierarchy C.hierarchy ∧
       ∃ (_ : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
        ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
         have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
          Fin.cast
           (by
            have :=
             GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
              corrRefl
            have := GoldbergSeymour.TreeSequence.positive T
            omega)
           j;
         HierarchyStoredColorsAt C.hierarchy j =
           HierarchyStoredColorsAt C.hierarchy j₂ ∧
          ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j,
           C.good.gamma j eta = C.good.gamma j₂ eta),
    minimumContext := ctx :
    HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
  ∀ beta ∈ TreeMissingColors phi A,
   (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
     beta ≠ D.alpha →
      (H.dividerCount = (0 : ℕ) →
        beta ∈
         TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
       ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        (∀ v ∈ TreeSequenceVertexSet B,
          MissingColors G P.coloring v = MissingColors G phi v) ∧
         beta ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∧
          ∀ (t : Fin T.length),
           A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) = phi (T.edge t)

private abbrev helperBranch1440Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  ∀
   (seriesFacts :
    ∀ (j : Fin (ett.rounds + (1 : ℕ))),
     IsProperEdgeColoring G (ett.series.data.coloring j) ∧
      IsOneEdgeUncolored (ett.series.data.coloring j) e0),
  let corrRefl : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
   {
    replacementInput := input, replacementSeries := ett.series, replacementETT := ett,
    rungAgreement := rfl, seriesPresentation := HEq.rfl,
    finalGeneratingColoring := ett.generatingColoring,
    ladderTreesAgree := fun (x : Fin ett.rounds) ↦ rfl,
    storedColorsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    connectingEdgesAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    extensionKindsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    replacementProper := fun (j : Fin (ett.rounds + (1 : ℕ))) ↦ (seriesFacts j).left,
    replacementOneUncolored := fun (j : Fin (ett.rounds + (1 : ℕ))) ↦ (seriesFacts j).right,
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
       fun (x_1 : V) (_ : x_1 ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc)) ↦
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
  let _ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
   {
    coloring := phi, corresponding := corrRefl, maximum := C.maximum, replacementBase := base,
    counterexample := C,
    sameGood :=
     (⟨(⟨rfl,
         (⟨by
           have := GoldbergSeymour.TreeSequence.positive T
           omega,
           (⟨HEq.rfl,
             (⟨HEq.rfl,
               (⟨Iff.rfl,
                 fun
                  (_ :
                   ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) ↦
                 rfl⟩ :
                (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                  corrRefl.replacementETT.series.data.kind
                    (Fin.last corrRefl.replacementETT.rounds) =
                   some TashkinovExtensionKind.PE) ∧
                 (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                  base.closure = base.closure))⟩ :
              C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                 corrRefl.replacementETT.series.data.kind
                   (Fin.last corrRefl.replacementETT.rounds) =
                  some TashkinovExtensionKind.PE) ∧
                (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                 base.closure = base.closure))⟩ :
            C.hierarchy.stage ≍ C.hierarchy.stage ∧
             C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
              (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                corrRefl.replacementETT.series.data.kind
                  (Fin.last corrRefl.replacementETT.rounds) =
                 some TashkinovExtensionKind.PE) ∧
               (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                base.closure = base.closure))⟩ :
          C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
           C.hierarchy.stage ≍ C.hierarchy.stage ∧
            C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
             (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
               corrRefl.replacementETT.series.data.kind
                 (Fin.last corrRefl.replacementETT.rounds) =
                some TashkinovExtensionKind.PE) ∧
              (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
               base.closure = base.closure))⟩ :
        base.core = base.core ∧
         C.hierarchy.dividerCount = C.hierarchy.dividerCount ∧
          C.hierarchy.stage ≍ C.hierarchy.stage ∧
           C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
            (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
              corrRefl.replacementETT.series.data.kind
                (Fin.last corrRefl.replacementETT.rounds) =
               some TashkinovExtensionKind.PE) ∧
             (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
              base.closure = base.closure)),
       Exists.intro
        (by
         have := GoldbergSeymour.TreeSequence.positive T
         omega)
        fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) ↦
        (⟨rfl, fun (x_1 : Fin k) (_ : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) ↦ rfl⟩ :
         HierarchyStoredColorsAt C.hierarchy x =
           HierarchyStoredColorsAt C.hierarchy
            (Fin.cast
             (by
              have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corrRefl
              have := GoldbergSeymour.TreeSequence.positive T
              omega)
             x) ∧
          ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
           C.good.gamma x eta =
            C.good.gamma
             (Fin.cast
              (by
               have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corrRefl
               have := GoldbergSeymour.TreeSequence.positive T
               omega)
              x)
             eta)⟩ :
      SameHierarchyStages C.hierarchy C.hierarchy ∧
       ∃ (_ : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
        ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
         have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
          Fin.cast
           (by
            have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corrRefl
            have := GoldbergSeymour.TreeSequence.positive T
            omega)
           j;
         HierarchyStoredColorsAt C.hierarchy j = HierarchyStoredColorsAt C.hierarchy j₂ ∧
          ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j,
           C.good.gamma j eta = C.good.gamma j₂ eta),
    minimumContext := ctx : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
  (∀ beta ∈ TreeMissingColors phi Bshort,
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
     beta ∉ HierarchyStoredColorsAt H q →
      (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
       (∀ eta ∈ HierarchyStoredColorsAt H q,
         beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
        ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
         (∀ v ∈ TreeSequenceVertexSet B,
           MissingColors G POne.coloring v = MissingColors G phi v) →
          beta ∈ MissingColors G POne.coloring (T.vertex D.terminalVertexIndex) →
           POne.coloring (T.edge D.lastEdgeIndex) = some D.theta →
            (∀ (t : Fin T.length),
              A.length ≤ (↑t : ℕ) → POne.coloring (T.edge t) = phi (T.edge t)) →
             (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → POne.coloring (T.edge t) ≠ some beta) →
              (POne.counterexample.hierarchy.dividerCount = (0 : ℕ) →
                beta ∈ TreeMissingColors POne.coloring A →
                 beta ∈
                   TreeMissingColors POne.coloring
                    (POne.corresponding.replacementETT.series.data.tree
                     (Fin.last POne.corresponding.replacementETT.rounds).castSucc) ∨
                  beta ∉
                    TashkinovStoredColors POne.corresponding.replacementETT.series.data
                     (Fin.last POne.corresponding.replacementETT.rounds) ∧
                   D.theta ∉
                    TashkinovStoredColors POne.corresponding.replacementETT.series.data
                     (Fin.last POne.corresponding.replacementETT.rounds)) →
               False) →
  (∀ (eta beta : Fin k),
    eta ∈ HierarchyStoredColorsAt H q →
     beta ∈ C.good.gamma q eta →
      (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
       eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort → False) →
  D.theta ∉ HierarchyStoredColorsAt H q →
  False

private abbrev helperBranch2793Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
  T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
     B) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    P.corresponding.replacementETT.series.data.tree
      (Fin.last P.corresponding.replacementETT.rounds).castSucc =
     ett.series.data.tree (Fin.last ett.rounds).castSucc) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
        eta) →
  (∀ {X Y F : TreeSequence G e0},
    TreeSequenceInitialSegment X F →
     TreeSequenceInitialSegment Y F →
      X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
  base.core.length ≤ A.length →
  (∀ (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
  (∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T rho)
    (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
     K.dividerCount = (0 : ℕ) →
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
       (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho
       sigma) →
  (∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T old)
    (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
     IsOneEdgeUncolored old e0 →
      IsOneEdgeUncolored new e0 →
       ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
         old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t)) →
  ∀ (beta : Fin k)
   (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  (∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) → POne.coloring (T.edge t) = phi (T.edge t)) →
  let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
  beta ≠ D.theta →
  let ib : Fin (T.length + (1 : ℕ)) :=
   HierarchyFirstMissingPosition phi T beta;
  T.vertex ib ∈ TreeSequenceVertexSet B →
  let rho : PartialEdgeColoring E k := POne.coloring;
  let ettOne :
   ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T
    POne.coloring :=
   POne.corresponding.replacementETT;
  let _ : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
   POne.replacementBase;
  let COne' : HierarchyCounterexample POne.replacementBase :=
   POne.counterexample;
  let _ :
   HierarchyMinimumCounterexampleContext G k e0
    POne.corresponding.replacementInput T POne.coloring
    POne.corresponding.replacementETT POne.replacementBase
    POne.counterexample :=
   POne.minimumContext;
  let HOne :
   TashkinovHierarchy POne.corresponding.replacementETT
    POne.replacementBase :=
   COne'.hierarchy;
  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) :=
   Fin.last HOne.dividerCount;
  ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
  D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) →
  beta ∈ MissingColors G rho (T.vertex ib) →
  HierarchyFirstMissingPosition rho T beta = ib →
  (∀ (t : Fin T.length),
    A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
  (beta ∈ TreeMissingColors phi A →
    (0 : ℕ) < HOne.dividerCount ∧
      beta ∈
       TreeMissingColors rho
        (HOne.stage
         (⟨HOne.dividerCount,
           by
           have := GoldbergSeymour.TreeSequence.positive T
           omega⟩ :
          Fin (HOne.dividerCount + (2 : ℕ)))) ∨
     HOne.dividerCount = (0 : ℕ) ∧
      (beta ∈
        TreeMissingColors rho
         (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) ∨
       beta ∈ TreeMissingColors rho A ∧
        beta ∉
          TashkinovStoredColors ettOne.series.data
           (Fin.last ettOne.rounds) ∧
         D.theta ∉
          TashkinovStoredColors ettOne.series.data
           (Fin.last ettOne.rounds))) →
  beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
  Disjoint
    (TwoColorComponent G rho beta D.theta
     (Sum.inl (T.vertex D.terminalVertexIndex)))
    (TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex ib))) →
  let muTwo : PartialEdgeColoring E k :=
   TwoColorComponentSwap G rho beta D.theta z;
  TwoColorPathComponent G rho beta D.theta z →
  (∀ w ∈ TreeSequenceVertexSet B,
    MissingColors G (TwoColorComponentSwap G rho beta D.theta z)
      w =
     MissingColors G rho w) →
  (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    HierarchyFirstMissingPosition muTwo T c =
     HierarchyFirstMissingPosition rho T c) →
  TashkinovAugmentationSequence rho B T →
  (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    beta ∈ POne.counterexample.good.gamma qOne c ∨
      D.theta ∈ POne.counterexample.good.gamma qOne c →
     (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤
      B.length) →
  beta ∈ TreeMissingColors phi A →
  ∃ (corrTwo :
   CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
   MaximumProperty corrTwo.replacementETT ∧
    ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo)
     (KTwo :
     TashkinovHierarchy corrTwo.replacementETT baseTwo)
     (goodTwo : GoodHierarchy KTwo),
     SameGoodHierarchy COne'.good goodTwo

private abbrev helperContinuation3031Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  ((0 : ℕ) < H.dividerCount →
    A =
     H.stage
      (⟨H.dividerCount, by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
       Fin (H.dividerCount + (2 : ℕ)))) →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
  T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  Bshort.length + (2 : ℕ) = T.length →
  TreeSequenceInitialSegment Bshort T →
  TreeSequenceInitialSegment Bshort B →
  Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
  (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ c ∈ TreeMissingColors rho X,
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
       (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (v : V),
       a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
        ((TwoColorIncidenceGraph G rho a b).neighborSet
          (Sum.inl v)).Subsingleton) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (u v w : V),
       u ≠ v →
        u ≠ w →
         v ≠ w →
          a ∈ MissingColors G rho u →
           b ∈ MissingColors G rho v →
            a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
             TwoColorComponent G rho a b (Sum.inl u) =
               TwoColorComponent G rho a b (Sum.inl v) →
              Disjoint (TwoColorComponent G rho a b (Sum.inl w))
               (TwoColorComponent G rho a b (Sum.inl u))) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (u v w : V),
       u ≠ w →
        v ≠ w →
         a ∈ MissingColors G rho u →
          b ∈ MissingColors G rho v →
           a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
            TwoColorComponent G rho a b (Sum.inl u) =
              TwoColorComponent G rho a b (Sum.inl v) →
             Disjoint (TwoColorComponent G rho a b (Sum.inl w))
              (TwoColorComponent G rho a b (Sum.inl u))) →
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
       ∀ (u v : V),
        u ∈ TreeSequenceVertexSet B →
         v ∈ TreeSequenceVertexSet B →
          a ∈ MissingColors G rho u →
           b ∈ MissingColors G rho v →
            Sum.inl u ∉ TwoColorComponent G rho a b z →
             Sum.inl v ∉ TwoColorComponent G rho a b z →
              ∀ w ∈ TreeSequenceVertexSet B,
               MissingColors G (TwoColorComponentSwap G rho a b z) w =
                MissingColors G rho w) →
  (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
     (∀ v ∈ TreeSequenceVertexSet B,
       MissingColors G sigma v = MissingColors G rho v) →
      c ∈ TreeMissingColors rho B →
       HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) →
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      c ≠ a →
       c ≠ b →
        HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
          c =
         HierarchyFirstMissingPosition rho T c) →
  ∀
   (seriesFacts :
    ∀ (j : Fin (ett.rounds + (1 : ℕ))),
     IsProperEdgeColoring G (ett.series.data.coloring j) ∧
      IsOneEdgeUncolored (ett.series.data.coloring j) e0),
  let corrRefl : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
   {
    replacementInput := input, replacementSeries := ett.series,
    replacementETT := ett, rungAgreement := rfl,
    seriesPresentation := HEq.rfl,
    finalGeneratingColoring := ett.generatingColoring,
    ladderTreesAgree := fun (x : Fin ett.rounds) ↦ rfl,
    storedColorsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    connectingEdgesAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    extensionKindsAgree := fun (x : Fin (ett.rounds + (1 : ℕ))) ↦ rfl,
    replacementProper := fun (j : Fin (ett.rounds + (1 : ℕ))) ↦
     (seriesFacts j).left,
    replacementOneUncolored := fun (j : Fin (ett.rounds + (1 : ℕ))) ↦
     (seriesFacts j).right,
    replacementStable := fun (x : Fin ett.rounds) ↦
     (⟨fun (x_1 : E)
        (x_2 :
         TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) x_1)
        (x_3 :
         ∃
          c ∈
           TreeMissingColors (ett.series.data.coloring x.succ)
             (ett.series.data.tree x.succ.castSucc) ∪
            TashkinovStoredColors ett.series.data x.succ,
          ett.series.data.coloring x.succ x_1 = some c) ↦
       rfl,
       fun (x_1 : V)
        (x_2 :
         x_1 ∈
          TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc)) ↦
       rfl⟩ :
      (∀ (f : E),
        TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) f →
         (∃
           c ∈
            TreeMissingColors (ett.series.data.coloring x.succ)
              (ett.series.data.tree x.succ.castSucc) ∪
             TashkinovStoredColors ett.series.data x.succ,
           ett.series.data.coloring x.succ f = some c) →
          ett.series.data.coloring x.succ f =
           ett.series.data.coloring x.succ f) ∧
       ∀
        v ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc),
        MissingColors G (ett.series.data.coloring x.succ) v =
         MissingColors G (ett.series.data.coloring x.succ) v) :
    CorrespondingExtendedTashkinovTree G k e0 ett phi T };
  False

private abbrev helperContinuation3998Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
  T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  TreeSequenceInitialSegment Bshort T →
  TreeSequenceInitialSegment Bshort B →
  Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
  (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ c ∈ TreeMissingColors rho X,
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
       (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
  (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
     (∀ v ∈ TreeSequenceVertexSet B,
       MissingColors G sigma v = MissingColors G rho v) →
      c ∈ TreeMissingColors rho B →
       HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
     B) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    P.corresponding.replacementETT.series.data.tree
      (Fin.last P.corresponding.replacementETT.rounds).castSucc =
     ett.series.data.tree (Fin.last ett.rounds).castSucc) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma
        (Fin.last P.counterexample.hierarchy.dividerCount) eta) →
  (∀ {X Y F : TreeSequence G e0},
    TreeSequenceInitialSegment X F →
     TreeSequenceInitialSegment Y F →
      X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
  base.core.length ≤ A.length →
  (∀ (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ (t : Fin T.length),
      (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
  (∀ {input' : PartialEdgeColoring E k}
    (rho sigma : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T rho)
    (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
     K.dividerCount = (0 : ℕ) →
      StableColoring
       (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
       (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho
       sigma) →
  (∀ {input' : PartialEdgeColoring E k}
    (old new : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T old)
    (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
     IsOneEdgeUncolored old e0 →
      IsOneEdgeUncolored new e0 →
       ∀
        (t :
         Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
         old
          ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t)) →
  ∀ beta ∉ HierarchyStoredColorsAt H q,
   (beta ∉ TreeMissingColors phi A →
     D.theta ∉ HierarchyStoredColorsAt H q) →
    (∀ eta ∈ HierarchyStoredColorsAt H q,
      beta ∈ C.good.gamma q eta →
       eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
     ∀
      (POne :
       HierarchyReplacementPresentation G k e0 input T phi ett base C
        ctx),
      POne.coloring (T.edge D.lastEdgeIndex) = some D.theta →
       (∀ (t : Fin T.length),
         A.length ≤ (↑t : ℕ) →
          POne.coloring (T.edge t) = phi (T.edge t)) →
        let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
        beta ≠ D.theta →
         let ib : Fin (T.length + (1 : ℕ)) :=
          HierarchyFirstMissingPosition phi T beta;
         T.vertex ib ∈ TreeSequenceVertexSet B →
          T.vertex D.penultimateVertexIndex ≠
            T.vertex D.terminalVertexIndex →
           TreeVertexOrder T (T.vertex ib)
             (T.vertex D.penultimateVertexIndex) →
            (∀ (rho : PartialEdgeColoring E k),
              ∀
               c ∈
                MissingColors G rho
                 (T.vertex (HierarchyFirstMissingPosition rho T c)),
               c ∉ TreeMissingColors rho A →
                A.length <
                 (↑(HierarchyFirstMissingPosition rho T c) : ℕ)) →
             let rho : PartialEdgeColoring E k := POne.coloring;
             let ettOne :
              ExtendedTashkinovTree G k e0
               POne.corresponding.replacementInput T POne.coloring :=
              POne.corresponding.replacementETT;
             let COne' : HierarchyCounterexample POne.replacementBase :=
              POne.counterexample;
             let ctxOne :
              HierarchyMinimumCounterexampleContext G k e0
               POne.corresponding.replacementInput T POne.coloring
               POne.corresponding.replacementETT POne.replacementBase
               POne.counterexample :=
              POne.minimumContext;
             let HOne :
              TashkinovHierarchy POne.corresponding.replacementETT
               POne.replacementBase :=
              COne'.hierarchy;
             let qOne : Fin (HOne.dividerCount + (1 : ℕ)) :=
              Fin.last HOne.dividerCount;
             (∀ v ∈ TreeSequenceVertexSet B,
               MissingColors G rho v = MissingColors G phi v) →
              ColoredVertexSetElementary G rho
                (TreeSequenceVertexSet B) →
               TreeMissingColors rho A = TreeMissingColors phi A →
                D.theta ∈
                  MissingColors G rho
                   (T.vertex D.penultimateVertexIndex) →
                 beta ∉
                   MissingColors G rho
                    (T.vertex D.penultimateVertexIndex) →
                  beta ∈
                    MissingColors G rho
                     (T.vertex D.terminalVertexIndex) →
                   beta ∈ MissingColors G rho (T.vertex ib) →
                    HierarchyFirstMissingPosition rho T beta = ib →
                     HierarchyFirstMissingPosition rho T D.theta =
                       D.penultimateVertexIndex →
                      (∀ (t : Fin T.length),
                        A.length ≤ (↑t : ℕ) →
                         rho (T.edge t) ≠ some beta) →
                       (beta ∈ TreeMissingColors phi A →
                         (0 : ℕ) < HOne.dividerCount ∧
                           beta ∈
                            TreeMissingColors rho
                             (HOne.stage
                              (⟨HOne.dividerCount, by omega⟩ :
                               Fin (HOne.dividerCount + (2 : ℕ)))) ∨
                          HOne.dividerCount = (0 : ℕ) ∧
                           (beta ∈
                             TreeMissingColors rho
                              (ettOne.series.data.tree
                               (Fin.last ettOne.rounds).castSucc) ∨
                            beta ∈ TreeMissingColors rho A ∧
                             beta ∉
                               TashkinovStoredColors ettOne.series.data
                                (Fin.last ettOne.rounds) ∧
                              D.theta ∉
                               TashkinovStoredColors ettOne.series.data
                                (Fin.last ettOne.rounds))) →
                        beta ∈ TreeMissingColors rho B ∧
                          D.theta ∈ TreeMissingColors rho B →
                         Disjoint
                           (TwoColorComponent G rho beta D.theta
                            (Sum.inl (T.vertex D.terminalVertexIndex)))
                           (TwoColorComponent G rho beta D.theta
                            (Sum.inl (T.vertex ib))) →
                          let muTwo : PartialEdgeColoring E k :=
                           TwoColorComponentSwap G rho beta D.theta z;
                          TwoColorPathComponent G rho beta D.theta z →
                           (∀ w ∈ TreeSequenceVertexSet B,
                             MissingColors G
                               (TwoColorComponentSwap G rho beta D.theta
                                z)
                               w =
                              MissingColors G rho w) →
                            (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
                              HierarchyFirstMissingPosition muTwo T c =
                               HierarchyFirstMissingPosition rho T c) →
                             False

private abbrev helperFinish3305Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (2 : ℕ) ≤ T.length - A.length →
  B.length + (1 : ℕ) = T.length →
  TreeSequenceInitialSegment B T →
  (H.dividerCount = (0 : ℕ) → A = base.core) →
  TreeSequenceInitialSegment A T →
  TreeSequenceInitialSegment A B →
  B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
  T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
  HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
     c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  Bshort.length + (2 : ℕ) = T.length →
  TreeSequenceInitialSegment Bshort T →
  TreeSequenceInitialSegment Bshort B →
  Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
  (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ c ∈ TreeMissingColors rho X,
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
       (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
    Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
  (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (v : V),
       a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
        ((TwoColorIncidenceGraph G rho a b).neighborSet
          (Sum.inl v)).Subsingleton) →
  (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ∀ (u v w : V),
       u ≠ v →
        u ≠ w →
         v ≠ w →
          a ∈ MissingColors G rho u →
           b ∈ MissingColors G rho v →
            a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
             TwoColorComponent G rho a b (Sum.inl u) =
               TwoColorComponent G rho a b (Sum.inl v) →
              Disjoint (TwoColorComponent G rho a b (Sum.inl w))
               (TwoColorComponent G rho a b (Sum.inl u))) →
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
       ∀ (u v : V),
        u ∈ TreeSequenceVertexSet B →
         v ∈ TreeSequenceVertexSet B →
          a ∈ MissingColors G rho u →
           b ∈ MissingColors G rho v →
            Sum.inl u ∉ TwoColorComponent G rho a b z →
             Sum.inl v ∉ TwoColorComponent G rho a b z →
              ∀ w ∈ TreeSequenceVertexSet B,
               MissingColors G (TwoColorComponentSwap G rho a b z) w =
                MissingColors G rho w) →
  (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
     (∀ v ∈ TreeSequenceVertexSet B,
       MissingColors G sigma v = MissingColors G rho v) →
      c ∈ TreeMissingColors rho B →
       HierarchyFirstMissingPosition sigma T c =
        HierarchyFirstMissingPosition rho T c) →
  (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k),
    a ≠ b →
     IsProperEdgeColoring G rho →
      c ≠ a →
       c ≠ b →
        HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T
          c =
         HierarchyFirstMissingPosition rho T c) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
     B) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    P.corresponding.replacementETT.series.data.tree
      (Fin.last P.corresponding.replacementETT.rounds).castSucc =
     ett.series.data.tree (Fin.last ett.rounds).castSucc) →
  (∀
    (P :
     HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma
        (Fin.last P.counterexample.hierarchy.dividerCount) eta) →
  (∀ {X Y F : TreeSequence G e0},
    TreeSequenceInitialSegment X F →
     TreeSequenceInitialSegment Y F →
      X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
  base.core.length ≤ A.length →
  (∀ (X : TreeSequence G e0),
    TreeSequenceInitialSegment X T →
     ∀ (t : Fin T.length),
      (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
  (∀ {input' : PartialEdgeColoring E k}
    (rho sigma : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T rho)
    (base' : HierarchyBase ett' rho)
    (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
     K.dividerCount = (0 : ℕ) →
      StableColoring
       (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
       (TashkinovStoredColors ett'.series.data
        (Fin.last ett'.rounds))
       rho sigma) →
  (∀ {input' : PartialEdgeColoring E k}
    (old new : PartialEdgeColoring E k)
    (ett' : ExtendedTashkinovTree G k e0 input' T old)
    (base' : HierarchyBase ett' old)
    (K : TashkinovHierarchy ett' base'),
    HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
     IsOneEdgeUncolored old e0 →
      IsOneEdgeUncolored new e0 →
       ∀
        (t :
         Fin
          (HierarchyStarredStage K
            (Fin.last K.dividerCount)).length),
        new
          ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge
           t) =
         old
          ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge
           t)) →
  ∀ beta ∈ TreeMissingColors phi Bshort,
   (∀ (t : Fin T.length),
     A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
     (beta ∉ TreeMissingColors phi A →
       D.theta ∉ HierarchyStoredColorsAt H q) →
      (∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta →
         eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
       ∀
        (POne :
         HierarchyReplacementPresentation G k e0 input T phi ett
          base C ctx),
        (∀ v ∈ TreeSequenceVertexSet B,
          MissingColors G POne.coloring v =
           MissingColors G phi v) →
         beta ∈
           MissingColors G POne.coloring
            (T.vertex D.terminalVertexIndex) →
          POne.coloring (T.edge D.lastEdgeIndex) = some D.theta →
           (∀ (t : Fin T.length),
             A.length ≤ (↑t : ℕ) →
              POne.coloring (T.edge t) = phi (T.edge t)) →
            (∀ (t : Fin T.length),
              A.length ≤ (↑t : ℕ) →
               POne.coloring (T.edge t) ≠ some beta) →
             (POne.counterexample.hierarchy.dividerCount =
                (0 : ℕ) →
               beta ∈ TreeMissingColors POne.coloring A →
                beta ∈
                  TreeMissingColors POne.coloring
                   (POne.corresponding.replacementETT.series.data.tree
                    (Fin.last
                      POne.corresponding.replacementETT.rounds).castSucc) ∨
                 beta ∉
                   TashkinovStoredColors
                    POne.corresponding.replacementETT.series.data
                    (Fin.last
                     POne.corresponding.replacementETT.rounds) ∧
                  D.theta ∉
                   TashkinovStoredColors
                    POne.corresponding.replacementETT.series.data
                    (Fin.last
                     POne.corresponding.replacementETT.rounds)) →
              False

private theorem helper_hBterminal_159.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hBlen hBT
  rw [← hBT.2.1 (Fin.last B.length)]
  congr 1
  apply Fin.ext
  have hp := D.penultimateVertexPosition
  simp only [Fin.val_castLE, Fin.val_last]
  omega

private theorem helper_hnotA_197.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    TreeSequenceInitialSegment A B →
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    ∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
    c ∉ TreeMissingColors phi A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hApositive hAzero hAT hAB
      hyB hElementary c hc ha
  rcases Finset.mem_biUnion.mp ha with ⟨v, hv, hvc⟩
  have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hv
  have hvne : v ≠ T.vertex D.penultimateVertexIndex := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, rfl⟩
    intro he
    have hi := T.vertex_injective ((hAT.2.1 i).trans he)
    have hp := D.penultimateVertexPosition
    have hib := i.isLt
    have hiv := congrArg Fin.val hi
    simp only [Fin.val_castLE] at hiv
    omega
  exact Finset.disjoint_left.mp (hElementary hvB hyB hvne) hvc hc

private theorem helper_hshortB_220.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    TreeSequenceInitialSegment Bshort B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hBlen Bshort hshortLen
  refine ⟨by omega, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rfl

private theorem helper_hterminalIncident_226.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D Bshort hshortLen
  obtain ⟨i, hi⟩ := T.attaches D.lastEdgeIndex
  have hj : D.lastEdgeIndex.succ = D.terminalVertexIndex := by
    apply Fin.ext
    have hl := D.lastEdgePosition
    have ht := D.terminalVertexPosition
    simp only [Fin.val_succ]
    omega
  change _ ∈ G.ends (T.edge D.lastEdgeIndex)
  rw [hi, hj]
  exact Sym2.mem_mk_left _ _

private theorem helper_hcoreLength_566.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (_ : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    base.core.length ≤ A.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A hApositive hAzero
  by_cases hz : H.dividerCount = 0
  · exact le_of_eq (congrArg TreeSequence.length (hAzero hz).symm)
  · rw [hApositive (Nat.pos_of_ne_zero hz)]
    have hm : Monotone (fun i : Fin (H.dividerCount + 2) => (H.stage i).length) :=
      Fin.monotone_iff_le_succ.mpr fun i => (H.nested i).1
    exact H.coreInsideFirst.1.trans (hm (show
      (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) ≤
        ⟨H.dividerCount, by omega⟩ from Nat.pos_of_ne_zero hz))

private theorem helper_hbetaTheta_660.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (2 : ℕ) ≤ T.length - A.length →
    ∀ (beta : Fin k),
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ≠ D.theta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A htail beta hbetaUnused he
  exact hbetaUnused D.lastEdgeIndex (by
    have hp := D.lastEdgePosition
    clear * - hp htail
    omega) (D.thetaOnLastEdge.trans (congrArg some he.symm))

private theorem helper_hby_672.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    ∀ (beta : Fin k),
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    T.vertex ib ≠ T.vertex D.penultimateVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D Bshort hshortLen beta ib hbFirst he
  have hi := congrArg Fin.val (T.vertex_injective he)
  have hp := D.penultimateVertexPosition
  have hb : ib.val ≤ Bshort.length := hbFirst.2
  clear * - hi hp hb hshortLen
  omega

private theorem helper_hbt_679.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    ∀ (beta : Fin k),
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    T.vertex ib ≠ T.vertex D.terminalVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D Bshort hshortLen beta ib hbFirst he
  have hi := congrArg Fin.val (T.vertex_injective he)
  have hp := D.terminalVertexPosition
  have hb : ib.val ≤ Bshort.length := hbFirst.2
  clear * - hi hp hb hshortLen
  omega

private theorem helper_hyt_686.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D he
  have hi := congrArg Fin.val (T.vertex_injective he)
  have hp := D.penultimateVertexPosition
  have ht := D.terminalVertexPosition
  clear * - hi hp ht
  omega

private theorem helper_hcaseOne_757.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    (POne.counterexample.hierarchy.dividerCount = (0 : ℕ) →
        beta ∈ TreeMissingColors POne.coloring A →
          beta ∈
              TreeMissingColors POne.coloring
                (POne.corresponding.replacementETT.series.data.tree
                  (Fin.last POne.corresponding.replacementETT.rounds).castSucc) ∨
            beta ∉
                TashkinovStoredColors POne.corresponding.replacementETT.series.data
                  (Fin.last POne.corresponding.replacementETT.rounds) ∧
              D.theta ∉
                TashkinovStoredColors POne.corresponding.replacementETT.series.data
                  (Fin.last POne.corresponding.replacementETT.rounds)) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let _ : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    TreeMissingColors rho A = TreeMissingColors phi A →
    beta ∈ TreeMissingColors phi A →
    (0 : ℕ) < HOne.dividerCount ∧
        beta ∈
          TreeMissingColors rho
            (HOne.stage
              (⟨HOne.dividerCount,
                  by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin (HOne.dividerCount + (2 : ℕ)))) ∨
      HOne.dividerCount = (0 : ℕ) ∧
        (beta ∈
            TreeMissingColors rho
              (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) ∨
          beta ∈ TreeMissingColors rho A ∧
            beta ∉ TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds) ∧
              D.theta ∉ TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A sameStar beta POne hzero rho ettOne
      COne' HOne qOne hmissingA hm
  have hcount : H.dividerCount = HOne.dividerCount := POne.sameGood.1.2.1
  by_cases hz : HOne.dividerCount = 0
  · refine Or.inr ⟨hz, ?_⟩
    have hmNew : beta ∈ TreeMissingColors rho A := hmissingA.symm ▸ hm
    rcases hzero hz hmNew with hn | hn
    · exact Or.inl hn
    · exact Or.inr ⟨hmNew, hn⟩
  · refine Or.inl ⟨Nat.pos_of_ne_zero hz, ?_⟩
    have hi : qOne =
        (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ :=
      Fin.ext (by simp only [qOne, Fin.val_last, Fin.val_succ]; omega)
    have hs := sameStar POne
    change HierarchyStarredStage HOne qOne = A at hs
    rw [hi] at hs
    have hind : (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ.castSucc =
        (⟨HOne.dividerCount, by omega⟩ : Fin (HOne.dividerCount + 2)) :=
      Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
    change HOne.stage _ = A at hs
    rw [hind] at hs
    rw [hs, hmissingA]
    exact hm

private theorem helper_hsameTwo_814.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    ∀ beta ∈ TreeMissingColors phi Bshort,
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    (∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    beta ∈ MissingColors G POne.coloring (T.vertex D.terminalVertexIndex) →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → POne.coloring (T.edge t) ≠ some beta) →
    (POne.counterexample.hierarchy.dividerCount = (0 : ℕ) →
        beta ∈ TreeMissingColors POne.coloring A →
          beta ∈
              TreeMissingColors POne.coloring
                (POne.corresponding.replacementETT.series.data.tree
                  (Fin.last POne.corresponding.replacementETT.rounds).castSucc) ∨
            beta ∉
                TashkinovStoredColors POne.corresponding.replacementETT.series.data
                  (Fin.last POne.corresponding.replacementETT.rounds) ∧
              D.theta ∉
                TashkinovStoredColors POne.corresponding.replacementETT.series.data
                  (Fin.last POne.corresponding.replacementETT.rounds)) →
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
    T.vertex ib ∈ TreeSequenceVertexSet B →
    T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
    T.vertex ib ≠ T.vertex D.terminalVertexIndex →
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let baseOne' : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
      POne.replacementBase;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    TreeMissingColors rho A = TreeMissingColors phi A →
    beta ∉ HierarchyStoredColorsAt HOne qOne →
    beta ∉ MissingColors G rho (T.vertex D.penultimateVertexIndex) →
    beta ∈ MissingColors G rho (T.vertex D.terminalVertexIndex) →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    (beta ∈ TreeMissingColors phi A →
        (0 : ℕ) < HOne.dividerCount ∧
            beta ∈
              TreeMissingColors rho
                (HOne.stage
                  (⟨HOne.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                    Fin (HOne.dividerCount + (2 : ℕ)))) ∨
          HOne.dividerCount = (0 : ℕ) ∧
            (beta ∈
                TreeMissingColors rho
                  (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) ∨
              beta ∈ TreeMissingColors rho A ∧
                beta ∉ TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds) ∧
                  D.theta ∉
                    TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds))) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    (let H : TashkinovHierarchy ettOne baseOne' := COne'.hierarchy;
      have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      have n : Fin (ettOne.rounds + (1 : ℕ)) := Fin.last ettOne.rounds;
      have A : TreeSequence G e0 := HierarchyStarredStage H q;
      have Tnq : TreeSequence G e0 :=
        H.stage
          (⟨H.dividerCount, by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin (H.dividerCount + (2 : ℕ)));
      have Tn : TreeSequence G e0 := ettOne.series.data.tree n.castSucc;
      have Dn : Finset (Fin k) := TashkinovStoredColors ettOne.series.data n;
      have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
      have va : V := T.vertex (HierarchyFirstMissingPosition rho T beta);
      have vb : V := T.vertex (HierarchyFirstMissingPosition rho T D.theta);
      have sameComponent : Prop :=
        TwoColorComponent G rho beta D.theta (Sum.inl va) =
          TwoColorComponent G rho beta D.theta (Sum.inl vb);
      ((0 : ℕ) < H.dividerCount ∧
            (beta ∈ TreeMissingColors rho Tnq ∨
              Disjoint (insert beta ({ D.theta } : Finset (Fin k)) : Finset (Fin k)) Dnq) →
          sameComponent) ∧
        (H.dividerCount = (0 : ℕ) ∧
              (beta ∈ TreeMissingColors rho Tn ∨
                Disjoint (insert beta ({ D.theta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
            sameComponent) ∧
          (beta ∈ TreeMissingColors rho A ∧
              TreeColorSetClosed G rho A ({ beta } : Finset (Fin k)) →
            sameComponent ∧ TreeInterchangeable G A rho beta D.theta)) →
    TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex ib)) =
      TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hnotA Bshort sameStar sameLast
      beta hbetaMissing hbetaUnused hbetaStored houtside hcutoff POne hterm hUnused hzero
      hbetaTheta ib hbFirst hibB hby hbt horder rho ettOne baseOne' COne' HOne qOne hmissingA
      hbetaStoredOne hgammaPenOne hgammaTermOne hgammaWitnessOne' hfirstGammaOne hfirstThetaOne
      hgammaUnusedOne hcaseOne hmissingPairOne hchangeOne
  rw [← hfirstGammaOne, ← hfirstThetaOne]
  by_cases hm : beta ∈ TreeMissingColors phi A
  · rcases hcaseOne hm with ⟨hp, hb⟩ | ⟨hz, hb⟩
    · exact hchangeOne.1 ⟨hp, Or.inl hb⟩
    · apply hchangeOne.2.1
      refine ⟨hz, ?_⟩
      rcases hb with hb | ⟨_, hbn, htn⟩
      · exact Or.inl hb
      · right
        rw [Finset.disjoint_left]
        intro c hc hd
        rcases Finset.mem_insert.mp hc with rfl | hc
        · exact hbn hd
        · exact htn (Finset.mem_singleton.mp hc ▸ hd)
  · have hnTheta : D.theta ∉ HierarchyStoredColorsAt HOne qOne := by
      rw [← (sameLast POne).1]
      exact houtside hm
    by_cases hz : HOne.dividerCount = 0
    · apply hchangeOne.2.1
      refine ⟨hz, Or.inr ?_⟩
      rw [Finset.disjoint_left]
      intro c hc hd
      rcases Finset.mem_insert.mp hc with rfl | hc
      · apply hbetaStoredOne
        refine Finset.mem_sdiff.mpr ⟨hd, ?_⟩
        rw [sameStar POne, hmissingA]
        exact hm
      · have he : c = D.theta := Finset.mem_singleton.mp hc
        subst c
        apply hnTheta
        refine Finset.mem_sdiff.mpr ⟨hd, ?_⟩
        rw [sameStar POne, hmissingA]
        exact hnotA (c := D.theta) D.thetaMissingPenultimate
    · apply hchangeOne.1
      refine ⟨Nat.pos_of_ne_zero hz, Or.inr ?_⟩
      rw [Finset.disjoint_left]
      intro c hc hd
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hbetaStoredOne hd
      · exact hnTheta (Finset.mem_singleton.mp hc ▸ hd)

private theorem helper_hstoredTwo_876.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
        ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
          (∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) →
            c ∈ TreeMissingColors rho B →
              HierarchyFirstMissingPosition sigma T c =
                HierarchyFirstMissingPosition rho T c) →
    (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k),
        a ≠ b →
          IsProperEdgeColoring G rho →
            c ≠ a →
              c ≠ b →
                HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
                  HierarchyFirstMissingPosition rho T c) →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    beta ≠ D.theta →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let _ :
      HierarchyMinimumCounterexampleContext G k e0 POne.corresponding.replacementInput T
        POne.coloring POne.corresponding.replacementETT POne.replacementBase
        POne.counterexample :=
      POne.minimumContext;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    beta ∉ HierarchyStoredColorsAt HOne qOne →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    (∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho beta D.theta z) w =
          MissingColors G rho w) →
    ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B firstPreserved firstUnaffected beta
      POne z hbetaTheta rho COne' ctxOne HOne qOne hElementaryOne hbetaStoredOne hmissingPairOne
      muTwo hmissingTwo c hc
  have hcb : c ≠ beta := fun he => hbetaStoredOne (he ▸ hc)
  by_cases hct : c = D.theta
  · exact hct.symm ▸
      firstPreserved rho muTwo D.theta hElementaryOne hmissingTwo hmissingPairOne.2
  · exact firstUnaffected z rho beta D.theta c hbetaTheta ctxOne.proper hcb hct

private theorem helper_hsuffix_885.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    rho (T.edge D.lastEdgeIndex) = some D.theta →
    TashkinovAugmentationSequence rho B T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D B hBlen hBT beta POne rho hmissingPairOne
      hthetaLastOne
  apply Relation.ReflTransGen.single
  refine ⟨hBlen.symm, hBT, D.theta, ?_, hmissingPairOne.2⟩
  have hi : Fin.cast hBlen (Fin.last B.length) = D.lastEdgeIndex :=
    Fin.ext (by
      have hl := D.lastEdgePosition
      simp only [Fin.val_cast, Fin.val_last]
      clear * - hBlen hl
      omega)
  rw [hi]
  exact hthetaLastOne

private theorem helper_hgammaCutoff_901.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    TreeSequenceInitialSegment Bshort T →
    TreeSequenceInitialSegment Bshort B →
    (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
        TreeSequenceInitialSegment X T →
          ∀ c ∈ TreeMissingColors rho X,
            c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
              (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
    (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
    (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
        ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
          (∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) →
            c ∈ TreeMissingColors rho B →
              HierarchyFirstMissingPosition sigma T c =
                HierarchyFirstMissingPosition rho T c) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    ∀ (beta : Fin k),
    (∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let rho : PartialEdgeColoring E k := POne.coloring;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    (∀ v ∈ TreeSequenceVertexSet B, MissingColors G rho v = MissingColors G phi v) →
    (↑(HierarchyFirstMissingPosition rho T D.theta) : ℕ) ≤ B.length →
    ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
    beta ∈ POne.counterexample.good.gamma qOne c ∨
        D.theta ∈ POne.counterexample.good.gamma qOne c →
    (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hElementary hnotA Bshort hshortT
      hshortB firstWitness missingSubset firstPreserved sameLast beta hcutoff POne rho COne' HOne
      qOne hmissingOne' hthetaBound c hc hpair
  have hcOld : c ∈ HierarchyStoredColorsAt H q :=
    Finset.subset_of_eq (sameLast POne).1.symm hc
  have hpairOld : beta ∈ C.good.gamma q c ∨ D.theta ∈ C.good.gamma q c :=
    ((sameLast POne).2 c hcOld).symm ▸ hpair
  rcases hpairOld with hb | ht
  · rcases hcutoff c hcOld hb with he | hm
    · exact he.symm ▸ hthetaBound
    · have hmB : c ∈ TreeMissingColors phi B := missingSubset (X := Bshort) (Y := B) phi hshortB hm
      exact (le_of_eq (congrArg Fin.val
        (firstPreserved phi rho c hElementary hmissingOne' hmB))).trans
          ((firstWitness phi Bshort hshortT c hm).2.trans hshortB.1)
  · exact False.elim (hnotA (c := D.theta) D.thetaMissingPenultimate
      ((GoodHierarchyReservedDisjoint C.good q).1 c hcOld ht))

private theorem helper_hfixedPrefix_1000.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let rho : PartialEdgeColoring E k := POne.coloring;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    (∀ (t : Fin T.length),
        A.length ≤ (↑t : ℕ) → (↑t : ℕ) < B.length → muTwo (T.edge t) = rho (T.edge t)) →
    (∀ (t : Fin A.length), muTwo (A.edge t) = rho (A.edge t)) →
    ∀ (t : Fin T.length),
    (↑t : ℕ) < B.length →
    muTwo (T.edge t) = rho (T.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hAT beta POne z rho muTwo
      hfixedTailTwo hfixedCore t ht
  by_cases ha : t.val < A.length
  · let ta : Fin A.length := ⟨t.val, ha⟩
    have he : Fin.castLE hAT.1 ta = t := Fin.ext rfl
    rw [← he, hAT.2.2 ta]
    exact hfixedCore ta
  · exact hfixedTailTwo t (Nat.le_of_not_gt ha) ht

private theorem helper_transportRoute_1009.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    TreeSequenceInitialSegment B T →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let rho : PartialEdgeColoring E k := POne.coloring;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    (∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho beta D.theta z) w =
          MissingColors G rho w) →
    beta ∈ TreeMissingColors phi A →
    (∀ (t : Fin T.length), (↑t : ℕ) < B.length → muTwo (T.edge t) = rho (T.edge t)) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence rho S B →
    TashkinovAugmentationSequence muTwo S B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBT commonPrefix beta POne
      z rho muTwo hmissingTwo hm hfixedPrefix S hs
  clear * - G T B rho muTwo hBT hfixedPrefix hmissingTwo commonPrefix hs
  unfold TashkinovAugmentationSequence at hs ⊢
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head X Y hstep htail ih =>
    have hYB := TashkinovAugmentationSequenceInitialSegment rho Y B htail
    obtain ⟨hlen, hXY, c, hedge, hm⟩ := hstep
    have hXB : TreeSequenceInitialSegment X B :=
      ⟨hXY.1.trans hYB.1,
        fun i => (hYB.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i),
        fun i => (hYB.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)⟩
    refine Relation.ReflTransGen.head ⟨hlen, hXY, c, ?_, ?_⟩ ih
    · let tY : Fin Y.length := Fin.cast hlen.symm (Fin.last X.length)
      let tB : Fin B.length := Fin.castLE hYB.1 tY
      have hf := hfixedPrefix (Fin.castLE hBT.1 tB) tB.isLt
      rw [hBT.2.2 tB, hYB.2.2 tY] at hf
      exact hf.trans hedge
    · obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hm
      exact Finset.mem_biUnion.mpr ⟨v, hv,
        (hmissingTwo v (TreeSequenceInitialSegmentVertexSetSubset hXB hv)).symm ▸ hvc⟩

private theorem helper_hrouteTwo_1032.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    base.core.length ≤ A.length →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let _ : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
      POne.replacementBase;
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence rho S B → TashkinovAugmentationSequence muTwo S B) →
    ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muTwo
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B ∨
      (ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨
          ettOne.series.data.kind (Fin.last ettOne.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = ({ f } : Finset E) ∧
            TreeSequenceAdjoinEdge
                (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f seed ∧
              TashkinovAugmentationSequence muTwo seed B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT commonPrefix
      hcoreLength beta POne z rho ettOne baseOne' muTwo transportRoute
  rcases P2813_T1_TerminalRoute G k e0 POne.corresponding.replacementInput T rho ettOne with
    ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, _, _, hseq⟩
  · have hTnB := commonPrefix ettOne.abovePenultimate hBT (by
      have hs := ettOne.strictAbovePenultimate
      clear * - hs hBlen
      omega)
    exact Or.inl ⟨hp, transportRoute _ (TashkinovAugmentationSequenceRestrict rho _ B T
      hseq hTnB hBT)⟩
  · have hseedT := TashkinovAugmentationSequenceInitialSegment rho seed T hseq
    have hTnCore : (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc).length ≤
        baseOne'.core.length := by
      have hnp : ettOne.series.data.kind (Fin.last ettOne.rounds) ≠
          some TashkinovExtensionKind.PE := by
        intro he
        rcases hp with he' | he' <;> rw [he'] at he <;> cases he
      rw [baseOne'.nonparallel hnp]
    have hcLen : baseOne'.core.length ≤ A.length := by
      rw [← POne.sameGood.1.1]
      exact hcoreLength
    have hsLen : seed.length ≤ B.length := by
      have hl := hseed.1
      change seed.length = (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc).length + 1
          at hl
      clear * - hl hTnCore hcLen htail hBlen
      omega
    have hseedB := commonPrefix hseedT hBT hsLen
    exact Or.inr ⟨hp, f, seed, hedges, hseed,
      transportRoute seed (TashkinovAugmentationSequenceRestrict rho seed B T hseq hseedB hBT)⟩

private theorem helper_branch_1087.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
          B) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    ∀ beta ∉ HierarchyStoredColorsAt H q,
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (∀ (rho : PartialEdgeColoring E k),
        ∀ c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)),
          c ∉ TreeMissingColors rho A →
            A.length < (↑(HierarchyFirstMissingPosition rho T c) : ℕ)) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let _ : HierarchyBase POne.corresponding.replacementETT POne.coloring :=
      POne.replacementBase;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let _ :
      HierarchyMinimumCounterexampleContext G k e0 POne.corresponding.replacementInput T
        POne.coloring POne.corresponding.replacementETT POne.replacementBase
        POne.counterexample :=
      POne.minimumContext;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    TreeMissingColors rho A = TreeMissingColors phi A →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    beta ∉ TreeMissingColors phi A →
    ∃ (corrTwo : CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
    MaximumProperty corrTwo.replacementETT ∧
      ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo) (KTwo :
        TashkinovHierarchy corrTwo.replacementETT baseTwo) (goodTwo : GoodHierarchy KTwo),
        SameGoodHierarchy COne'.good goodTwo := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hAT sameStar samePrefix sameLast
      beta hbetaStored houtside POne z hbetaTheta ib horder firstAfter rho ettOne baseOne' COne'
      ctxOne hElementaryOne hmissingA hgammaWitnessOne' hfirstGammaOne hfirstThetaOne
      hgammaUnusedOne hmissingPairOne muTwo hm
  have hnotAOne : beta ∉ TreeMissingColors rho A := by rw [hmissingA]; exact hm
  have ha := firstAfter rho beta (by rw [hfirstGammaOne]; exact hgammaWitnessOne') hnotAOne
  rw [hfirstGammaOne] at ha
  exact (StableChangeCaseThree G k e0 POne.corresponding.replacementInput T rho ettOne
    baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung ctxOne.fewerDividers
    ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
      rw [samePrefix POne]
      exact hElementaryOne)
    ctxOne.largeMissingSet beta D.theta hbetaTheta
    (by
      change beta ∈ TreeMissingColors rho
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
        D.theta ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
      rw [samePrefix POne]
      exact hmissingPairOne)
    z muTwo rfl
    (by
      rw [sameStar POne, hfirstGammaOne]
      intro u hu
      obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hu
      exact ⟨Fin.castLE (Nat.succ_le_succ hAT.1) i, ib, hAT.2.1 i, rfl,
        lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) ha⟩)
    (by rw [hfirstGammaOne, hfirstThetaOne]; exact horder)
    (by rw [← (sameLast POne).1]; exact ⟨hbetaStored, houtside hm⟩)
    (by
      rw [hfirstGammaOne]
      intro hc
      obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
      exact hgammaUnusedOne t (by clear * - ht ha; omega) he)).2.2.2.2

private theorem helper_hlastComponent_1122.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    let rho : PartialEdgeColoring E k := POne.coloring;
    rho (T.edge D.lastEdgeIndex) = some D.theta →
    Sum.inr (T.edge D.lastEdgeIndex) ∈ TwoColorComponent G rho beta D.theta z := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D hterminalIncident beta POne z rho
      hthetaLastOne
  have hadj : (TwoColorIncidenceGraph G rho beta D.theta).Adj
      (Sum.inr (T.edge D.lastEdgeIndex)) z := by
    exact ⟨hterminalIncident, Or.inr hthetaLastOne⟩
  change (TwoColorIncidenceGraph G rho beta D.theta).connectedComponentMk
    (Sum.inr (T.edge D.lastEdgeIndex)) = _
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj

private theorem helper_recolor_1219.{u_1, u_2} :
    helperRecolor1219Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBT hApositive hAT hAB
      hElementary Bshort hshortLen hshortT hshortB firstWitness self leaf separateAny
      prefixMissing firstPreserved firstUnaffected seriesFacts corrRefl PRefl beta hbetaA
      hbetaUnused hbetaStored hbetaAlpha hzeroBeta
  as_aux_lemma =>
    let ib := HierarchyFirstMissingPosition phi T beta
    let ia := HierarchyFirstMissingPosition phi T D.alpha
    have hb := firstWitness phi A hAT beta hbetaA
    have ha := firstWitness phi Bshort hshortT D.alpha D.alphaMissingTwoBefore
    have inPrefix (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
        T.vertex i ∈ TreeSequenceVertexSet B := by
      let j : Fin (B.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
      have hj : Fin.castLE (Nat.succ_le_succ hBT.1) j = i := Fin.ext rfl
      exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨j, Finset.mem_univ _, (hBT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
    have hibB := inPrefix ib (hb.2.trans hAB.1)
    have hiaB := inPrefix ia (ha.2.trans hshortB.1)
    have hbt : T.vertex ib ≠ T.vertex D.terminalVertexIndex := by
      intro he
      have hi := congrArg Fin.val (T.vertex_injective he)
      have hv : ib.val ≤ A.length := hb.2
      have ht := D.terminalVertexPosition
      clear * - hi hv ht htail
      omega
    have hat : T.vertex ia ≠ T.vertex D.terminalVertexIndex := by
      intro he
      have hi := congrArg Fin.val (T.vertex_injective he)
      have hv : ia.val ≤ Bshort.length := ha.2
      have ht := D.terminalVertexPosition
      clear * - hi hv ht hshortLen
      omega
    have hmissing : beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B :=
      ⟨Finset.mem_biUnion.mpr ⟨_, hibB, hb.1⟩,
        Finset.mem_biUnion.mpr ⟨_, hiaB, ha.1⟩⟩
    have hchange := ChangeLemma G k e0 input T phi ett base C ctx.proper
      ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers ctx.lexicographicMinimality
      hElementary ctx.largeMissingSet beta D.alpha hbetaAlpha hmissing
      (by
        dsimp only
        intro hn
        have hnAlpha : D.alpha ∉ TreeMissingColors phi A :=
          hn.resolve_left (not_not.mpr hbetaA)
        have hafter : A.length < ia.val := by
          by_contra hn
          have hi : ia.val ≤ A.length := Nat.le_of_not_gt hn
          let i : Fin (A.length + 1) := ⟨ia.val, Nat.lt_succ_of_le hi⟩
          have he : Fin.castLE (Nat.succ_le_succ hAT.1) i = ia := Fin.ext rfl
          apply hnAlpha
          refine Finset.mem_biUnion.mpr ⟨A.vertex i,
            (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
          rw [← hAT.2.1 i, he]
          exact ha.1
        refine ⟨⟨ib, ia, rfl, rfl, lt_of_le_of_lt hb.2 hafter⟩, ?_⟩
        intro hc
        obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
        exact hbetaUnused t ht he)
    have hcase :
        (0 < H.dividerCount ∧ beta ∈ TreeMissingColors phi
          (H.stage ⟨H.dividerCount, by omega⟩)) ∨
        (H.dividerCount = 0 ∧ beta ∈ TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
      by_cases hz : H.dividerCount = 0
      · exact Or.inr ⟨hz, hzeroBeta hz⟩
      · exact Or.inl ⟨Nat.pos_of_ne_zero hz, hApositive (Nat.pos_of_ne_zero hz) ▸ hbetaA⟩
    have hsame : TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
        TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ia)) := by
      rcases hcase with hp | hz
      · exact hchange.1 ⟨hp.1, Or.inl hp.2⟩
      · exact hchange.2.1 ⟨hz.1, Or.inl hz.2⟩
    let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
    let mu := TwoColorComponentSwap G phi beta D.alpha z
    have hdisjoint := separateAny phi beta D.alpha hbetaAlpha ctx.proper
      (T.vertex ib) (T.vertex ia) (T.vertex D.terminalVertexIndex)
      hbt hat hb.1 ha.1 (Or.inr D.alphaMissingTerminal) hsame
    have hpath : TwoColorPathComponent G phi beta D.alpha z :=
      ⟨hbetaAlpha, _, self phi beta D.alpha _,
        leaf phi beta D.alpha hbetaAlpha ctx.proper _ (Or.inr D.alphaMissingTerminal)⟩
    have hdu : Sum.inl (T.vertex ib) ∉ TwoColorComponent G phi beta D.alpha z := by
      intro hm
      exact Set.disjoint_left.mp hdisjoint hm (self phi beta D.alpha _)
    have hdv : Sum.inl (T.vertex ia) ∉ TwoColorComponent G phi beta D.alpha z := by
      intro hm
      apply Set.disjoint_left.mp hdisjoint hm
      rw [hsame]
      exact self phi beta D.alpha _
    have hmissingNew := prefixMissing z phi beta D.alpha hbetaAlpha ctx.proper
      hElementary _ _ hibB hiaB hb.1 ha.1 hdu hdv
    have hfixed : ∀ t : Fin T.length, A.length ≤ t.val →
        mu (T.edge t) = phi (T.edge t) := by
      intro t ht
      have hb := hbetaUnused t ht
      have ha := D.alphaUnusedOnFullTail t ht
      simp only [mu, TwoColorComponentSwap, hb, ha, ite_false, ite_self]
    have hstored : ∀ c ∈ HierarchyStoredColorsAt H q,
        HierarchyFirstMissingPosition mu T c = HierarchyFirstMissingPosition phi T c := by
      intro c hc
      have hcb : c ≠ beta := fun he => hbetaStored (he ▸ hc)
      by_cases hca : c = D.alpha
      · subst c
        exact firstPreserved phi mu D.alpha hElementary hmissingNew hmissing.2
      · exact firstUnaffected z phi beta D.alpha c hbetaAlpha ctx.proper hcb hca
    obtain ⟨corr, hmax, baseNew, K, good, hsameGood⟩ :=
      (StableChangeCasesOneTwoFullTail G k e0 input T phi ett base C ctx
        beta D.alpha hbetaAlpha hmissing z hpath mu rfl
        (by dsimp only; rcases hcase with hp | ⟨hz, hm⟩
            · exact Or.inl hp
            · exact Or.inr ⟨hz, Or.inl hm⟩)
        hdisjoint hfixed hmissingNew hstored).2.2.2.2
    have hterm : beta ∈ MissingColors G mu (T.vertex D.terminalVertexIndex) :=
      (TwoColorComponentSwapMissingBehavior G phi beta D.alpha hbetaAlpha ctx.proper z).2.2.1
        _ (self phi beta D.alpha _) D.alphaMissingTerminal
    let CNew : HierarchyCounterexample baseNew :=
      { positive := by rw [corr.rungAgreement]; exact C.positive
        hierarchy := K
        good := good
        maximum := hmax
        notElementary := by
          intro he
          have hv : T.vertex ib ∈ TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
          have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T := by simp
              [TreeSequenceVertexSet]
          exact Finset.disjoint_left.mp (he hv ht hbt)
            ((hmissingNew _ hibB).symm ▸ hb.1) hterm }
    obtain ⟨P, hP⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
      ett base C ctx PRefl mu corr baseNew CNew hsameGood
    exact ⟨P, hP.symm ▸ hmissingNew, hP.symm ▸ hterm, hP.symm ▸ hfixed⟩

private theorem helper_gammaReduction_1356.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    (∀ beta ∈ TreeMissingColors phi Bshort,
        (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
          beta ∉ HierarchyStoredColorsAt H q →
            (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
              (∀ eta ∈ HierarchyStoredColorsAt H q,
                  beta ∈ C.good.gamma q eta →
                    eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
                ∀
                  (POne :
                    HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                  (∀ v ∈ TreeSequenceVertexSet B,
                      MissingColors G POne.coloring v = MissingColors G phi v) →
                    beta ∈ MissingColors G POne.coloring (T.vertex D.terminalVertexIndex) →
                      POne.coloring (T.edge D.lastEdgeIndex) = some D.theta →
                        (∀ (t : Fin T.length),
                            A.length ≤ (↑t : ℕ) →
                              POne.coloring (T.edge t) = phi (T.edge t)) →
                          (∀ (t : Fin T.length),
                              A.length ≤ (↑t : ℕ) → POne.coloring (T.edge t) ≠ some beta) →
                            (POne.counterexample.hierarchy.dividerCount = (0 : ℕ) →
                                beta ∈ TreeMissingColors POne.coloring A →
                                  beta ∈
                                      TreeMissingColors POne.coloring
                                        (POne.corresponding.replacementETT.series.data.tree
                                          (Fin.last
                                              POne.corresponding.replacementETT.rounds).castSucc) ∨
                                    beta ∉
                                        TashkinovStoredColors
                                          POne.corresponding.replacementETT.series.data
                                          (Fin.last
                                            POne.corresponding.replacementETT.rounds) ∧
                                      D.theta ∉
                                        TashkinovStoredColors
                                          POne.corresponding.replacementETT.series.data
                                          (Fin.last
                                            POne.corresponding.replacementETT.rounds)) →
                              False) →
    (∀ beta ∈ TreeMissingColors phi A,
        (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
          beta ∉ HierarchyStoredColorsAt H q →
            beta ≠ D.alpha →
              (H.dividerCount = (0 : ℕ) →
                  beta ∈
                    TreeMissingColors phi
                      (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
                ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                  (∀ v ∈ TreeSequenceVertexSet B,
                      MissingColors G P.coloring v = MissingColors G phi v) ∧
                    beta ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∧
                      ∀ (t : Fin T.length),
                        A.length ≤ (↑t : ℕ) → P.coloring (T.edge t) = phi (T.edge t)) →
    ∀ (eta beta : Fin k),
    eta ∈ HierarchyStoredColorsAt H q →
    beta ∈ C.good.gamma q eta →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hApositive hAzero
      hAT Bshort hshortLen missingSubset sameTn commonPrefix finish recolor eta beta heta hbeta
      hUnused hposition
  as_aux_lemma =>
    have hbetaA := (GoodHierarchyReservedDisjoint C.good q).1 eta heta hbeta
    have hbetaStored : beta ∉ HierarchyStoredColorsAt H q := by
      intro hc
      exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2
        (Finset.mem_biUnion.mpr ⟨eta, heta, hbeta⟩) hc
    have hbetaAlpha : beta ≠ D.alpha := by
      intro he
      have haGamma : D.alpha ∈ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) :=
        Finset.mem_biUnion.mpr ⟨eta, heta, he ▸ hbeta⟩
      rcases D.normalizedAlternative with hp | hz | hs
      · exact hp.2.2 haGamma
      · exact hz.2.2 haGamma
      · exact hbetaStored (he.symm ▸ hs.1)
    have hzeroBeta (hz : H.dividerCount = 0) :
        beta ∈ TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
      have hi : q = 0 := Fin.ext (by simpa only [q, Fin.val_last, Fin.val_zero] using hz)
      have hm := (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hbeta)).1
      rw [hi] at hm
      exact hm
    obtain ⟨P, hprefix, hterm, hfixed⟩ :=
      recolor beta hbetaA hUnused hbetaStored hbetaAlpha hzeroBeta
    have hAS : TreeSequenceInitialSegment A Bshort :=
      ⟨by omega, hAT.2.1, hAT.2.2⟩
    apply finish beta (missingSubset phi hAS hbetaA) hUnused hbetaStored
      (fun hn => False.elim (hn hbetaA)) ?_ P hprefix hterm ?_ hfixed ?_ ?_
    · intro c hc hb
      have he : c = eta := by
        by_contra hne
        exact Finset.disjoint_left.mp (C.good.disjointPairs q c eta hc heta hne) hb hbeta
      exact he.symm ▸ hposition
    · exact (hfixed D.lastEdgeIndex (by
        have hl := D.lastEdgePosition
        clear * - hl htail
        omega)).trans D.thetaOnLastEdge
    · intro t ht
      rw [hfixed t ht]
      exact hUnused t ht
    · intro hz _
      left
      rw [sameTn P]
      have hm := hzeroBeta (P.sameGood.1.2.1.trans hz)
      obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hm
      have hTnB := commonPrefix ett.abovePenultimate hBT (by
        have hs := ett.strictAbovePenultimate
        clear * - hs hBlen
        omega)
      exact Finset.mem_biUnion.mpr ⟨v, hv,
        (hprefix v (TreeSequenceInitialSegmentVertexSetSubset hTnB hv)).symm ▸ hvc⟩

private theorem helper_branch_1413.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    (∀ (eta beta : Fin k),
        eta ∈ HierarchyStoredColorsAt H q →
          beta ∈ C.good.gamma q eta →
            (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
              eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort → False) →
    D.theta ∈ HierarchyStoredColorsAt H q →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A hfirstTheta hnotA Bshort hshortLen
      gammaReduction hthetaStored
  obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp
    (C.good.twoColors q D.theta hthetaStored)
  have hg : g1 ∈ C.good.gamma q D.theta := by rw [hpair]; simp
  have hgA := (GoodHierarchyReservedDisjoint C.good q).1 D.theta hthetaStored hg
  have hgTheta : g1 ≠ D.theta := by
    intro he
    exact hnotA (c := D.theta) D.thetaMissingPenultimate (he ▸ hgA)
  apply gammaReduction D.theta g1 hthetaStored hg ?_ (Or.inl rfl)
  intro t ht he
  by_cases hl : t = D.lastEdgeIndex
  · rw [hl, D.thetaOnLastEdge] at he
    exact hgTheta (Option.some.inj he).symm
  · have hav := (Finset.mem_sdiff.mp
      (C.good.avoidance q D.theta hthetaStored hg)).2
    apply hav
    unfold HierarchySegmentColors
    dsimp only
    have hend : H.stage q.succ = T := by
      convert H.terminalStage using 1
      congr 1
    rw [hend, hfirstTheta]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, ?_, he⟩
    have hp := D.penultimateVertexPosition
    have hlast := D.lastEdgePosition
    have hvne : t.val ≠ D.lastEdgeIndex.val := fun he => hl (Fin.ext he)
    have hv := t.isLt
    omega

private theorem helper_branch_1440.{u_1, u_2} :
    helperBranch1440Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hnotA Bshort seriesFacts corrRefl
      PRefl finish gammaReduction hthetaStored
  by_cases halphaStored : D.alpha ∈ HierarchyStoredColorsAt H q
  · obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp
      (C.good.twoColors q D.alpha halphaStored)
    have hg : g1 ∈ C.good.gamma q D.alpha := by rw [hpair]; simp
    apply gammaReduction D.alpha g1 halphaStored hg ?_ (Or.inr D.alphaMissingTwoBefore)
    have havoid : Disjoint (C.good.gamma q D.alpha)
        (Finset.univ.filter fun c =>
          ∃ t : Fin T.length, A.length ≤ t.val ∧ phi (T.edge t) = some c) := by
      rcases D.normalizedAlternative with hp | hz | hs
      · exact False.elim (hp.2.1 halphaStored)
      · exact False.elim (hz.2.1 (Finset.mem_sdiff.mp halphaStored).1)
      · exact hs.2
    intro t ht he
    exact Finset.disjoint_left.mp havoid hg
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, he⟩)
  · apply finish D.alpha D.alphaMissingTwoBefore D.alphaUnusedOnFullTail halphaStored
      (fun _ => hthetaStored) ?_ PRefl (fun _ _ => rfl) D.alphaMissingTerminal
      D.thetaOnLastEdge (fun _ _ => rfl) D.alphaUnusedOnFullTail ?_
    · intro eta heta ha
      have hGamma : D.alpha ∈ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) :=
        Finset.mem_biUnion.mpr ⟨eta, heta, ha⟩
      rcases D.normalizedAlternative with hp | hz | hs
      · exact False.elim (hp.2.2 hGamma)
      · exact False.elim (hz.2.2 hGamma)
      · exact False.elim (halphaStored hs.1)
    · intro hz _
      right
      have halphaRaw : D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
        rcases D.normalizedAlternative with hp | hzero | hs
        · have hpos := hp.1
          change 0 < H.dividerCount at hpos
          change H.dividerCount = 0 at hz
          omega
        · exact hzero.2.1
        · exact False.elim (halphaStored hs.1)
      have hthetaRaw : D.theta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
        intro hc
        exact hthetaStored (Finset.mem_sdiff.mpr
          ⟨hc, hnotA (c := D.theta) D.thetaMissingPenultimate⟩)
      exact ⟨halphaRaw, hthetaRaw⟩

private theorem helper_branch_2793.{u_1, u_2} :
    helperBranch2793Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hnotA sameStar samePrefix sameTn sameLast commonPrefix
      hcoreLength predecessorIncident seedStable weakEdges beta POne hfixed z hbetaTheta ib hibB
      rho ettOne baseOne' COne' ctxOne HOne qOne hElementaryOne hthetaPenOne hgammaWitnessOne'
      hfirstGammaOne hgammaUnusedOne hcaseOne hmissingPairOne hdisjointTwo muTwo hpathTwo
      hmissingTwo hstoredTwo hsuffix hgammaCutoff hm
  have hstableTwo := StableChangeCasesOneTwo G k e0 POne.corresponding.replacementInput T rho
    ettOne baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
    ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by
      change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
      rw [samePrefix POne]
      exact hElementaryOne)
    ctxOne.largeMissingSet beta D.theta hbetaTheta
    (by
      change beta ∈ TreeMissingColors rho
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
        D.theta ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
      rw [samePrefix POne]
      exact hmissingPairOne)
    z hpathTwo muTwo rfl
    (by dsimp only; rcases hcaseOne hm with hpos | ⟨hz, hb⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hz, by
            rcases hb with hb | ⟨hm, hn⟩
            · exact Or.inl hb
            · exact Or.inr ⟨by rw [sameStar POne]; exact hm, hn⟩⟩)
    (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
  have hthetaExclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
    ett base H hElementary (HierarchyFullTailLength C - 1)
    (by change 1 ≤ T.length - A.length - 1; clear * - htail; omega)
    (by change T.length - A.length - 1 < T.length - A.length; clear * - htail; omega)
    D.theta (by
      change D.theta ∈ MissingColors G phi (B.vertex (Fin.last B.length))
      rw [hBterminal]
      exact D.thetaMissingPenultimate)
  have hfixedTailTwo : ∀ t : Fin T.length, A.length ≤ t.val → t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    intro t ht hb
    have hng := hgammaUnusedOne t ht
    by_cases htheta : rho (T.edge t) = some D.theta
    · let tB : Fin B.length := ⟨t.val, hb⟩
      have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
      have heOld : phi (T.edge t) = some D.theta := by
        exact (hfixed t ht).symm.trans htheta
      have heB : phi (B.edge tB) = some D.theta := by
        rw [← hBT.2.2 tB, hcast]
        exact heOld
      obtain ⟨hz, hcore, hpos, f, _, _, _, _, _, hs⟩ :=
        hthetaExclusion tB ht (by
          change tB.val < A.length + (T.length - A.length - 1)
          have hv := tB.isLt
          clear * - hv htail hBlen
          change tB.val < B.length at hv
          omega) heB
      have hzOne : HOne.dividerCount = 0 := POne.sameGood.1.2.1.symm.trans hz
      have htn : ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc = A :=
        (sameTn POne).trans ((hAzero hz).trans hcore).symm
      have hinc : TreeIncidentEdge
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) (T.edge t) := by
        rw [htn]
        exact predecessorIncident A hAT t hpos
      have hsOld : D.theta ∈ HierarchyStoredColorsAt H q :=
        Finset.mem_sdiff.mpr ⟨hs, hnotA (c := D.theta) D.thetaMissingPenultimate⟩
      have hsOne : D.theta ∈ HierarchyStoredColorsAt HOne qOne :=
        (sameLast POne).1 ▸ hsOld
      exact (seedStable rho muTwo ettOne baseOne' HOne hstableTwo.1 hzOne).1 _ hinc
        ⟨D.theta, Finset.mem_union_right _ (Finset.mem_sdiff.mp hsOne).1, htheta⟩
    · simp only [muTwo, TwoColorComponentSwap, hng, htheta, ite_false, ite_self]
  have hfixedCore := weakEdges rho muTwo ettOne baseOne' HOne hstableTwo.1
    ctxOne.oneEdgeUncolored hstableTwo.2.1.2.1
  change ∀ t : Fin (HierarchyStarredStage POne.counterexample.hierarchy
    (Fin.last POne.counterexample.hierarchy.dividerCount)).length,
    muTwo ((HierarchyStarredStage POne.counterexample.hierarchy
      (Fin.last POne.counterexample.hierarchy.dividerCount)).edge t) =
    rho ((HierarchyStarredStage POne.counterexample.hierarchy
      (Fin.last POne.counterexample.hierarchy.dividerCount)).edge t) at hfixedCore
  rw [sameStar POne] at hfixedCore
  have hfixedPrefix : ∀ t : Fin T.length, t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    exact @helper_hfixedPrefix_1000 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hAT)
        (@beta) (@POne) (@hfixedTailTwo) (@hfixedCore)
  have transportRoute (S : TreeSequence G e0)
      (hs : TashkinovAugmentationSequence rho S B) :
      TashkinovAugmentationSequence muTwo S B := by
    exact @helper_transportRoute_1009 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBT) (@commonPrefix) (@beta) (@POne) (@hmissingTwo) (@hm) (@hfixedPrefix) (@S)
        (@hs)
  have hrouteTwo :
      (ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muTwo
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B) ∨
      ((ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨
          ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f
              seed ∧
          TashkinovAugmentationSequence muTwo seed B) := by
    exact @helper_hrouteTwo_1032 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBlen) (@hBT) (@commonPrefix) (@hcoreLength) (@beta) (@POne) (@transportRoute)
  exact (StableChangeCasesOneTwoSplitTail G k e0 POne.corresponding.replacementInput T rho
    ettOne baseOne' COne' ctxOne beta D.theta hbetaTheta
    (by rw [samePrefix POne]; exact hmissingPairOne)
    z hpathTwo muTwo rfl
    (by dsimp only; rcases hcaseOne hm with hpos | ⟨hz, hb⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hz, by
            rcases hb with hb | ⟨hm, hn⟩
            · exact Or.inl hb
            · exact Or.inr ⟨by rw [sameStar POne]; exact hm, hn⟩⟩)
    (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
    B (by dsimp only; rw [sameStar POne]; exact hAB)
    (by dsimp only; rw [sameStar POne]; clear * - htail hBlen; omega)
    (by rw [samePrefix POne]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
    (by dsimp only; intro t _ ht; exact hfixedPrefix t ht)
    hrouteTwo hsuffix
    ⟨Finset.mem_biUnion.mpr ⟨_, hibB, (hmissingTwo _ hibB).symm ▸ hgammaWitnessOne'⟩,
      Finset.mem_biUnion.mpr ⟨_, hyB, (hmissingTwo _ hyB).symm ▸ hthetaPenOne⟩⟩
    (by rw [samePrefix POne]; exact hmissingTwo) hstoredTwo hgammaCutoff).2.2

private theorem helper_continuation_3433.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    ((0 : ℕ) < H.dividerCount →
        A =
          H.stage
            (⟨H.dividerCount,
                have _ : (1 : ℕ) ≤ T.length := T.positive;
                Decidable.byContradiction
                  fun (a : ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦ by omega⟩ :
              Fin (H.dividerCount + (2 : ℕ)))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    TreeSequenceInitialSegment A B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    HierarchyFirstMissingPosition phi T D.theta = D.penultimateVertexIndex →
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    let Bshort : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
    Bshort.length + (2 : ℕ) = T.length →
    TreeSequenceInitialSegment Bshort T →
    TreeSequenceInitialSegment Bshort B →
    (∀ (rho : PartialEdgeColoring E k) (X : TreeSequence G e0),
        TreeSequenceInitialSegment X T →
          ∀ c ∈ TreeMissingColors rho X,
            c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
              (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ X.length) →
    (∀ (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V),
        Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v)) →
    (∀ (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0},
        TreeSequenceInitialSegment X Y →
          TreeMissingColors rho X ⊆ TreeMissingColors rho Y) →
    (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
        a ≠ b →
          IsProperEdgeColoring G rho →
            ∀ (v : V),
              a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v →
                ((TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl v)).Subsingleton) →
    (∀ (rho : PartialEdgeColoring E k) (a b : Fin k),
        a ≠ b →
          IsProperEdgeColoring G rho →
            ∀ (u v w : V),
              u ≠ w →
                v ≠ w →
                  a ∈ MissingColors G rho u →
                    b ∈ MissingColors G rho v →
                      a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w →
                        TwoColorComponent G rho a b (Sum.inl u) =
                            TwoColorComponent G rho a b (Sum.inl v) →
                          Disjoint (TwoColorComponent G rho a b (Sum.inl w))
                            (TwoColorComponent G rho a b (Sum.inl u))) →
    (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b : Fin k),
        a ≠ b →
          IsProperEdgeColoring G rho →
            ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
              ∀ (u v : V),
                u ∈ TreeSequenceVertexSet B →
                  v ∈ TreeSequenceVertexSet B →
                    a ∈ MissingColors G rho u →
                      b ∈ MissingColors G rho v →
                        Sum.inl u ∉ TwoColorComponent G rho a b z →
                          Sum.inl v ∉ TwoColorComponent G rho a b z →
                            ∀ w ∈ TreeSequenceVertexSet B,
                              MissingColors G (TwoColorComponentSwap G rho a b z) w =
                                MissingColors G rho w) →
    (∀ (rho sigma : PartialEdgeColoring E k) (c : Fin k),
        ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
          (∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v) →
            c ∈ TreeMissingColors rho B →
              HierarchyFirstMissingPosition sigma T c =
                HierarchyFirstMissingPosition rho T c) →
    (∀ (z : V ⊕ E) (rho : PartialEdgeColoring E k) (a b c : Fin k),
        a ≠ b →
          IsProperEdgeColoring G rho →
            c ≠ a →
              c ≠ b →
                HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
                  HierarchyFirstMissingPosition rho T c) →
    (∀ (j : Fin (ett.rounds + (1 : ℕ))),
        IsProperEdgeColoring G (ett.series.data.coloring j) ∧
          IsOneEdgeUncolored (ett.series.data.coloring j) e0) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    (∀ beta ∈ TreeMissingColors phi Bshort,
        (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
          beta ∉ HierarchyStoredColorsAt H q →
            (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
              (∀ eta ∈ HierarchyStoredColorsAt H q,
                  beta ∈ C.good.gamma q eta →
                    eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
                ∀
                  (POne :
                    HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                  (∀ v ∈ TreeSequenceVertexSet B,
                      MissingColors G POne.coloring v = MissingColors G phi v) →
                    beta ∈ MissingColors G POne.coloring (T.vertex D.terminalVertexIndex) →
                      POne.coloring (T.edge D.lastEdgeIndex) = some D.theta →
                        (∀ (t : Fin T.length),
                            A.length ≤ (↑t : ℕ) →
                              POne.coloring (T.edge t) = phi (T.edge t)) →
                          (∀ (t : Fin T.length),
                              A.length ≤ (↑t : ℕ) → POne.coloring (T.edge t) ≠ some beta) →
                            (POne.counterexample.hierarchy.dividerCount = (0 : ℕ) →
                                beta ∈ TreeMissingColors POne.coloring A →
                                  beta ∈
                                      TreeMissingColors POne.coloring
                                        (POne.corresponding.replacementETT.series.data.tree
                                          (Fin.last
                                              POne.corresponding.replacementETT.rounds).castSucc) ∨
                                    beta ∉
                                        TashkinovStoredColors
                                          POne.corresponding.replacementETT.series.data
                                          (Fin.last
                                            POne.corresponding.replacementETT.rounds) ∧
                                      D.theta ∉
                                        TashkinovStoredColors
                                          POne.corresponding.replacementETT.series.data
                                          (Fin.last
                                            POne.corresponding.replacementETT.rounds)) →
                              False) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hApositive hAzero
      hAT hAB hElementary hfirstTheta hnotA Bshort hshortLen hshortT hshortB firstWitness self
      missingSubset leaf separateAny prefixMissing firstPreserved firstUnaffected seriesFacts
      sameTn commonPrefix finish
  have recolor (beta : Fin k)
      (hbetaA : beta ∈ TreeMissingColors phi A)
      (hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
      (hbetaStored : beta ∉ HierarchyStoredColorsAt H q)
      (hbetaAlpha : beta ≠ D.alpha)
      (hzeroBeta : H.dividerCount = 0 →
        beta ∈ TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)) :
      ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
        (∀ v ∈ TreeSequenceVertexSet B,
          MissingColors G P.coloring v = MissingColors G phi v) ∧
        beta ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∧
        (∀ t : Fin T.length, A.length ≤ t.val →
          P.coloring (T.edge t) = phi (T.edge t)) := by
    exact @helper_recolor_1219 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@hBT)
        (@hApositive) (@hAT) (@hAB) (@hElementary) (@hshortLen) (@hshortT) (@hshortB)
        (@firstWitness) (@self) (@leaf) (@separateAny) (@prefixMissing) (@firstPreserved)
        (@firstUnaffected) (@seriesFacts) (@beta) (@hbetaA) (@hbetaUnused) (@hbetaStored)
        (@hbetaAlpha) (@hzeroBeta)
  -- Both stored-color branches use the same two swaps and compose their provenance.
  have gammaReduction (eta beta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H q)
      (hbeta : beta ∈ C.good.gamma q eta)
      (hUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
      (hposition : eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) : False := by
    exact @helper_gammaReduction_1356 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBlen) (@hBT) (@hApositive) (@hAzero) (@hAT) (@hshortLen) (@missingSubset)
        (@sameTn) (@commonPrefix) (@finish) (@recolor) (@eta) (@beta) (@heta) (@hbeta) (@hUnused)
        (@hposition)
  by_cases hthetaStored : D.theta ∈ HierarchyStoredColorsAt H q
  · exact @helper_branch_1413 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hfirstTheta)
      (@hnotA) (@hshortLen) (@gammaReduction) (@hthetaStored)
  · exact @helper_branch_1440 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hnotA)
      (@seriesFacts) (@finish) (@gammaReduction) (@hthetaStored)

private theorem helper_branch_3639.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (2 : ℕ) ≤ T.length - A.length →
    B.length + (1 : ℕ) = T.length →
    TreeSequenceInitialSegment B T →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment A T →
    TreeSequenceInitialSegment A B →
    B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex →
    T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) →
    (∀ {c : Fin k},
        c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) →
          c ∉ TreeMissingColors phi A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
          B) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    (∀ {X Y F : TreeSequence G e0},
        TreeSequenceInitialSegment X F →
          TreeSequenceInitialSegment Y F →
            X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
    base.core.length ≤ A.length →
    (∀ (X : TreeSequence G e0),
        TreeSequenceInitialSegment X T →
          ∀ (t : Fin T.length), (↑t : ℕ) = X.length → TreeIncidentEdge X (T.edge t)) →
    (∀ {input' : PartialEdgeColoring E k} (rho sigma : PartialEdgeColoring E k)
        (ett' : ExtendedTashkinovTree G k e0 input' T rho) (base' : HierarchyBase ett' rho)
        (K : TashkinovHierarchy ett' base'),
        HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma →
          K.dividerCount = (0 : ℕ) →
            StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
              (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma) →
    (∀ {input' : PartialEdgeColoring E k} (old new : PartialEdgeColoring E k)
        (ett' : ExtendedTashkinovTree G k e0 input' T old) (base' : HierarchyBase ett' old)
        (K : TashkinovHierarchy ett' base'),
        HierarchyWeaklyStable K (Fin.last K.dividerCount) new →
          IsOneEdgeUncolored old e0 →
            IsOneEdgeUncolored new e0 →
              ∀ (t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length),
                new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
                  old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t)) →
    ∀ (beta : Fin k)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    (∀ (t : Fin T.length),
        A.length ≤ (↑t : ℕ) → POne.coloring (T.edge t) = phi (T.edge t)) →
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    T.vertex ib ∈ TreeSequenceVertexSet B →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    let HOne : TashkinovHierarchy POne.corresponding.replacementETT POne.replacementBase :=
      COne'.hierarchy;
    let qOne : Fin (HOne.dividerCount + (1 : ℕ)) := Fin.last HOne.dividerCount;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    (beta ∈ TreeMissingColors phi A →
        (0 : ℕ) < HOne.dividerCount ∧
            beta ∈
              TreeMissingColors rho
                (HOne.stage
                  (⟨HOne.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                    Fin (HOne.dividerCount + (2 : ℕ)))) ∨
          HOne.dividerCount = (0 : ℕ) ∧
            (beta ∈
                TreeMissingColors rho
                  (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) ∨
              beta ∈ TreeMissingColors rho A ∧
                beta ∉ TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds) ∧
                  D.theta ∉
                    TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds))) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    Disjoint
        (TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex D.terminalVertexIndex)))
        (TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex ib))) →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    TwoColorPathComponent G rho beta D.theta z →
    (∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho beta D.theta z) w =
          MissingColors G rho w) →
    (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
        HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c) →
    TashkinovAugmentationSequence rho B T →
    (∀ c ∈ HierarchyStoredColorsAt HOne qOne,
        beta ∈ POne.counterexample.good.gamma qOne c ∨
            D.theta ∈ POne.counterexample.good.gamma qOne c →
          (↑(HierarchyFirstMissingPosition rho T c) : ℕ) ≤ B.length) →
    beta ∈ TreeMissingColors phi A →
    ∃ (corrTwo : CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
    MaximumProperty corrTwo.replacementETT ∧
      ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo) (KTwo :
        TashkinovHierarchy corrTwo.replacementETT baseTwo) (goodTwo : GoodHierarchy KTwo),
        SameGoodHierarchy COne'.good goodTwo := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hnotA sameStar samePrefix sameTn sameLast commonPrefix
      hcoreLength predecessorIncident seedStable weakEdges beta POne hfixed z hbetaTheta ib hibB
      rho ettOne COne' HOne qOne hElementaryOne hthetaPenOne hgammaWitnessOne' hfirstGammaOne
      hgammaUnusedOne hcaseOne hmissingPairOne hdisjointTwo muTwo hpathTwo hmissingTwo hstoredTwo
      hsuffix hgammaCutoff hm
  exact @helper_branch_2793 (@V) (@E) inferInstance inferInstance inferInstance
    inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
    (@htail) (@hBlen) (@hBT) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary)
    (@hnotA) (@sameStar) (@samePrefix) (@sameTn) (@sameLast) (@commonPrefix)
    (@hcoreLength) (@predecessorIncident) (@seedStable) (@weakEdges) (@beta) (@POne)
    (@hfixed) (@hbetaTheta) (@hibB) (@hElementaryOne) (@hthetaPenOne)
    (@hgammaWitnessOne') (@hfirstGammaOne) (@hgammaUnusedOne) (@hcaseOne)
    (@hmissingPairOne) (@hdisjointTwo) (@hpathTwo) (@hmissingTwo) (@hstoredTwo)
    (@hsuffix) (@hgammaCutoff) (@hm)

private theorem helper_branch_3648.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeTwoData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    TreeSequenceInitialSegment A T →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) =
          A) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix P.counterexample
            (HierarchyFullTailLength P.counterexample - (1 : ℕ)) =
          B) →
    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStoredColorsAt H q =
            HierarchyStoredColorsAt P.counterexample.hierarchy
              (Fin.last P.counterexample.hierarchy.dividerCount) ∧
          ∀ eta ∈ HierarchyStoredColorsAt H q,
            C.good.gamma q eta =
              P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)
                eta) →
    ∀ beta ∉ HierarchyStoredColorsAt H q,
    (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
    ∀ (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
    beta ≠ D.theta →
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
    (∀ (rho : PartialEdgeColoring E k),
        ∀ c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)),
          c ∉ TreeMissingColors rho A →
            A.length < (↑(HierarchyFirstMissingPosition rho T c) : ℕ)) →
    let rho : PartialEdgeColoring E k := POne.coloring;
    let ettOne :
      ExtendedTashkinovTree G k e0 POne.corresponding.replacementInput T POne.coloring :=
      POne.corresponding.replacementETT;
    let COne' : HierarchyCounterexample POne.replacementBase := POne.counterexample;
    ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) →
    TreeMissingColors rho A = TreeMissingColors phi A →
    beta ∈ MissingColors G rho (T.vertex ib) →
    HierarchyFirstMissingPosition rho T beta = ib →
    HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex →
    (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
    beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B →
    let muTwo : PartialEdgeColoring E k := TwoColorComponentSwap G rho beta D.theta z;
    beta ∉ TreeMissingColors phi A →
    ∃ (corrTwo : CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T),
    MaximumProperty corrTwo.replacementETT ∧
      ∃ (baseTwo : HierarchyBase corrTwo.replacementETT muTwo) (KTwo :
        TashkinovHierarchy corrTwo.replacementETT baseTwo) (goodTwo : GoodHierarchy KTwo),
        SameGoodHierarchy COne'.good goodTwo := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B hAT sameStar samePrefix sameLast
      beta hbetaStored houtside POne z hbetaTheta ib horder firstAfter rho ettOne COne'
      hElementaryOne hmissingA hgammaWitnessOne' hfirstGammaOne hfirstThetaOne hgammaUnusedOne
      hmissingPairOne muTwo hm
  exact @helper_branch_1087 (@V) (@E) inferInstance inferInstance inferInstance
    inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
    (@hAT) (@sameStar) (@samePrefix) (@sameLast) (@beta) (@hbetaStored) (@houtside)
    (@POne) (@hbetaTheta) (@horder) (@firstAfter) (@hElementaryOne) (@hmissingA)
    (@hgammaWitnessOne') (@hfirstGammaOne) (@hfirstThetaOne) (@hgammaUnusedOne)
    (@hmissingPairOne) (@hm)

private theorem helper_continuation_3998.{u_1, u_2} :
    helperContinuation3998Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hnotA Bshort hshortT hshortB hterminalIncident firstWitness self
      missingSubset firstPreserved sameStar samePrefix sameTn sameLast commonPrefix hcoreLength
      predecessorIncident seedStable weakEdges beta hbetaStored houtside hcutoff POne hlast
      hfixed z hbetaTheta ib hibB hyt horder firstAfter rho ettOne COne' ctxOne HOne qOne
      hmissingOne' hElementaryOne hmissingA hthetaPenOne hgammaPenOne hgammaTermOne
      hgammaWitnessOne' hfirstGammaOne hfirstThetaOne hgammaUnusedOne hcaseOne hmissingPairOne
      hdisjointTwo muTwo hpathTwo hmissingTwo hstoredTwo
  have hthetaLastOne : rho (T.edge D.lastEdgeIndex) = some D.theta := hlast
  have hsuffix : TashkinovAugmentationSequence rho B T := by
    exact @helper_hsuffix_885 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@beta) (@POne) (@hmissingPairOne) (@hthetaLastOne)
  have hthetaBound : (HierarchyFirstMissingPosition rho T D.theta).val ≤ B.length := by
    rw [hfirstThetaOne]
    have hp := D.penultimateVertexPosition
    clear * - hp hBlen
    omega
  have hgammaCutoff : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      (beta ∈ POne.counterexample.good.gamma qOne c ∨
        D.theta ∈ POne.counterexample.good.gamma qOne c) →
      (HierarchyFirstMissingPosition rho T c).val ≤ B.length := by
    exact @helper_hgammaCutoff_901 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hElementary) (@hnotA) (@hshortT) (@hshortB) (@firstWitness) (@missingSubset)
        (@firstPreserved) (@sameLast) (@beta) (@hcutoff) (@POne) (@hmissingOne') (@hthetaBound)
  obtain ⟨corrTwo, hmaxTwo, baseTwo, KTwo, goodTwo, hsameGoodTwo⟩ : ∃ corrTwo :
      CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T,
      MaximumProperty corrTwo.replacementETT ∧
        ∃ baseTwo : HierarchyBase corrTwo.replacementETT muTwo,
          ∃ KTwo : TashkinovHierarchy corrTwo.replacementETT baseTwo,
            ∃ goodTwo : GoodHierarchy KTwo, SameGoodHierarchy COne'.good goodTwo := by
    by_cases hm : beta ∈ TreeMissingColors phi A
    · exact @helper_branch_3639 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@hBlen)
        (@hBT) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary) (@hnotA) (@sameStar)
        (@samePrefix) (@sameTn) (@sameLast) (@commonPrefix) (@hcoreLength) (@predecessorIncident)
        (@seedStable) (@weakEdges) (@beta) (@POne) (@hfixed) (@hbetaTheta) (@hibB)
        (@hElementaryOne) (@hthetaPenOne) (@hgammaWitnessOne') (@hfirstGammaOne)
        (@hgammaUnusedOne) (@hcaseOne) (@hmissingPairOne) (@hdisjointTwo) (@hpathTwo)
        (@hmissingTwo) (@hstoredTwo) (@hsuffix) (@hgammaCutoff) (@hm)
    · exact @helper_branch_3648 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hAT) (@sameStar)
        (@samePrefix) (@sameLast) (@beta) (@hbetaStored) (@houtside) (@POne) (@hbetaTheta)
        (@horder) (@firstAfter) (@hElementaryOne) (@hmissingA) (@hgammaWitnessOne')
        (@hfirstGammaOne) (@hfirstThetaOne) (@hgammaUnusedOne) (@hmissingPairOne) (@hm)
  have hlastComponent : Sum.inr (T.edge D.lastEdgeIndex) ∈ TwoColorComponent G rho beta
      D.theta z := by
    exact @helper_hlastComponent_1122 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hterminalIncident) (@beta) (@POne) (@hthetaLastOne)
  have hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some beta := by
    simp [muTwo, TwoColorComponentSwap, hlastComponent, hthetaLastOne, hbetaTheta.symm]
  have hthetaTermTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.terminalVertexIndex) :=
    (TwoColorComponentSwapMissingBehavior G rho beta D.theta hbetaTheta ctxOne.proper z).2.1
      _ (self rho beta D.theta _) hgammaTermOne
  have hthetaPenTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingTwo _ hyB]
    exact hthetaPenOne
  have hgammaPenTwo : beta ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingTwo _ hyB]
    exact hgammaPenOne
  let CTwo : HierarchyCounterexample baseTwo :=
    { positive := by rw [corrTwo.rungAgreement]; exact COne'.positive
      hierarchy := KTwo
      good := goodTwo
      maximum := hmaxTwo
      notElementary := by
        intro he
        have hy : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet T := by simp
            [TreeSequenceVertexSet]
        have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T := by simp
            [TreeSequenceVertexSet]
        exact Finset.disjoint_left.mp (he hy ht hyt) hthetaPenTwo hthetaTermTwo }
  obtain ⟨PTwo, hPTwo⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx POne muTwo corrTwo baseTwo CTwo hsameGoodTwo
  let tailTwo : HierarchySituationTwoTailData G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext :=
    { tailAtLeastTwo := by
        change 2 ≤ T.length - (HierarchyStarredStage PTwo.counterexample.hierarchy
          (Fin.last PTwo.counterexample.hierarchy.dividerCount)).length
        rw [sameStar PTwo]
        exact htail
      pathNumberFull := by
        have hp := D.pathNumberFull
        unfold HierarchyPathNumber HierarchyFullTailLength at hp ⊢
        dsimp only at hp ⊢
        rw [sameStar PTwo]
        exact hp
      lastEdgeIndex := D.lastEdgeIndex
      penultimateVertexIndex := D.penultimateVertexIndex
      terminalVertexIndex := D.terminalVertexIndex
      lastEdgePosition := D.lastEdgePosition
      penultimateVertexPosition := D.penultimateVertexPosition
      terminalVertexPosition := D.terminalVertexPosition
      lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
      theta := beta
      thetaOnLastEdge := hPTwo.symm ▸ hlastTwo
      thetaPresentPenultimate := hPTwo.symm ▸ hgammaPenTwo }
  by_cases hstored : D.theta ∈ HierarchyStoredColorsAt PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount)
  · obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp
      (PTwo.counterexample.good.twoColors _ D.theta hstored)
    let finalData : HierarchySituationTwoCaseOneData G k e0
        PTwo.corresponding.replacementInput T
        PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
        PTwo.counterexample PTwo.minimumContext :=
      { toHierarchySituationTwoTailData := tailTwo
        alpha := D.theta
        gammaOne := g1
        gammaTwo := g2
        alphaMissingPenultimate := by
          change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.penultimateVertexIndex)
          rw [hPTwo]
          exact hthetaPenTwo
        alphaMissingTerminal := by
          change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.terminalVertexIndex)
          rw [hPTwo]
          exact hthetaTermTwo
        alphaStored := hstored
        gammaPair := hpair
        gammaDistinct := hne }
    exact HierarchySituationTwoSubcaseOneOne G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext finalData
  · let finalData : HierarchySituationTwoCaseTwoData G k e0
      PTwo.corresponding.replacementInput T
        PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
        PTwo.counterexample PTwo.minimumContext :=
      { toHierarchySituationTwoTailData := tailTwo
        alpha := D.theta
        alphaMissingPenultimate := by
          change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.penultimateVertexIndex)
          rw [hPTwo]
          exact hthetaPenTwo
        alphaMissingTerminal := by
          change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.terminalVertexIndex)
          rw [hPTwo]
          exact hthetaTermTwo
        alphaOutsideStored := hstored }
    exact HierarchySituationTwoSubcaseTwoOne G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext finalData

private theorem helper_finish_3305.{u_1, u_2} :
    helperFinish3305Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hAzero hAT hAB
      hBterminal hyB hElementary hfirstTheta hnotA Bshort hshortLen hshortT hshortB
      hterminalIncident firstWitness self missingSubset leaf separate prefixMissing
      firstPreserved firstUnaffected sameStar samePrefix sameTn sameLast commonPrefix hcoreLength
      predecessorIncident seedStable weakEdges beta hbetaMissing hbetaUnused hbetaStored houtside
      hcutoff POne hprefix hterm hlast hfixed hUnused hzero
  as_aux_lemma =>
    let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
    have hbetaTheta : beta ≠ D.theta := by
      exact @helper_hbetaTheta_660 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
          (@htail) (@beta) (@hbetaUnused)
    let ib := HierarchyFirstMissingPosition phi T beta
    have hbFirst := firstWitness phi Bshort hshortT beta hbetaMissing
    have hibB : T.vertex ib ∈ TreeSequenceVertexSet B := by
      let i : Fin (Bshort.length + 1) := ⟨ib.val, by have := hbFirst.2; omega⟩
      exact TreeSequenceInitialSegmentVertexSetSubset hshortB
        ((@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hby : T.vertex ib ≠ T.vertex D.penultimateVertexIndex := by
      exact @helper_hby_672 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hshortLen)
          (@beta) (@hbFirst)
    have hbt : T.vertex ib ≠ T.vertex D.terminalVertexIndex := by
      exact @helper_hbt_679 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hshortLen)
          (@beta) (@hbFirst)
    have hyt : T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
      exact @helper_hyt_686 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
    have horder : TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) :=
      ⟨ib, D.penultimateVertexIndex, rfl, rfl, by
        have hb : ib.val ≤ Bshort.length := hbFirst.2
        have hp := D.penultimateVertexPosition
        clear * - hb hp hshortLen
        omega⟩
    have firstAfter (rho : PartialEdgeColoring E k) (c : Fin k)
        (hc : c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)))
        (hn : c ∉ TreeMissingColors rho A) :
        A.length < (HierarchyFirstMissingPosition rho T c).val := by
      exact @SharedFacts.SecondSituationTransport.firstAfter (@V) (@E) inferInstance
          inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hAT) (@rho)
          (@c) (@hc) (@hn)
    let rho := POne.coloring
    let ettOne := POne.corresponding.replacementETT
    let baseOne' := POne.replacementBase
    let COne' := POne.counterexample
    let ctxOne := POne.minimumContext
    let HOne := COne'.hierarchy
    let qOne : Fin (HOne.dividerCount + 1) := Fin.last HOne.dividerCount
    have hmissingOne' : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G rho v = MissingColors G phi v := by
      exact hprefix
    have hElementaryOne : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) := by
      intro u hu v hv huv
      rw [hmissingOne' u hu, hmissingOne' v hv]
      exact hElementary hu hv huv
    have missingEq (X : TreeSequence G e0) (hXB : TreeSequenceInitialSegment X B) :
        TreeMissingColors rho X = TreeMissingColors phi X := by
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl (fun v hv =>
        hmissingOne' v (TreeSequenceInitialSegmentVertexSetSubset hXB hv))
    have hmissingA := missingEq A hAB
    have hbetaStoredOne : beta ∉ HierarchyStoredColorsAt HOne qOne := by
      rw [← (sameLast POne).1]
      exact hbetaStored
    have hthetaPenOne : D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
      rw [hmissingOne' _ hyB]
      exact D.thetaMissingPenultimate
    have hgammaPenOne : beta ∉ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
      rw [hmissingOne' _ hyB]
      intro hm
      exact Finset.disjoint_left.mp (hElementary hibB hyB hby) hbFirst.1 hm
    have hgammaTermOne : beta ∈ MissingColors G rho (T.vertex D.terminalVertexIndex) := by
      exact hterm
    have hgammaWitnessOne' : beta ∈ MissingColors G rho (T.vertex ib) := by
      rw [hmissingOne' _ hibB]
      exact hbFirst.1
    have hfirstGammaOne : HierarchyFirstMissingPosition rho T beta = ib :=
      firstPreserved phi rho beta hElementary hmissingOne'
        (Finset.mem_biUnion.mpr ⟨_, hibB, hbFirst.1⟩)
    have hfirstThetaOne : HierarchyFirstMissingPosition rho T D.theta =
        D.penultimateVertexIndex :=
      (firstPreserved phi rho D.theta hElementary hmissingOne'
        (Finset.mem_biUnion.mpr ⟨_, hyB, D.thetaMissingPenultimate⟩)).trans hfirstTheta
    have hgammaUnusedOne : ∀ t : Fin T.length, A.length ≤ t.val →
        rho (T.edge t) ≠ some beta := by
      exact hUnused
    have hcaseOne (hm : beta ∈ TreeMissingColors phi A) :
        (0 < HOne.dividerCount ∧ beta ∈ TreeMissingColors rho
          (HOne.stage ⟨HOne.dividerCount, by omega⟩)) ∨
        (HOne.dividerCount = 0 ∧
          (beta ∈ TreeMissingColors rho
            (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) ∨
          (beta ∈ TreeMissingColors rho A ∧
            beta ∉ TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds) ∧
            D.theta ∉ TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds)))) := by
      exact @helper_hcaseOne_757 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
          (@sameStar) (@beta) (@POne) (@hzero) (@hmissingA) (@hm)
    have hmissingPairOne : beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B :=
      ⟨Finset.mem_biUnion.mpr ⟨_, hibB, hgammaWitnessOne'⟩,
        Finset.mem_biUnion.mpr ⟨_, hyB, hthetaPenOne⟩⟩
    have hchangeOne := ChangeLemma G k e0 POne.corresponding.replacementInput T rho ettOne
      baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
      ctxOne.fewerDividers ctxOne.lexicographicMinimality
      (by
        change ColoredVertexSetElementary G rho
          (TreeSequenceVertexSet (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne'
              - 1)))
        rw [samePrefix POne]
        exact hElementaryOne)
      ctxOne.largeMissingSet beta D.theta hbetaTheta
      (by
        change beta ∈ TreeMissingColors rho
          (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
          D.theta ∈ TreeMissingColors rho
            (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
        rw [samePrefix POne]
        exact hmissingPairOne)
      (by
        dsimp only
        rw [sameStar POne, hfirstGammaOne, hfirstThetaOne]
        intro _
        refine ⟨horder, ?_⟩
        intro hc
        obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
        exact hgammaUnusedOne t ht he)
    have hsameTwo : TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex ib)) =
        TwoColorComponent G rho beta D.theta
          (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
      exact @helper_hsameTwo_814 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
          (@hnotA) (@sameStar) (@sameLast) (@beta) (@hbetaMissing) (@hbetaUnused) (@hbetaStored)
          (@houtside) (@hcutoff) (@POne) (@hterm) (@hUnused) (@hzero) (@hbetaTheta) (@hbFirst)
          (@hibB) (@hby) (@hbt) (@horder) (@hmissingA) (@hbetaStoredOne) (@hgammaPenOne)
          (@hgammaTermOne) (@hgammaWitnessOne') (@hfirstGammaOne) (@hfirstThetaOne)
          (@hgammaUnusedOne) (@hcaseOne) (@hmissingPairOne) (@hchangeOne)
    have hdisjointTwo := separate rho beta D.theta hbetaTheta ctxOne.proper
      (T.vertex ib) (T.vertex D.penultimateVertexIndex) (T.vertex D.terminalVertexIndex)
      hby hbt hyt hgammaWitnessOne' hthetaPenOne (Or.inl hgammaTermOne) hsameTwo
    let muTwo := TwoColorComponentSwap G rho beta D.theta z
    have hpathTwo : TwoColorPathComponent G rho beta D.theta z :=
      ⟨hbetaTheta, _, self rho beta D.theta _,
        leaf rho beta D.theta hbetaTheta ctxOne.proper _ (Or.inl hgammaTermOne)⟩
    have houtsideBetaTwo : Sum.inl (T.vertex ib) ∉ TwoColorComponent G rho beta D.theta z := by
      intro hm
      exact Set.disjoint_left.mp hdisjointTwo hm (self rho beta D.theta _)
    have houtsideThetaTwo : Sum.inl (T.vertex D.penultimateVertexIndex) ∉
        TwoColorComponent G rho beta D.theta z := by
      intro hm
      apply Set.disjoint_left.mp hdisjointTwo hm
      rw [hsameTwo]
      exact self rho beta D.theta _
    have hmissingTwo := prefixMissing z rho beta D.theta hbetaTheta ctxOne.proper
      hElementaryOne _ _ hibB hyB hgammaWitnessOne' hthetaPenOne
      houtsideBetaTwo houtsideThetaTwo
    have hstoredTwo : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
        HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c := by
      exact @helper_hstoredTwo_876 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
          (@firstPreserved) (@firstUnaffected) (@beta) (@POne) (@hbetaTheta) (@hElementaryOne)
          (@hbetaStoredOne) (@hmissingPairOne) (@hmissingTwo)
    exact @helper_continuation_3998 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hBlen) (@hBT) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary)
        (@hnotA) (@hshortT) (@hshortB) (@hterminalIncident) (@firstWitness) (@self)
        (@missingSubset) (@firstPreserved) (@sameStar) (@samePrefix) (@sameTn) (@sameLast)
        (@commonPrefix) (@hcoreLength) (@predecessorIncident) (@seedStable) (@weakEdges) (@beta)
        (@hbetaStored) (@houtside) (@hcutoff) (@POne) (@hlast) (@hfixed) (@hbetaTheta) (@hibB)
        (@hyt) (@horder) (@firstAfter) (@hmissingOne') (@hElementaryOne) (@hmissingA)
        (@hthetaPenOne) (@hgammaPenOne) (@hgammaTermOne) (@hgammaWitnessOne') (@hfirstGammaOne)
        (@hfirstThetaOne) (@hgammaUnusedOne) (@hcaseOne) (@hmissingPairOne) (@hdisjointTwo)
        (@hpathTwo) (@hmissingTwo) (@hstoredTwo)
private theorem helper_continuation_3031.{u_1, u_2} :
    helperContinuation3031Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A B htail hBlen hBT hApositive hAzero
      hAT hAB hBterminal hyB hElementary hfirstTheta hnotA Bshort hshortLen hshortT hshortB
      hterminalIncident firstWitness self missingSubset leaf separate separateAny prefixMissing
      firstPreserved firstUnaffected seriesFacts corrRefl
  let PRefl : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
    { coloring := phi
      corresponding := corrRefl
      maximum := C.maximum
      replacementBase := base
      counterexample := C
      sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
        rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
      minimumContext := ctx }
  have sameStar (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) = A := by
    exact @SharedFacts.FirstSubcaseTransport.sameStar (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
  have samePrefix (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1) = B
         := by
    simp only [HierarchyFullTailPrefix, HierarchyFullTailLength, sameStar P]
    rfl
  have sameTn (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      P.corresponding.replacementETT.series.data.tree
        (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    have hs := (Fin.heq_fun_iff
      (congrArg (fun n => n + 2) P.sameGood.1.2.1)).mp P.sameGood.1.2.2.1 0
    exact P.counterexample.hierarchy.baseStage.symm.trans (hs.symm.trans H.baseStage)
  have sameLast (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStoredColorsAt H q =
        HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        C.good.gamma q eta = P.counterexample.good.gamma
          (Fin.last P.counterexample.hierarchy.dividerCount) eta := by
    obtain ⟨hc, hd⟩ := P.sameGood.2
    have hi : Fin.cast (congrArg (fun n => n + 1) hc) q =
        Fin.last P.counterexample.hierarchy.dividerCount := Fin.ext hc
    simpa only [hi] using hd q
  have commonPrefix {X Y F : TreeSequence G e0}
      (hXF : TreeSequenceInitialSegment X F) (hYF : TreeSequenceInitialSegment Y F)
      (hXY : X.length ≤ Y.length) : TreeSequenceInitialSegment X Y := by
    exact @SharedFacts.SecondSituationTransport.comparableInitialSegments (@V) (@E) (@G) (@e0)
        (@X) (@Y) (@F) (@hXF) (@hYF) (@hXY)
  have hcoreLength : base.core.length ≤ A.length := by
    exact @helper_hcoreLength_566 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hApositive) (@hAzero)
  have predecessorIncident (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (t : Fin T.length)
      (ht : t.val = X.length) : TreeIncidentEdge X (T.edge t) := by
    exact @SharedFacts.SecondSituationTransport.predecessorIncident (@V) (@E) inferInstance
        inferInstance (@G) (@e0) (@T)
        (@X) (@hXT) (@t) (@ht)
  have seedStable {input' : PartialEdgeColoring E k}
      (rho sigma : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T rho)
      (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base')
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma)
      (hq : K.dividerCount = 0) :
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
        (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma := by
    exact @SharedFacts.SecondSituationTransport.seedStable (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@T) (@input') (@rho) (@sigma) (@ett') (@base') (@K) (@hw)
        (@hq)
  have weakEdges {input' : PartialEdgeColoring E k}
      (old new : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T old)
      (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base')
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
      (ho : IsOneEdgeUncolored old e0) (hno : IsOneEdgeUncolored new e0) :
      ∀ t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length,
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
          old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) := by
    exact @SharedFacts.SecondSituationTransport.weakEdges (@V) (@E) inferInstance
        inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@T) (@input') (@old) (@new) (@ett') (@base') (@K) (@hw) (@ho) (@hno)
  -- Swap the last-edge color, preserving the certified prefix route and Gamma cutoffs.
  have finish (beta : Fin k)
      (hbetaMissing : beta ∈ TreeMissingColors phi Bshort)
      (hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
      (hbetaStored : beta ∉ HierarchyStoredColorsAt H q)
      (houtside : beta ∉ TreeMissingColors phi A →
        D.theta ∉ HierarchyStoredColorsAt H q)
      (hcutoff : ∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta →
          eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hprefix : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G POne.coloring v = MissingColors G phi v)
      (hterm : beta ∈ MissingColors G POne.coloring (T.vertex D.terminalVertexIndex))
      (hlast : POne.coloring (T.edge D.lastEdgeIndex) = some D.theta)
      (hfixed : ∀ t : Fin T.length, A.length ≤ t.val →
        POne.coloring (T.edge t) = phi (T.edge t))
      (hUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        POne.coloring (T.edge t) ≠ some beta)
      (hzero : POne.counterexample.hierarchy.dividerCount = 0 →
        beta ∈ TreeMissingColors POne.coloring A →
        beta ∈ TreeMissingColors POne.coloring
          (POne.corresponding.replacementETT.series.data.tree
            (Fin.last POne.corresponding.replacementETT.rounds).castSucc) ∨
        (beta ∉ TashkinovStoredColors POne.corresponding.replacementETT.series.data
          (Fin.last POne.corresponding.replacementETT.rounds) ∧
         D.theta ∉ TashkinovStoredColors POne.corresponding.replacementETT.series.data
          (Fin.last POne.corresponding.replacementETT.rounds))) : False := by
    exact @helper_finish_3305 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail) (@hBlen)
        (@hBT) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary) (@hfirstTheta)
        (@hnotA) (@hshortLen) (@hshortT) (@hshortB) (@hterminalIncident) (@firstWitness) (@self)
        (@missingSubset) (@leaf) (@separate) (@prefixMissing) (@firstPreserved)
        (@firstUnaffected) (@sameStar) (@samePrefix) (@sameTn) (@sameLast) (@commonPrefix)
        (@hcoreLength) (@predecessorIncident) (@seedStable) (@weakEdges) (@beta) (@hbetaMissing)
        (@hbetaUnused) (@hbetaStored) (@houtside) (@hcutoff) (@POne) (@hprefix) (@hterm) (@hlast)
        (@hfixed) (@hUnused) (@hzero)
  -- A tail-unused stage color can replace alpha without changing any tail edge.
  exact @helper_continuation_3433 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hBlen) (@hBT) (@hApositive) (@hAzero) (@hAT) (@hAB) (@hElementary) (@hfirstTheta)
      (@hnotA) (@hshortLen) (@hshortT) (@hshortB) (@firstWitness) (@self) (@missingSubset)
      (@leaf) (@separateAny) (@prefixMissing) (@firstPreserved) (@firstUnaffected) (@seriesFacts)
      (@sameTn) (@commonPrefix) (@finish)
theorem HierarchySituationTwoSubcaseThreeTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeTwoData
      G k e0 input T phi ett base C ctx) :
    False := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have htail : 2 ≤ T.length - A.length := D.tailAtLeastTwo
  have hBlen : B.length + 1 = T.length := by
    simp only [B, HierarchyFullTailPrefix, HierarchyFullTailLength,
      TreeSequencePrefix]
    change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
    omega
  have hBT : TreeSequenceInitialSegment B T := by
    exact @SharedFacts.FirstSubcaseTransport.bT (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hBlen)
  have hApositive (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact @SharedFacts.SecondSituationTransport.apositive (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hq)
  have hAzero (hq : H.dividerCount = 0) : A = base.core := by
    have hi : q = 0 := by apply Fin.ext; simp [q, hq]
    change HierarchyStarredStage H q = _
    rw [hi]
    rfl
  have hAT : TreeSequenceInitialSegment A T := by
    exact @SharedFacts.SecondSituationTransport.aT (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hApositive) (@hAzero)
  have hAB : TreeSequenceInitialSegment A B := by
    exact @SharedFacts.SecondSituationTransport.aB (@V) (@E) inferInstance inferInstance
        inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@htail) (@hBlen) (@hApositive)
        (@hAzero) (@hAT)
  have hBterminal : B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex := by
    exact @helper_hBterminal_159 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT)
  have hyB : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, hBterminal⟩
  have hElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have firstAt {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      HierarchyFirstMissingPosition phi T c = D.penultimateVertexIndex := by
    exact TreeSequenceFirstMissingPositionEq hBT hElementary (by
      have := D.penultimateVertexPosition
      omega) hc
  have hfirstTheta := firstAt D.thetaMissingPenultimate
  have hnotA {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      c ∉ TreeMissingColors phi A := by
    exact @helper_hnotA_197 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
        (@hApositive) (@hAzero) (@hAT) (@hAB) (@hyB) (@hElementary) (@c) (@hc)
  let Bshort := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
  have hshortLen : Bshort.length + 2 = T.length := by
    change min (A.length + (T.length - A.length - 2)) T.length + 2 = T.length
    omega
  have hshortT : TreeSequenceInitialSegment Bshort T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hshortB : TreeSequenceInitialSegment Bshort B := by
    exact @helper_hshortB_220 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hBlen) (@hshortLen)
  have hterminalIncident :
      Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
    exact @helper_hterminalIncident_226 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hshortLen)
  have firstWitness (rho : PartialEdgeColoring E k) (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (c : Fin k)
      (hc : c ∈ TreeMissingColors rho X) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      (HierarchyFirstMissingPosition rho T c).val ≤ X.length := by
    exact @SharedFacts.SecondSituationTransport.firstWitness (@V) (@E) inferInstance
        inferInstance (@G) (@k) (@e0) (@T)
        (@rho) (@X) (@hXT) (@c) (@hc)
  have self (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl v) = _
    rfl
  have missingSubset (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      TreeMissingColors rho X ⊆ TreeMissingColors rho Y := by
    exact @SharedFacts.SecondSituationTransport.missingSubset (@V) (@E) inferInstance
        inferInstance (@G) (@k) (@e0) (@rho)
        (@X) (@Y) (@hXY)
  have leaf := TwoColorMissingVertexLeaf G k
  have separate (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    exact TwoColorMissingVerticesDisjoint G k rho a b hne hp u v w huv huw hvw hu hv hw hsame
  -- Coincident first witnesses miss both colors, so their component is isolated.
  have separateAny (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    exact TwoColorMissingVerticesDisjointAny G k rho a b hne hp u v w huw hvw hu hv hw hsame
  have prefixMissing (z : Sum V E) (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B))
      (u v : V) (huB : u ∈ TreeSequenceVertexSet B) (hvB : v ∈ TreeSequenceVertexSet B)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z)
      (hdv : Sum.inl v ∉ TwoColorComponent G rho a b z) :
      ∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
    exact TwoColorComponentSwapMissingOnElementarySet (TreeSequenceVertexSet B) rho a b
      hne hp helem z u v huB hvB hu hv hdu hdv
  have firstPreserved (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B))
      (hmiss : ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho B) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    exact @SharedFacts.SecondSituationTransport.firstPreserved (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hBT)
        (@firstWitness) (@rho) (@sigma) (@c) (@helem) (@hmiss) (@hc)
  have firstUnaffected (z : Sum V E) (rho : PartialEdgeColoring E k) (a b c : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (hca : c ≠ a) (hcb : c ≠ b) :
      HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c := by
    exact @SharedFacts.SecondSituationTransport.firstUnaffected (@V) (@E) inferInstance
        inferInstance (@G) (@k) (@e0) (@T)
        (@z) (@rho) (@a) (@b) (@c) (@hne) (@hp) (@hca) (@hcb)
  have seriesFacts : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) ∧
        IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    exact ett.series.coloringProperties
  let corrRefl : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
    { replacementInput := input
      replacementSeries := ett.series
      replacementETT := ett
      rungAgreement := rfl
      seriesPresentation := HEq.rfl
      finalGeneratingColoring := ett.generatingColoring
      ladderTreesAgree := fun _ => rfl
      storedColorsAgree := fun _ => rfl
      connectingEdgesAgree := fun _ => rfl
      extensionKindsAgree := fun _ => rfl
      replacementProper := fun j => (seriesFacts j).1
      replacementOneUncolored := fun j => (seriesFacts j).2
      replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  exact @helper_continuation_3031 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hBlen) (@hBT) (@hApositive) (@hAzero) (@hAT) (@hAB) (@hBterminal) (@hyB) (@hElementary)
      (@hfirstTheta) (@hnotA) (@hshortLen) (@hshortT) (@hshortB) (@hterminalIncident)
      (@firstWitness) (@self) (@missingSubset) (@leaf) (@separate) (@separateAny)
      (@prefixMissing) (@firstPreserved) (@firstUnaffected) (@seriesFacts)
end GoldbergSeymour

end
