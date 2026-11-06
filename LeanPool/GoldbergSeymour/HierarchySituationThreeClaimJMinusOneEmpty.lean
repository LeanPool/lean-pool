/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.StoredExceptionTransport


public import LeanPool.GoldbergSeymour.EmptyCommonMissingLocation
public import LeanPool.GoldbergSeymour.BaseExtraReplacement
public import LeanPool.GoldbergSeymour.AbsentOwnerReplacement
public import LeanPool.GoldbergSeymour.LateOwnerReplacement
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTerminalCommonMissing
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.HierarchySituationThreeClaimJMinusOneNonempty

/-!
# Hierarchy Situation Three Claim JMinus One Empty

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch291Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy →
   HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C →
    (∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu →
       IsOneEdgeUncolored mu e0 → ∀ (v : V), (MissingColors G mu v).Nonempty) →
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
        ladderTreesAgree := fun (_ : Fin ett.rounds) => rfl,
        storedColorsAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
        connectingEdgesAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
        extensionKindsAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
        replacementProper := seriesProper, replacementOneUncolored := seriesOne,
        replacementStable := fun (x : Fin ett.rounds) =>
         (⟨fun (x_1 : E) (_ : TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) x_1)
            (_ :
             ∃
              c ∈
               TreeMissingColors (ett.series.data.coloring x.succ)
                 (ett.series.data.tree x.succ.castSucc) ∪
                TashkinovStoredColors ett.series.data x.succ,
              ett.series.data.coloring x.succ x_1 = some c) =>
           rfl,
           fun (x_1 : V) (_ : x_1 ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc)) =>
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
        coloring := phi, corresponding := selfCorr, maximum := C.maximum, replacementBase := base,
        counterexample := C,
        sameGood :=
         (⟨(⟨rfl,
             (⟨rfl,
               (⟨HEq.rfl,
                 (⟨HEq.rfl,
                   (⟨Iff.rfl,
                     fun
                      (_ :
                       ett.series.data.kind (Fin.last ett.rounds) =
                        some TashkinovExtensionKind.PE) =>
                     rfl⟩ :
                    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                      selfCorr.replacementETT.series.data.kind
                        (Fin.last selfCorr.replacementETT.rounds) =
                       some TashkinovExtensionKind.PE) ∧
                     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                      base.closure = base.closure))⟩ :
                  C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                   (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                     selfCorr.replacementETT.series.data.kind
                       (Fin.last selfCorr.replacementETT.rounds) =
                      some TashkinovExtensionKind.PE) ∧
                    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                     base.closure = base.closure))⟩ :
                C.hierarchy.stage ≍ C.hierarchy.stage ∧
                 C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                  (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                    selfCorr.replacementETT.series.data.kind
                      (Fin.last selfCorr.replacementETT.rounds) =
                     some TashkinovExtensionKind.PE) ∧
                   (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
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
           Exists.intro rfl fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) =>
            (⟨rfl, fun (x_1 : Fin k) (_ : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) => rfl⟩ :
             HierarchyStoredColorsAt C.hierarchy x =
               HierarchyStoredColorsAt C.hierarchy
                (Fin.cast
                 ((by
                  first
                  | omega))
                 x) ∧
              ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
               C.good.gamma x eta =
                C.good.gamma
                 (Fin.cast
                  ((by
                   first
                   | omega))
                  x)
                 eta)⟩ :
          SameHierarchyStages C.hierarchy C.hierarchy ∧
           ∃ (hcount : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
            ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
             have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
              Fin.cast
               ((by
                first
                | omega))
               j;
             HierarchyStoredColorsAt C.hierarchy j = HierarchyStoredColorsAt C.hierarchy j₂ ∧
              ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j,
               C.good.gamma j eta = C.good.gamma j₂ eta),
        minimumContext := ctx :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
      let j : ℕ := HierarchyPathNumber C.hierarchy;
      let ell : ℕ := HierarchyFullTailLength C;
      let A : TreeSequence G e0 :=
       HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
      let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
      let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
      let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
      TreeSequenceInitialSegment A T →
       (3 : ℕ) ≤ ell →
        ell = T.length - A.length →
         (∀ r ≤ ell, (HierarchyFullTailPrefix C r).length = A.length + r) →
          (∀ (r : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T) →
           B.length = T.length - (1 : ℕ) →
            Y.length = A.length + (j - (2 : ℕ)) →
             (∀ (U : TreeSequence G e0) (i : Fin (U.length + (1 : ℕ))),
               U.vertex i ∈ TreeSequenceVertexSet U) →
              (∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))),
                c ∈ MissingColors G psi (T.vertex j) → HierarchyFirstMissingPosition psi T c ≤ j) →
               (∀ (psi : PartialEdgeColoring E k) (c : Fin k),
                 (↑(HierarchyFirstMissingPosition psi T c) : ℕ) < T.length →
                  c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c))) →
                (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
                  (c : Fin k) (i : ℕ),
                  (1 : ℕ) ≤ i ∧ i ≤ ell - (1 : ℕ) →
                   c ∈
                     MissingColors G P.coloring
                      ((HierarchyFullTailPrefix C i).vertex
                       (Fin.last (HierarchyFullTailPrefix C i).length)) →
                    c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) → I.Nonempty) →
                 ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
                  alpha ∈ TreeMissingColors phi A →
                   alpha ∈ TreeMissingColors phi Y →
                    let q : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
                     Fin.last C.hierarchy.dividerCount;
                    let D : Finset (Fin k) := HierarchyStoredColorsAt C.hierarchy q;
                    ∀ eta ∈ D,
                     alpha ∈ C.good.gamma q eta →
                      eta ∈ TreeMissingColors phi B →
                       ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
                        (alpha : Fin k),
                        let H :
                         TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
                         P.counterexample.hierarchy;
                        let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                        let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
                         Fin.last P.corresponding.replacementETT.rounds;
                        let Tn : TreeSequence G e0 :=
                         P.corresponding.replacementETT.series.data.tree n.castSucc;
                        let B : TreeSequence G e0 :=
                         HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (2 : ℕ));
                        let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
                        let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
                        let baseExtraMissing : Finset (Fin k) :=
                         (TreeSequenceVertexSet P.replacementBase.core \
                            TreeSequenceVertexSet Tn).biUnion
                          fun (v : V) => MissingColors G P.coloring v;
                        alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
                         alpha ∈ TreeMissingColors P.coloring B ∧
                          (alpha ∉ Gamma ∪ baseExtraMissing ∨
                           ∃ eta ∈ D,
                            alpha ∈ P.counterexample.good.gamma q eta ∧
                             (↑(HierarchyFirstMissingPosition P.coloring T eta) : ℕ) ≤ B.length)

private abbrev helperBranch326Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy →
   HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C →
    (∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu →
       IsOneEdgeUncolored mu e0 → ∀ (v : V), (MissingColors G mu v).Nonempty) →
     (∀ {X Y Z : TreeSequence G e0},
       TreeSequenceInitialSegment X Z →
        TreeSequenceInitialSegment Y Z → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
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
         ladderTreesAgree := fun (_ : Fin ett.rounds) => rfl,
         storedColorsAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
         connectingEdgesAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
         extensionKindsAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
         replacementProper := seriesProper, replacementOneUncolored := seriesOne,
         replacementStable := fun (x : Fin ett.rounds) =>
          (⟨fun (x_1 : E) (_ : TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) x_1)
             (_ :
              ∃
               c ∈
                TreeMissingColors (ett.series.data.coloring x.succ)
                  (ett.series.data.tree x.succ.castSucc) ∪
                 TashkinovStoredColors ett.series.data x.succ,
               ett.series.data.coloring x.succ x_1 = some c) =>
            rfl,
            fun (x_1 : V)
             (_ : x_1 ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc)) =>
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
         coloring := phi, corresponding := selfCorr, maximum := C.maximum, replacementBase := base,
         counterexample := C,
         sameGood :=
          (⟨(⟨rfl,
              (⟨rfl,
                (⟨HEq.rfl,
                  (⟨HEq.rfl,
                    (⟨Iff.rfl,
                      fun
                       (_ :
                        ett.series.data.kind (Fin.last ett.rounds) =
                         some TashkinovExtensionKind.PE) =>
                      rfl⟩ :
                     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                       selfCorr.replacementETT.series.data.kind
                         (Fin.last selfCorr.replacementETT.rounds) =
                        some TashkinovExtensionKind.PE) ∧
                      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                       base.closure = base.closure))⟩ :
                   C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                      selfCorr.replacementETT.series.data.kind
                        (Fin.last selfCorr.replacementETT.rounds) =
                       some TashkinovExtensionKind.PE) ∧
                     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                      base.closure = base.closure))⟩ :
                 C.hierarchy.stage ≍ C.hierarchy.stage ∧
                  C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                   (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                     selfCorr.replacementETT.series.data.kind
                       (Fin.last selfCorr.replacementETT.rounds) =
                      some TashkinovExtensionKind.PE) ∧
                    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
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
            Exists.intro rfl fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) =>
             (⟨rfl, fun (x_1 : Fin k) (_ : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) => rfl⟩ :
              HierarchyStoredColorsAt C.hierarchy x =
                HierarchyStoredColorsAt C.hierarchy
                 (Fin.cast
                  ((by
                   first
                   | omega))
                  x) ∧
               ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
                C.good.gamma x eta =
                 C.good.gamma
                  (Fin.cast
                   ((by
                    first
                    | omega))
                   x)
                  eta)⟩ :
           SameHierarchyStages C.hierarchy C.hierarchy ∧
            ∃ (hcount : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
             ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
              have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
               Fin.cast
                ((by
                 first
                 | omega))
                j;
              HierarchyStoredColorsAt C.hierarchy j = HierarchyStoredColorsAt C.hierarchy j₂ ∧
               ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j,
                C.good.gamma j eta = C.good.gamma j₂ eta),
         minimumContext := ctx :
         HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
       let j : ℕ := HierarchyPathNumber C.hierarchy;
       let ell : ℕ := HierarchyFullTailLength C;
       let A : TreeSequence G e0 :=
        HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
       let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
       let Y : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
       let I : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
       TreeSequenceInitialSegment A T →
        (3 : ℕ) ≤ ell →
         ell = T.length - A.length →
          (∀ r ≤ ell, (HierarchyFullTailPrefix C r).length = A.length + r) →
           (∀ (r : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T) →
            B.length = T.length - (1 : ℕ) →
             Y.length = A.length + (j - (2 : ℕ)) →
              TreeSequenceInitialSegment A Y →
               (∀ {X Z : TreeSequence G e0} (psi : PartialEdgeColoring E k),
                 TreeSequenceInitialSegment X Z →
                  TreeMissingColors psi X ⊆ TreeMissingColors psi Z) →
                (∀ (U : TreeSequence G e0) (i : Fin (U.length + (1 : ℕ))),
                  U.vertex i ∈ TreeSequenceVertexSet U) →
                 (∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (T.length + (1 : ℕ))),
                   c ∈ MissingColors G psi (T.vertex j) →
                    HierarchyFirstMissingPosition psi T c ≤ j) →
                  (∀ (psi : PartialEdgeColoring E k) (c : Fin k),
                    (↑(HierarchyFirstMissingPosition psi T c) : ℕ) < T.length →
                     c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c))) →
                   (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
                     (c : Fin k) (i : ℕ),
                     (1 : ℕ) ≤ i ∧ i ≤ ell - (1 : ℕ) →
                      c ∈
                        MissingColors G P.coloring
                         ((HierarchyFullTailPrefix C i).vertex
                          (Fin.last (HierarchyFullTailPrefix C i).length)) →
                       c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) → I.Nonempty) →
                    (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                      ∀
                       c ∈
                        TreeMissingColors P.coloring
                         (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))),
                       c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) →
                        c ∈
                         TreeMissingColors P.coloring
                          (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))) →
                     ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
                      alpha ∈ TreeMissingColors phi A →
                       alpha ∈ TreeMissingColors phi Y →
                        let q : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
                         Fin.last C.hierarchy.dividerCount;
                        let D : Finset (Fin k) := HierarchyStoredColorsAt C.hierarchy q;
                        let Gamma : Finset (Fin k) := D.biUnion (C.good.gamma q);
                        alpha ∈ Gamma →
                         ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
                          (alpha : Fin k),
                          let H :
                           TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
                           P.counterexample.hierarchy;
                          let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                          let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
                           Fin.last P.corresponding.replacementETT.rounds;
                          let Tn : TreeSequence G e0 :=
                           P.corresponding.replacementETT.series.data.tree n.castSucc;
                          let B : TreeSequence G e0 :=
                           HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (2 : ℕ));
                          let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
                          let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
                          let baseExtraMissing : Finset (Fin k) :=
                           (TreeSequenceVertexSet P.replacementBase.core \
                              TreeSequenceVertexSet Tn).biUnion
                            fun (v : V) => MissingColors G P.coloring v;
                          alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
                           alpha ∈ TreeMissingColors P.coloring B ∧
                            (alpha ∉ Gamma ∪ baseExtraMissing ∨
                             ∃ eta ∈ D,
                              alpha ∈ P.counterexample.good.gamma q eta ∧
                               (↑(HierarchyFirstMissingPosition P.coloring T eta) : ℕ) ≤ B.length)

private abbrev helperContinuation671Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy →
   HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C →
    (∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu →
       IsOneEdgeUncolored mu e0 → ∀ (v : V), (MissingColors G mu v).Nonempty) →
     ¬(HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty →
      (∀ {X Y Z : TreeSequence G e0},
        TreeSequenceInitialSegment X Z →
         TreeSequenceInitialSegment Y Z → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
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
          ladderTreesAgree := fun (_ : Fin ett.rounds) => rfl,
          storedColorsAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
          connectingEdgesAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
          extensionKindsAgree := fun (_ : Fin (ett.rounds + (1 : ℕ))) => rfl,
          replacementProper := seriesProper, replacementOneUncolored := seriesOne,
          replacementStable := fun (x : Fin ett.rounds) =>
           (⟨fun (x_1 : E) (_ : TreeIncidentEdge (ett.series.data.tree x.succ.castSucc) x_1)
              (_ :
               ∃
                c ∈
                 TreeMissingColors (ett.series.data.coloring x.succ)
                   (ett.series.data.tree x.succ.castSucc) ∪
                  TashkinovStoredColors ett.series.data x.succ,
                ett.series.data.coloring x.succ x_1 = some c) =>
             rfl,
             fun (x_1 : V)
              (_ : x_1 ∈ TreeSequenceVertexSet (ett.series.data.tree x.succ.castSucc)) =>
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
                          some TashkinovExtensionKind.PE) =>
                       rfl⟩ :
                      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                        selfCorr.replacementETT.series.data.kind
                          (Fin.last selfCorr.replacementETT.rounds) =
                         some TashkinovExtensionKind.PE) ∧
                       (ett.series.data.kind (Fin.last ett.rounds) =
                         some TashkinovExtensionKind.PE →
                        base.closure = base.closure))⟩ :
                    C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                       selfCorr.replacementETT.series.data.kind
                         (Fin.last selfCorr.replacementETT.rounds) =
                        some TashkinovExtensionKind.PE) ∧
                      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
                       base.closure = base.closure))⟩ :
                  C.hierarchy.stage ≍ C.hierarchy.stage ∧
                   C.hierarchy.dividerPosition ≍ C.hierarchy.dividerPosition ∧
                    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ↔
                      selfCorr.replacementETT.series.data.kind
                        (Fin.last selfCorr.replacementETT.rounds) =
                       some TashkinovExtensionKind.PE) ∧
                     (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
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
             Exists.intro rfl fun (x : Fin (C.hierarchy.dividerCount + (1 : ℕ))) =>
              (⟨rfl, fun (x_1 : Fin k) (_ : x_1 ∈ HierarchyStoredColorsAt C.hierarchy x) => rfl⟩ :
               HierarchyStoredColorsAt C.hierarchy x =
                 HierarchyStoredColorsAt C.hierarchy
                  (Fin.cast
                   ((by
                    first
                    | omega))
                   x) ∧
                ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy x,
                 C.good.gamma x eta =
                  C.good.gamma
                   (Fin.cast
                    ((by
                     first
                     | omega))
                    x)
                   eta)⟩ :
            SameHierarchyStages C.hierarchy C.hierarchy ∧
             ∃ (hcount : C.hierarchy.dividerCount = C.hierarchy.dividerCount),
              ∀ (j : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
               have j₂ : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
                Fin.cast
                 ((by
                  first
                  | omega))
                 j;
               HierarchyStoredColorsAt C.hierarchy j = HierarchyStoredColorsAt C.hierarchy j₂ ∧
                ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy j,
                 C.good.gamma j eta = C.good.gamma j₂ eta),
          minimumContext := ctx :
          HierarchyReplacementPresentation G k e0 input T phi ett base C ctx };
        let j : ℕ := HierarchyPathNumber C.hierarchy;
        let ell : ℕ := HierarchyFullTailLength C;
        let A : TreeSequence G e0 :=
         HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
        let _ : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
        let _ : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
        let _ : Finset ℕ := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx;
        TreeSequenceInitialSegment A T →
         ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
          let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
           P.counterexample.hierarchy;
          let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
          let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
           Fin.last P.corresponding.replacementETT.rounds;
          let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
          let B : TreeSequence G e0 :=
           HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (2 : ℕ));
          let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
          let Gamma : Finset (Fin k) := D.biUnion (P.counterexample.good.gamma q);
          let baseExtraMissing : Finset (Fin k) :=
           (TreeSequenceVertexSet P.replacementBase.core \ TreeSequenceVertexSet Tn).biUnion
            fun (v : V) => MissingColors G P.coloring v;
          alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
           alpha ∈ TreeMissingColors P.coloring B ∧
            (alpha ∉ Gamma ∪ baseExtraMissing ∨
             ∃ eta ∈ D,
              alpha ∈ P.counterexample.good.gamma q eta ∧
               (↑(HierarchyFirstMissingPosition P.coloring T eta) : ℕ) ≤ B.length)

private theorem helper_branch_291.{u_1, u_2} :
    helperBranch291Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower hpathUpper hvertexMissing
      seriesProper seriesOne selfCorr P0 j ell A B Y I hAT htail hell prefixLen prefixT hBLen
      hYLen vertexMem firstLe firstMem eligible alpha haTerminal haA haY q D eta heta haGamma howner
  obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp howner
  obtain ⟨x, hx⟩ : ∃ x, B.vertex x = v := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hv
  have hmT : eta ∈ MissingColors G phi
      (T.vertex (Fin.castLE (Nat.succ_le_succ (prefixT (ell - 1)).1) x)) := by
    rw [(prefixT (ell - 1)).2.1, hx]; exact hm
  have hfLe := firstLe phi eta _ hmT
  have hfLt : (HierarchyFirstMissingPosition phi T eta).val < T.length := by
    change (HierarchyFirstMissingPosition phi T eta).val ≤ x.val at hfLe
    have := x.isLt
    omega
  have hmFirst := firstMem phi eta hfLt
  have hnotA : eta ∉ TreeMissingColors phi A := (Finset.mem_sdiff.mp heta).2
  have hfPos : A.length < (HierarchyFirstMissingPosition phi T eta).val := by
    by_contra hh
    have hle : (HierarchyFirstMissingPosition phi T eta).val ≤ A.length := by omega
    let a : Fin (A.length + 1) := ⟨(HierarchyFirstMissingPosition phi T eta).val, by omega⟩
    have hidx : Fin.castLE (Nat.succ_le_succ hAT.1) a =
        HierarchyFirstMissingPosition phi T eta := Fin.ext rfl
    apply hnotA
    refine Finset.mem_biUnion.mpr ⟨A.vertex a, vertexMem A a, ?_⟩
    rw [← hAT.2.1 a, hidx]
    exact hmFirst
  by_cases hsmall : (HierarchyFirstMissingPosition phi T eta).val ≤ Y.length
  · exact ⟨P0, alpha, haTerminal, haY, Or.inr ⟨eta, heta, haGamma, hsmall⟩⟩
  let t := (HierarchyFirstMissingPosition phi T eta).val - A.length
  have htpos : 1 ≤ t := by dsimp [t]; omega
  have htupper : t < ell := by dsimp [t]; omega
  have htlate : j - 1 ≤ t := by dsimp [t]; omega
  have hfirst : (HierarchyFirstMissingPosition phi T eta).val = A.length + t := by
    dsimp [t]; omega
  have hmTail : eta ∈ MissingColors G phi
      ((HierarchyFullTailPrefix C t).vertex
        (Fin.last (HierarchyFullTailPrefix C t).length)) := by
    rw [← (prefixT t).2.1]
    have hp := prefixLen t (by omega)
    have hidx : Fin.castLE (Nat.succ_le_succ (prefixT t).1)
        (Fin.last (HierarchyFullTailPrefix C t).length) =
        HierarchyFirstMissingPosition phi T eta := by
      apply Fin.ext
      simp only [Fin.val_castLE, Fin.val_last]
      omega
    rw [hidx]
    exact hmFirst
  obtain ⟨P, hterm, htailMissing⟩ := P2905_T2_LateOwnerReplacement
    G k e0 input T phi ett base C ctx hpathLower hpathUpper
    alpha haTerminal haA eta heta haGamma t htpos htupper htlate hfirst hmTail
  exact HierarchySituationThreeClaimJMinusOneNonempty G k e0 input T phi
    ett base C ctx hpathLower hpathUpper hvertexMissing
    (eligible P eta t ⟨htpos, by omega⟩ htailMissing hterm)

private theorem helper_branch_326.{u_1, u_2} :
    helperBranch326Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower hpathUpper hvertexMissing common
      seriesProper seriesOne selfCorr P0 j ell A B Y I hAT htail hell prefixLen prefixT hBLen
      hYLen hAY missingMono vertexMem firstLe firstMem eligible emptyReduction alpha haTerminal
      haA haY q D Gamma hgamma
  obtain ⟨eta, heta, haGamma⟩ := Finset.mem_biUnion.mp hgamma
  by_cases howner : eta ∈ TreeMissingColors phi B
  · exact @helper_branch_291 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hpathLower hpathUpper hvertexMissing seriesProper seriesOne hAT
      htail hell prefixLen prefixT hBLen hYLen vertexMem firstLe firstMem eligible alpha
      haTerminal haA haY eta heta haGamma howner
  · obtain ⟨P, beta, hterm, hbX, hbad⟩ := P2905_T2_AbsentOwnerReplacement
      G k e0 input T phi ett base C ctx hpathLower hpathUpper
      alpha haTerminal haA eta heta haGamma howner
    have hXB : TreeSequenceInitialSegment
        (HierarchyFullTailPrefix C (ell - 2)) B :=
      common (prefixT _) (prefixT _) (by
        rw [prefixLen _ (by omega), hBLen]; omega)
    have hbA := emptyReduction P beta (missingMono P.coloring hXB hbX) hterm
    exact ⟨P, beta, hterm, missingMono P.coloring hAY hbA, Or.inl hbad⟩

private theorem helper_continuation_671.{u_1, u_2} :
    helperContinuation671Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower hpathUpper hvertexMissing hempty
      common seriesProper seriesOne selfCorr P0 j ell A B Y I hAT
  have htail : 3 ≤ ell := by change j < ell at hpathUpper; change 2 ≤ j at hpathLower; omega
  have hell : ell = T.length - A.length := rfl
  have prefixLen (r : ℕ) (hr : r ≤ ell) :
      (HierarchyFullTailPrefix C r).length = A.length + r := by as_aux_lemma =>
    change min (A.length + r) T.length = A.length + r
    apply Nat.min_eq_left
    omega
  have prefixT (r : ℕ) :
      TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBLen : B.length = T.length - 1 := by
    have := prefixLen (ell - 1) (by omega)
    change B.length = A.length + (ell - 1) at this
    omega
  have hYLen : Y.length = A.length + (j - 2) := prefixLen _ (by
    change j < ell at hpathUpper; omega)
  have hAB : TreeSequenceInitialSegment A B := common hAT (prefixT _) (by omega)
  have hAY : TreeSequenceInitialSegment A Y := common hAT (prefixT _) (by omega)
  have hYB : TreeSequenceInitialSegment Y B := common (prefixT _) (prefixT _) (by
    change j < ell at hpathUpper; omega)
  have missingMono {X Z : TreeSequence G e0}
      (psi : PartialEdgeColoring E k) (hXZ : TreeSequenceInitialSegment X Z) :
      TreeMissingColors psi X ⊆ TreeMissingColors psi Z := by as_aux_lemma =>
    intro c hc
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXZ hv, hm⟩
  have vertexMem (U : TreeSequence G e0) (i : Fin (U.length + 1)) :
      U.vertex i ∈ TreeSequenceVertexSet U := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
      (j : Fin (T.length + 1)) (hj : c ∈ MissingColors G psi (T.vertex j)) :
      HierarchyFirstMissingPosition psi T c ≤ j := by as_aux_lemma =>
    clear * - G T psi c j hj
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    have hm : j ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hn : candidates.Nonempty := ⟨j, hm⟩
    unfold HierarchyFirstMissingPosition
    rw [dite_eq_left hn]
    exact Finset.min'_le candidates j hm
  have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition psi T c).val < T.length) :
      c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
          as_aux_lemma =>
    clear * - G T psi c hlt
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    by_cases hn : candidates.Nonempty
    · unfold HierarchyFirstMissingPosition
      rw [dite_eq_left hn]
      exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    · have hh : (HierarchyFirstMissingPosition psi T c).val = T.length := by
        unfold HierarchyFirstMissingPosition
        rw [dite_eq_right hn]
        rfl
      omega
  have eligible
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ ell - 1)
      (hc : c ∈ MissingColors G P.coloring
        ((HierarchyFullTailPrefix C i).vertex
          (Fin.last (HierarchyFullTailPrefix C i).length)))
      (hterm : c ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length))) :
      I.Nonempty := by as_aux_lemma =>
    refine ⟨i, ?_⟩
    change i ∈ (Finset.Icc 1 (HierarchyFullTailLength C - 1)).filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hi, P, c, hc, hterm⟩
  have emptyReduction := P2905_T2_EmptyCommonMissingLocation
    G k e0 input T phi ett base C ctx hpathLower hpathUpper hempty
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  obtain ⟨alpha, haPen, haTerminal⟩ :=
    HierarchyCounterexampleTerminalCommonMissing G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have haA : alpha ∈ TreeMissingColors phi A := emptyReduction P0 alpha haPen haTerminal
  have haY : alpha ∈ TreeMissingColors phi Y := missingMono phi hAY haA
  let q := Fin.last C.hierarchy.dividerCount
  let D := HierarchyStoredColorsAt C.hierarchy q
  let Gamma := D.biUnion (C.good.gamma q)
  let Extra := ((TreeSequenceVertexSet base.core \
      TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)).biUnion
        fun v => MissingColors G phi v)
  by_cases hfree : alpha ∉ Gamma ∪ Extra
  · exact ⟨P0, alpha, haTerminal, haY, Or.inl hfree⟩
  by_cases hgamma : alpha ∈ Gamma
  · exact @helper_branch_326 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C ctx hpathLower hpathUpper hvertexMissing common seriesProper
      seriesOne hAT htail hell prefixLen prefixT hBLen hYLen hAY missingMono vertexMem firstLe
      firstMem eligible emptyReduction alpha haTerminal haA haY hgamma
  · have hextra : alpha ∈ Extra := by
      have hmem : alpha ∈ Gamma ∪ Extra := by simpa only [not_not] using hfree
      exact (Finset.mem_union.mp hmem).resolve_left hgamma
    obtain ⟨P, beta, hterm, hbA, hbad⟩ := P2905_T2_BaseExtraReplacement
      G k e0 input T phi ett base C ctx hpathLower hpathUpper
      alpha haTerminal haA hextra hgamma
    exact ⟨P, beta, hterm, missingMono P.coloring hAY hbA, Or.inl hbad⟩

theorem HierarchySituationThreeClaimJMinusOneEmpty {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (hempty : ¬ (HierarchyEligibleCommonMissingIndices
      G k e0 input T phi ett base C ctx).Nonempty) :
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
    ∃ alpha : Fin k,
    let H := P.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
      Fin.last P.corresponding.replacementETT.rounds
    let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
    let B := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 2)
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (P.counterexample.good.gamma q)
    let baseExtraMissing :=
      ((TreeSequenceVertexSet P.replacementBase.core \ TreeSequenceVertexSet Tn).biUnion
        fun v => MissingColors G P.coloring v)
    alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
      alpha ∈ TreeMissingColors P.coloring B ∧
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          ∃ eta : Fin k,
            eta ∈ D ∧
              alpha ∈ P.counterexample.good.gamma q eta ∧
                (HierarchyFirstMissingPosition P.coloring T eta).val ≤ B.length) := by
  classical
  have common {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by as_aux_lemma =>
    clear * - hXZ hYZ hXY
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
  have seriesProper : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) := by
    intro j
    exact (ett.series.coloringProperties j).1
  have seriesOne : ∀ j : Fin (ett.rounds + 1),
      IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    intro j
    exact (ett.series.coloringProperties j).2
  let selfCorr := @SharedFacts.StoredExceptionTransport.selfCorr425 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@phi) (@ett) (@seriesProper) (@seriesOne)
  let P0 := @SharedFacts.StoredExceptionTransport.p0462 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@seriesProper) (@seriesOne)
  let j := HierarchyPathNumber C.hierarchy
  let ell := HierarchyFullTailLength C
  let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  let B := HierarchyFullTailPrefix C (ell - 1)
  let Y := HierarchyFullTailPrefix C (j - 2)
  let I := HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx
  have hAT : TreeSequenceInitialSegment A T := by
    have starNext (i : Fin (C.hierarchy.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy i)
          (C.hierarchy.stage i.succ) :=
      Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) i
    simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
      starNext (Fin.last C.hierarchy.dividerCount)
  exact @helper_continuation_671 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx hpathLower hpathUpper hvertexMissing hempty common
      seriesProper seriesOne hAT
end GoldbergSeymour

end
