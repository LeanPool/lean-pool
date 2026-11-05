/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.CertifiedETTPredecessor
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HierarchyCounterexample
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPosition
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchySegmentColors
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HierarchyStageMissingColors
public import LeanPool.GoldbergSeymour.HierarchyStarredStage
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.OrderedTreeUnion
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceComponentSwap
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovExtensionKind
public import LeanPool.GoldbergSeymour.TashkinovHierarchy
public import LeanPool.GoldbergSeymour.TashkinovStoredColors
public import LeanPool.GoldbergSeymour.TreeColorSetMinusClosed
public import LeanPool.GoldbergSeymour.TreeColoringInvariant
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.BaseControl
public import LeanPool.GoldbergSeymour.DisplayedEdges
public import LeanPool.GoldbergSeymour.MinusClosedTransport
public import LeanPool.GoldbergSeymour.PrefixSegmentTransport
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Stable Change Cases One Two Split Tail

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation777Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
   HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (alpha beta : Fin k),
     alpha ≠ beta →
      ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
       sigma = TwoColorComponentSwap G phi alpha beta z →
        ∀ (X : TreeSequence G e0),
         (let H : TashkinovHierarchy ett base := C.hierarchy;
          let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
          ∀ (t : Fin T.length),
           A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → sigma (T.edge t) = phi (T.edge t)) →
          (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
           let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
           ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
             TashkinovAugmentationSequence sigma Tn X ∨
            (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
             ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = { f } ∧
               TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) →
           TashkinovAugmentationSequence phi X T →
            alpha ∈ TreeMissingColors sigma X ∧ beta ∈ TreeMissingColors sigma X →
             (let H : TashkinovHierarchy ett base := C.hierarchy;
              let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
              ∀ eta ∈ HierarchyStoredColorsAt H q,
               HierarchyFirstMissingPosition sigma T eta =
                HierarchyFirstMissingPosition phi T eta) →
              (let H : TashkinovHierarchy ett base := C.hierarchy;
               let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
               ∀ eta ∈ HierarchyStoredColorsAt H q,
                alpha ∈ C.good.gamma q eta ∨ beta ∈ C.good.gamma q eta →
                 (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) ≤ X.length) →
               let H : TashkinovHierarchy ett base := C.hierarchy;
               let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
               let A : TreeSequence G e0 := HierarchyStarredStage H q;
               let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
               let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
               let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
               (if ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE then
                 CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                  base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi
                  sigma
                else
                 StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                  (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma) →
                IsProperEdgeColoring G sigma →
                 IsOneEdgeUncolored sigma e0 →
                  (∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
                    c = alpha ∨ c = beta →
                     c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
                      TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) { c } →
                       OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha
                        beta) →
                   HierarchyWeaklyStable C.hierarchy (Fin.last C.hierarchy.dividerCount) sigma →
                    ModColoring ett sigma →
                     ((0 : ℕ) < C.hierarchy.dividerCount →
                       ∃ (inputA : PartialEdgeColoring E k) (ettA :
                        ExtendedTashkinovTree G k e0 inputA
                         (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))
                         sigma)
                        (baseA : HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA)
                        (goodA : GoodHierarchy K),
                        MaximumProperty ettA ∧
                         ettA.series.data.kind (Fin.last ettA.rounds) =
                           ett.series.data.kind (Fin.last ett.rounds) ∧
                          ∃ (hcount : K.dividerCount + (1 : ℕ) = C.hierarchy.dividerCount),
                           baseA.core = base.core ∧
                            baseA.closure = base.closure ∧
                             (∀ (j : Fin (K.dividerCount + (2 : ℕ))),
                               K.stage j =
                                C.hierarchy.stage
                                 (⟨(↑j : ℕ), by omega⟩ :
                                  Fin (C.hierarchy.dividerCount + (2 : ℕ)))) ∧
                              (∀ (j : Fin (K.dividerCount + (1 : ℕ))),
                                have jH : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
                                 (⟨(↑j : ℕ), by omega⟩ : Fin (C.hierarchy.dividerCount + (1 : ℕ)));
                                HierarchyStoredColorsAt K j =
                                  HierarchyStoredColorsAt C.hierarchy jH ∧
                                 ∀ eta ∈ HierarchyStoredColorsAt K j,
                                  goodA.gamma j eta = C.good.gamma jH eta) ∧
                               TreeColorSetMinusClosed G sigma
                                (C.hierarchy.stage
                                 (⟨C.hierarchy.dividerCount, by omega⟩ :
                                  Fin (C.hierarchy.dividerCount + (2 : ℕ))))
                                ((HierarchyStoredColorsAt C.hierarchy
                                   (Fin.last C.hierarchy.dividerCount)).biUnion
                                 (C.good.gamma
                                  (⟨C.hierarchy.dividerCount - (1 : ℕ), by omega⟩ :
                                   Fin (C.hierarchy.dividerCount + (1 : ℕ)))))) →
                      TreeSequenceInitialSegment A X →
                       A.length < X.length →
                        (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
                         (∀ v ∈ TreeSequenceVertexSet A,
                           MissingColors G sigma v = MissingColors G phi v) →
                          (∀ {S U : TreeSequence G e0},
                            TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
                           (H.dividerCount = (0 : ℕ) → A = base.core) →
                            TreeSequenceInitialSegment Tn A →
                             (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                               TreeSequenceInitialSegment (H.stage j.castSucc) A) →
                              (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
                               TreeSequenceInitialSegment X T →
                                TreeSequenceInitialSegment A T →
                                 (∀ (S : TreeSequence G e0),
                                   TreeSequenceInitialSegment S A →
                                    TreeMissingColors sigma S = TreeMissingColors phi S) →
                                  let H : TashkinovHierarchy ett base := C.hierarchy;
                                  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                                  HierarchyWeaklyStable H q sigma ∧
                                   ModColoring ett sigma ∧
                                    ∃ (corrT :
                                     CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                                     MaximumProperty corrT.replacementETT ∧
                                      ∃ (baseT : HierarchyBase corrT.replacementETT sigma) (K :
                                       TashkinovHierarchy corrT.replacementETT baseT) (goodT :
                                       GoodHierarchy K), SameGoodHierarchy C.good goodT

private theorem helper_corrData_311.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k) (_ : TreeSequence G e0),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    TreeSequenceInitialSegment Tn A →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        Tn ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind n ∧
        TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) =
          Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma X H q A n Tn Dn TnToA treeMissingEq corr
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generating =>
    cases rungAgreement
    have hs : replacementData = replacementSeries := eq_of_heq seriesPresentation
    cases hs
    let a : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
    have ha : a.succ = Fin.last ett.rounds := by
      apply Fin.ext
      change ett.rounds - 1 + 1 = ett.rounds
      have := ett.roundsPositive
      omega
    have ht : replacementSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
      change replacementSeries.data.tree (Fin.last ett.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc
      rw [← ha]
      exact ladderTreesAgree a
    have hm : TreeMissingColors (replacementSeries.data.coloring (Fin.last ett.rounds))
        (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors phi Tn := by
      rw [← finalGeneratingColoring, ht]
      exact treeMissingEq Tn TnToA
    have hmOld : TreeMissingColors (ett.series.data.coloring (Fin.last ett.rounds))
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors phi Tn := by
      rw [← ett.generatingColoring]
    refine ⟨ht, extensionKindsAgree (Fin.last ett.rounds), ?_⟩
    change TashkinovStoredColors replacementSeries.data (Fin.last ett.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds)
    simp only [TashkinovStoredColors, storedColorsAgree, hm, hmOld]

private theorem helper_fullBase_358.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (sigma : PartialEdgeColoring E k),
    let _ : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    ModColoring ett sigma →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn T ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = { f } ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence sigma seed T) →
    (∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
        corr.replacementETT.series.data.tree
              (Fin.last corr.replacementETT.rounds).castSucc =
            Tn ∧
          corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corr.replacementETT.series.data
                (Fin.last corr.replacementETT.rounds) =
              Dn) →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        CombinedStableColoring Tn base.closure Dn phi sigma) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    MaximumProperty corr.replacementETT ∧
      ∃ (baseT : HierarchyBase corr.replacementETT sigma),
        baseT.core = base.core ∧ baseT.closure = base.closure := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx sigma H n Tn Dn hsproper hsone hmod
      fullRoute corrData combined
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · have hb : TashkinovAugmentationSequence sigma Tn T := by
      rcases fullRoute with ⟨_, hseq⟩ | ⟨hk, rest⟩
      · exact hseq
      · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
    obtain ⟨corr, hMP, baseT, K0, hsame⟩ := HierarchySplitter G k e0 input T phi sigma
      ett C.maximum C.positive ctx.lowerRung base H hp ctx.proper ctx.oneEdgeUncolored
      hsproper hsone (combined hp) hb
    exact ⟨corr, hMP, baseT, hsame.1.symm, (hsame.2.2.2.2.2 hp).symm⟩
  · obtain ⟨corr⟩ := hmod.2.2 T ett.abovePenultimate ett.strictAbovePenultimate fullRoute
    have hd := corrData corr
    let pos : Fin ((corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc).length + 1) :=
      Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1) hd.1.symm)
        base.supportPosition
    let baseT : HierarchyBase corr.replacementETT sigma := {
      core := base.core
      closure := base.closure
      supportPosition := pos
      supportPositive := by simpa [pos] using base.supportPositive
      terminalMissingColors := rfl
      parallel := by
        dsimp only
        intro hPE
        exact False.elim (hp (hd.2.1.symm.trans hPE))
      nonparallel := by
        dsimp only
        intro _
        exact (base.nonparallel hp).trans hd.1.symm }
    exact ⟨corr, MaximumPropertyTransport G k e0 ett sigma hmod T corr C.maximum,
      baseT, rfl, rfl⟩

private theorem helper_coreNotClosed_479.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k) (X : TreeSequence G e0),
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
      ∀ (t : Fin T.length),
        A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → sigma (T.edge t) = phi (T.edge t)) →
    (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn X ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = { f } ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence sigma seed X) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ((0 : ℕ) < C.hierarchy.dividerCount →
        ∃ (inputA : PartialEdgeColoring E k) (ettA :
          ExtendedTashkinovTree G k e0 inputA
            (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) sigma)
          (baseA : HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA) (goodA :
          GoodHierarchy K),
          MaximumProperty ettA ∧
            ettA.series.data.kind (Fin.last ettA.rounds) =
                ett.series.data.kind (Fin.last ett.rounds) ∧
              ∃ (hcount : K.dividerCount + (1 : ℕ) = C.hierarchy.dividerCount),
                baseA.core = base.core ∧
                  baseA.closure = base.closure ∧
                    (∀ (j : Fin (K.dividerCount + (2 : ℕ))),
                        K.stage j =
                          C.hierarchy.stage
                            (⟨(↑j : ℕ), by omega⟩ :
                              Fin (C.hierarchy.dividerCount + (2 : ℕ)))) ∧
                      (∀ (j : Fin (K.dividerCount + (1 : ℕ))),
                          have jH : Fin (C.hierarchy.dividerCount + (1 : ℕ)) :=
                            (⟨(↑j : ℕ), by omega⟩ :
                              Fin (C.hierarchy.dividerCount + (1 : ℕ)));
                          HierarchyStoredColorsAt K j =
                              HierarchyStoredColorsAt C.hierarchy jH ∧
                            ∀ eta ∈ HierarchyStoredColorsAt K j,
                              goodA.gamma j eta = C.good.gamma jH eta) ∧
                        TreeColorSetMinusClosed G sigma
                          (C.hierarchy.stage
                            (⟨C.hierarchy.dividerCount, by omega⟩ :
                              Fin (C.hierarchy.dividerCount + (2 : ℕ))))
                          ((HierarchyStoredColorsAt C.hierarchy
                                (Fin.last C.hierarchy.dividerCount)).biUnion
                            (C.good.gamma
                              (⟨C.hierarchy.dividerCount - (1 : ℕ), by omega⟩ :
                                Fin (C.hierarchy.dividerCount + (1 : ℕ)))))) →
    TreeSequenceInitialSegment A X →
    A.length < X.length →
    (∀ {S U : TreeSequence G e0},
        TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment Tn A →
    TreeSequenceInitialSegment X T →
    TreeSequenceInitialSegment A T →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    ¬TreeColorSetMinusClosed G sigma base.core
        ((HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
          (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma X hfixedPrefix hrouteX H q A n Tn
      hretained hAX hAXstrict equalTrees lastZero TnToA hXT hAT hp
  by_cases hz : H.dividerCount = 0
  · have hroute : TashkinovAugmentationSequence sigma Tn X := by
      rcases hrouteX with ⟨_, hseq⟩ | ⟨hk, rest⟩
      · exact hseq
      · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
    let tX : Fin X.length := ⟨A.length, hAXstrict⟩
    let Z := TreeSequencePrefix X A.length A.positive hAX.1
    have hAZ : TreeSequenceInitialSegment A Z :=
      ⟨le_rfl, hAX.2.1, hAX.2.2⟩
    have hAZeq : A = Z := equalTrees hAZ rfl
    have hposition := TashkinovAugmentationSequencePosition sigma Tn X hroute tX TnToA.1
    obtain ⟨c, hcol, hcm⟩ := hposition.1.2.2
    have hcmA : c ∈ TreeMissingColors sigma A := by
      rw [hAZeq]
      exact hcm
    have hcolX : sigma (X.edge tX) = some c := by
      rw [← hposition.2]
      have hidx : Fin.cast hposition.1.1.symm
          (Fin.last (TreeSequencePrefix X tX.val
            (le_trans Tn.positive TnToA.1) (Nat.le_of_lt tX.isLt)).length) =
          Fin.last tX.val := Fin.ext rfl
      simpa only [hidx] using hcol
    let tT : Fin T.length := Fin.castLE hXT.1 tX
    have hcolT : sigma (T.edge tT) = some c := by
      rw [show T.edge tT = X.edge tX from hXT.2.2 tX]
      exact hcolX
    have hcolOld : phi (T.edge tT) = some c :=
      (hfixedPrefix tT le_rfl hAXstrict).symm.trans hcolT
    have firstAfter (eta : Fin k) (heta : eta ∉ TreeMissingColors phi A) :
        A.length < (HierarchyFirstMissingPosition phi T eta).val := by
      clear * - eta heta hAT hAXstrict hXT
      let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
        eta ∈ MissingColors G phi (T.vertex j)
      have hfirst : HierarchyFirstMissingPosition phi T eta =
          if h : candidates.Nonempty then candidates.min' h else Fin.last T.length := rfl
      rw [hfirst]
      by_cases hnon : candidates.Nonempty
      · rw [dite_eq_left hnon]
        have hmem := (Finset.mem_filter.mp (Finset.min'_mem candidates hnon)).2
        by_contra hle
        have hv : (candidates.min' hnon).val ≤ A.length := by omega
        let a : Fin (A.length + 1) := ⟨(candidates.min' hnon).val, by omega⟩
        have ha : Fin.castLE (Nat.succ_le_succ hAT.1) a =
            candidates.min' hnon := Fin.ext rfl
        rw [← ha, hAT.2.1 a] at hmem
        apply heta
        refine Finset.mem_biUnion.mpr ⟨A.vertex a, ?_, hmem⟩
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨a, rfl⟩
      · rw [dite_eq_right hnon]
        simp only [Fin.val_last]
        have := hXT.1
        omega
    have hcUnreserved : c ∉ (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
      intro hcReserved
      obtain ⟨eta, heta, hcGamma⟩ := Finset.mem_biUnion.mp hcReserved
      have hetaNot : eta ∉ TreeMissingColors phi A := by
        rw [lastZero hz]
        exact (Finset.mem_sdiff.mp heta).2
      have hpAfter := firstAfter eta hetaNot
      have hnextLast : (0 : Fin (H.dividerCount + 1)).succ =
          Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
      have hseg : c ∈ HierarchySegmentColors H 0 eta := by
        unfold HierarchySegmentColors
        dsimp only
        rw [hnextLast, H.terminalStage]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, tT, ?_, ?_, hcolOld⟩
        · change base.core.length ≤ tT.val
          rw [← lastZero hz]
          exact le_rfl
        · have ht := tT.isLt
          change A.length < min (HierarchyFirstMissingPosition phi T eta).val T.length
          omega
      exact (Finset.mem_sdiff.mp (C.good.avoidance 0 eta heta hcGamma)).2 hseg
    obtain ⟨i, hi⟩ := T.attaches tT
    let old : Fin (T.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ tT.isLt))
    have holdIn : T.vertex old ∈ TreeSequenceVertexSet A := by
      let a : Fin (A.length + 1) := ⟨i.val, by simpa [tT, tX] using i.isLt⟩
      have ha : Fin.castLE (Nat.succ_le_succ hAT.1) a = old := Fin.ext rfl
      rw [← ha, hAT.2.1 a]
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨a, rfl⟩
    have hnewOut : T.vertex tT.succ ∉ TreeSequenceVertexSet A := by
      intro hv
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨a, ha⟩ := hv
      have he := T.vertex_injective ((hAT.2.1 a).trans ha)
      have hev := congrArg Fin.val he
      have := a.isLt
      change a.val = A.length + 1 at hev
      omega
    have hboundary : T.edge tT ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet A) c := by
      clear * - hi holdIn hnewOut hcolT
      simp only [BoundaryColorEdges, BoundaryEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨⟨T.vertex old, holdIn, T.vertex tT.succ, hnewOut,
        hi.trans Sym2.eq_swap⟩, hcolT⟩
    rw [lastZero hz] at hcmA hboundary
    intro hclosed
    have hcMissing : c ∈ TreeMissingColors sigma base.core \
        (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) :=
      Finset.mem_sdiff.mpr ⟨hcmA, hcUnreserved⟩
    rw [hclosed c hcMissing] at hboundary
    exact Finset.notMem_empty _ hboundary
  · obtain ⟨inputA, ettA, baseA, KA, goodA, hMPA, hkindA,
        hcountA, hcoreA, hclosureA, hstagesA, hgammaA, hminusA⟩ :=
      hretained (by change 0 < H.dividerCount; omega)
    have hpA : ettA.series.data.kind (Fin.last ettA.rounds) =
        some TashkinovExtensionKind.PE := hkindA.trans hp
    have hnot := (goodA.parallelBase hpA).1
    have hzindex : (⟨(0 : Fin (KA.dividerCount + 1)).val, by simp⟩ :
        Fin (H.dividerCount + 1)) = 0 := Fin.ext rfl
    have hzero := hgammaA 0
    dsimp only at hzero
    rw [hzindex] at hzero
    have hunion : (HierarchyStoredColorsAt KA 0).biUnion (goodA.gamma 0) =
        (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
      apply Finset.biUnion_congr hzero.1
      intro eta heta
      exact hzero.2 eta heta
    rw [hcoreA, hunion] at hnot
    exact hnot

private theorem helper_terminalTransfer_696.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k) (X : TreeSequence G e0),
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
      ∀ (t : Fin T.length),
        A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → sigma (T.edge t) = phi (T.edge t)) →
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta) →
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        alpha ∈ C.good.gamma q eta ∨ beta ∈ C.good.gamma q eta →
          (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) ≤ X.length) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core)
      (terminalData :
        corrT.replacementETT.series.data.tree
              (Fin.last corrT.replacementETT.rounds).castSucc =
            Tn ∧
          corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corrT.replacementETT.series.data
                (Fin.last corrT.replacementETT.rounds) =
              Dn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst :=
          Eq.mpr
            (id
              (congrArg
                (fun (_a : TreeSequence G e0) =>
                  TreeSequenceInitialSegment _a
                    (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                hcoreT))
            H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStarredStage K j = HierarchyStarredStage H j) →
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    ∀ (eta c : Fin k),
    eta ∈ HierarchyStoredColorsAt H q →
    c ∈ C.good.gamma q eta →
    c ∈ HierarchySegmentColors K q eta →
    c ∈ HierarchySegmentColors H q eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma X hfixedPrefix hstoredFirst
      hgammaCutoff H q n Tn Dn corrT baseT hcoreT terminalData K starredEq unaffected eta c heta
      hc hseg
  unfold HierarchySegmentColors at hseg ⊢
  dsimp only at hseg ⊢
  have hlast : H.stage q.succ = T := by
    have hi : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    rw [hi, H.terminalStage]
  rw [starredEq q, hlast, hstoredFirst eta heta] at hseg
  rw [hlast]
  obtain ⟨_, t, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hseg
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hlo, hhi, ?_⟩
  by_cases hca : c = alpha
  · subst c
    have hcut := hgammaCutoff eta heta (Or.inl hc)
    have htX : t.val < X.length := by
      have := Nat.lt_of_lt_of_le hhi (Nat.min_le_left _ _)
      omega
    exact (hfixedPrefix t hlo htX).symm.trans hcol
  · by_cases hcb : c = beta
    · subst c
      have hcut := hgammaCutoff eta heta (Or.inr hc)
      have htX : t.val < X.length := by
        have := Nat.lt_of_lt_of_le hhi (Nat.min_le_left _ _)
        omega
      exact (hfixedPrefix t hlo htX).symm.trans hcol
    · exact (unaffected _ c hca hcb).mp hcol

private theorem helper_preStepElementary_566.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (_ : TreeSequence G e0),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let i : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by have this : (0 : ℕ) < ett.rounds := C.positive; omega⟩ :
        Fin ett.rounds);
    ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
      (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx X n Tn
  dsimp only
  by_cases hn : ett.rounds = 1
  · have hcolor : (⟨ett.rounds - 1, by have := C.positive; omega⟩ : Fin ett.rounds).castSucc = 0 :=
      Fin.ext (by simp [hn])
    have htree : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext (by simp [n, hn])
    dsimp only [Tn]
    rw [hcolor, htree]
    exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
  · have hmore : 1 < ett.rounds := by have := C.positive; omega
    obtain ⟨predecessor, hr, hmaximum, _, _⟩ :=
      CertifiedETTPredecessor G k e0 input T phi ett C.maximum hmore
    have htree : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext rfl
    dsimp only [Tn]
    rw [htree]
    exact (ctx.lowerRung predecessor (by omega) (by omega) hmaximum).1

private theorem helper_equalTrees_615.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {S U : TreeSequence G e0},
    TreeSequenceInitialSegment S U →
    S.length = U.length →
    S = U := by
  classical
  intro V E G e0 S U hSU hlen
  cases S with
  | mk ls ps vs es vis eis fs aas =>
    cases U with
    | mk lu pu vu eu viu eiu fu aau =>
      simp only at hlen
      subst lu
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hSU.2.1 i).symm
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hSU.2.2 i).symm

private theorem helper_branch_846.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    TreeSequenceInitialSegment Tn A →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        CombinedStableColoring Tn base.closure Dn phi sigma) →
    ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core),
    baseT.closure = base.closure →
    ∀
      (terminalData :
        corrT.replacementETT.series.data.tree
              (Fin.last corrT.replacementETT.rounds).castSucc =
            Tn ∧
          corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corrT.replacementETT.series.data
                (Fin.last corrT.replacementETT.rounds) =
              Dn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst :=
          Eq.mpr
            (id
              (congrArg
                (fun (_a : TreeSequence G e0) =>
                  TreeSequenceInitialSegment _a
                    (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                hcoreT))
            H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    (4 : ℕ) ≤
      ((TreeMissingColors sigma
              (corrT.replacementETT.series.data.tree
                (Fin.last corrT.replacementETT.rounds).castSucc) ∩
            TreeMissingColors sigma baseT.closure) \
          (HierarchyStoredColorsAt K (0 : Fin (K.dividerCount + (1 : ℕ)))).biUnion
            (C.good.gamma (0 : Fin (K.dividerCount + (1 : ℕ))))).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn TnToA treeMissingEq
      combined corrT baseT hcoreT hclosureT terminalData K storedEq hpOld
  change 4 ≤ ((TreeMissingColors sigma
    (corrT.replacementETT.series.data.tree
      (Fin.last corrT.replacementETT.rounds).castSucc) ∩
    TreeMissingColors sigma baseT.closure) \
      (HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)).card
  have hclosureMissing : TreeMissingColors sigma base.closure =
      TreeMissingColors phi base.closure := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (combined hpOld).2.2
  rw [terminalData.1, hclosureT, storedEq 0, treeMissingEq Tn TnToA,
    hclosureMissing]
  exact (C.good.parallelBase hpOld).2

private theorem helper_continuation_810.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
    sigma = TwoColorComponentSwap G phi alpha beta z →
    ∀ (_ : TreeSequence G e0),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    (∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
        c = alpha ∨ c = beta →
          c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
            TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) { c } →
              OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha
                beta) →
    HierarchyWeaklyStable C.hierarchy (Fin.last C.hierarchy.dividerCount) sigma →
    ModColoring ett sigma →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    TreeSequenceInitialSegment Tn A →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (H.stage j.castSucc) A) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        CombinedStableColoring Tn base.closure Dn phi sigma) →
    ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    MaximumProperty corrT.replacementETT →
    ∀ (baseT : HierarchyBase corrT.replacementETT sigma) (hcoreT : baseT.core = base.core),
    baseT.closure = base.closure →
    ∀
      (terminalData :
        corrT.replacementETT.series.data.tree
              (Fin.last corrT.replacementETT.rounds).castSucc =
            Tn ∧
          corrT.replacementETT.series.data.kind (Fin.last corrT.replacementETT.rounds) =
              ett.series.data.kind n ∧
            TashkinovStoredColors corrT.replacementETT.series.data
                (Fin.last corrT.replacementETT.rounds) =
              Dn),
    let K : TashkinovHierarchy corrT.replacementETT baseT :=
      { dividerCount := H.dividerCount, stage := H.stage,
        baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
        terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
        dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
        dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
        coreInsideFirst :=
          Eq.mpr
            (id
              (congrArg
                (fun (_a : TreeSequence G e0) =>
                  TreeSequenceInitialSegment _a
                    (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                hcoreT))
            H.coreInsideFirst :
        TashkinovHierarchy corrT.replacementETT baseT };
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStarredStage K j = HierarchyStarredStage H j) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j) →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        HierarchyStageMissingColors K j = HierarchyStageMissingColors H j) →
    (∀ (i : Fin H.dividerCount) (eta : Fin k),
        HierarchySegmentColors K i.castSucc eta = HierarchySegmentColors H i.castSucc eta) →
    (∀ (eta c : Fin k),
        eta ∈ HierarchyStoredColorsAt H q →
          c ∈ C.good.gamma q eta →
            c ∈ HierarchySegmentColors K q eta → c ∈ HierarchySegmentColors H q eta) →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        ¬TreeColorSetMinusClosed G sigma base.core
            ((HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
              (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ)))))) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
        ∃ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
          MaximumProperty corrT.replacementETT ∧
            ∃ (baseT : HierarchyBase corrT.replacementETT sigma) (K :
              TashkinovHierarchy corrT.replacementETT baseT) (goodT : GoodHierarchy K),
              SameGoodHierarchy C.good goodT := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne z sigma hsigma X H q A n Tn
      Dn houtside hweak hmod hmissingA TnToA ordinaryToA starredToA treeMissingEq combined corrT
      hmaximumT baseT hcoreT hclosureT terminalData K starredEq storedEq stageMissingEq
      internalSegmentEq terminalTransfer coreNotClosed
  let goodT : GoodHierarchy K := {
    gamma := C.good.gamma
    twoColors := by
      intro j eta heta
      exact C.good.twoColors j eta (by rw [storedEq j] at heta; exact heta)
    avoidance := by
      intro j eta heta c hc
      have hjbound : j.val < H.dividerCount + 1 := j.isLt
      have ho : eta ∈ HierarchyStoredColorsAt H j := by rw [← storedEq j]; exact heta
      have old := C.good.avoidance j eta ho hc
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [stageMissingEq j]; exact (Finset.mem_sdiff.mp old).1
      · intro hseg
        by_cases hj : j.val < H.dividerCount
        · let i : Fin H.dividerCount := ⟨j.val, hj⟩
          have hi : i.castSucc = j := Fin.ext rfl
          rw [← hi, internalSegmentEq i eta, hi] at hseg
          exact (Finset.mem_sdiff.mp old).2 hseg
        · have hjlast : j = q := Fin.ext (by dsimp [q]; omega)
          subst j
          exact (Finset.mem_sdiff.mp old).2 (terminalTransfer eta c ho hc hseg)
    disjointPairs := by
      intro j eta theta heta htheta hne
      exact C.good.disjointPairs j eta theta
        (by rw [storedEq j] at heta; exact heta)
        (by rw [storedEq j] at htheta; exact htheta) hne
    uniqueRefresh := by
      intro a
      have hnew :
          ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
              fun v => MissingColors G sigma v) =
          ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H a.castSucc)).biUnion
              fun v => MissingColors G phi v) := by
        apply Finset.biUnion_congr rfl
        intro v hv
        exact hmissingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA a.succ)
          (Finset.mem_sdiff.mp hv).1)
      change ∃! eta : Fin k,
        eta ∈ HierarchyStoredColorsAt K a.succ ∧
          C.good.gamma a.succ eta ⊆
            ((TreeSequenceVertexSet (H.stage a.succ.castSucc) \
              TreeSequenceVertexSet (HierarchyStarredStage K a.castSucc)).biUnion
                fun v => MissingColors G sigma v) ∧
          ∀ theta ∈ HierarchyStoredColorsAt K a.succ, theta ≠ eta →
            C.good.gamma a.succ theta = C.good.gamma a.castSucc theta
      rw [starredEq a.castSucc, hnew]
      simp only [storedEq]
      exact C.good.uniqueRefresh a
    parallelBase := by
      dsimp only
      intro hp
      have hpOld : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
        terminalData.2.1.symm.trans hp
      constructor
      · change ¬ TreeColorSetMinusClosed G sigma baseT.core
          ((HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0))
        rw [hcoreT, storedEq 0]
        exact coreNotClosed hpOld
      · exact @helper_branch_846 V E inferInstance inferInstance inferInstance inferInstance G k
          e0 input T phi ett base C sigma TnToA treeMissingEq combined corrT baseT hcoreT
          hclosureT terminalData storedEq hpOld
    minusClosed := by
      intro a
      change TreeColorSetMinusClosed G sigma (H.stage a.succ.castSucc)
        ((HierarchyStoredColorsAt K a.succ).biUnion (C.good.gamma a.castSucc))
      rw [storedEq a.succ]
      have hs : HierarchyStarredStage H a.succ = H.stage a.succ.castSucc := rfl
      rw [← hs]
      apply P2813_T1_MinusClosedTransport G k e0 _ phi sigma alpha beta hne z hsigma
        ctx.proper ctx.oneEdgeUncolored _
      · rw [hs]; exact C.good.minusClosed a
      · intro v hv
        exact hmissingA v (TreeSequenceInitialSegmentVertexSetSubset (starredToA a.succ) hv)
      · exact houtside a.succ }
  have same : SameGoodHierarchy C.good goodT := by
    refine ⟨?_, rfl, ?_⟩
    · refine ⟨hcoreT.symm, rfl, HEq.rfl, HEq.rfl, ?_, fun _ => hclosureT.symm⟩
      exact ⟨fun hp => terminalData.2.1.trans hp, fun hp => terminalData.2.1.symm.trans hp⟩
    · intro j
      exact ⟨(storedEq j).symm, fun _ _ => rfl⟩
  exact ⟨hweak, hmod, corrT, hmaximumT, baseT, K, goodT, same⟩

private theorem helper_continuation_777.{u_1, u_2} :
    helperContinuation777Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne z sigma hsigma X
      hfixedPrefix hrouteX hsuffix hsplitMissing hstoredFirst hgammaCutoff H q A n Tn Dn hbase
      hsproper hsone houtside hweak hmod hretained hAX hAXstrict hfixedA hmissingA equalTrees
      lastZero TnToA ordinaryToA starredToA hXT hAT treeMissingEq
  have hsuffixSigma : TashkinovAugmentationSequence sigma X T := by
    rw [hsigma] at hsplitMissing ⊢
    exact TashkinovAugmentationSequenceComponentSwap G k e0 phi alpha beta hne z
      X T hsuffix hsplitMissing.1 hsplitMissing.2
  have fullRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence sigma seed T) := by
    rcases hrouteX with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hseq⟩
    · exact Or.inl ⟨hp, hseq.trans hsuffixSigma⟩
    · exact Or.inr ⟨hp, f, seed, hedges, hseed, hseq.trans hsuffixSigma⟩
  have corrData := @helper_corrData_311 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T phi ett base C sigma X TnToA treeMissingEq
  have combined (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      CombinedStableColoring Tn base.closure Dn phi sigma := by
    change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma) at hbase
    simpa only [hp, ite_true] using hbase
  have fullBase := @helper_fullBase_358 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T phi ett base C ctx sigma hsproper hsone hmod fullRoute corrData combined
  obtain ⟨corrT, hmaximumT, baseT, hcoreT, hclosureT⟩ := fullBase
  have terminalData := corrData corrT
  let K : TashkinovHierarchy corrT.replacementETT baseT := {
    dividerCount := H.dividerCount
    stage := H.stage
    baseStage := H.baseStage.trans terminalData.1.symm
    terminalStage := H.terminalStage
    nested := H.nested
    strict := H.strict
    dividerPosition := H.dividerPosition
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := H.dividerStage
    coreInsideFirst := by rw [hcoreT]; exact H.coreInsideFirst }
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j :=
    Fin.cases hcoreT (fun _ => rfl) j
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [terminalData.2.2, starredEq j, treeMissingEq _ (starredToA j)]
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun a => ?_) j
    · change TreeMissingColors sigma
        (corrT.replacementETT.series.data.tree
          (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
      rw [terminalData.1]
      exact treeMissingEq Tn TnToA
    · exact treeMissingEq _ (ordinaryToA a.succ)
  have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      sigma f = some c ↔ phi f = some c := by
    clear * - G phi sigma alpha beta hne z hsigma f c hca hcb
    rw [hsigma]
    by_cases hf : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
    · by_cases ha : phi f = some alpha
      · simp [TwoColorComponentSwap, hf, ha, hca.symm, hcb.symm]
      · by_cases hb : phi f = some beta
        · simp [TwoColorComponentSwap, hf, hb, hne.symm, hca.symm, hcb.symm]
        · simp [TwoColorComponentSwap, hf, ha, hb]
    · simp [TwoColorComponentSwap, hf]
  have internalSegmentEq (i : Fin H.dividerCount) (eta : Fin k) :
      HierarchySegmentColors K i.castSucc eta =
        HierarchySegmentColors H i.castSucc eta := by
    have hnext := ordinaryToA i.succ
    have hcut := HierarchyFirstMissingPositionPrefixCutoff sigma A T hAT eta
      (H.stage i.castSucc.succ).length (by simpa using hnext.1)
    have htransport := P2813_T1_PrefixSegmentTransport phi sigma
      (H.stage i.castSucc.succ) A T (by simpa using hnext) hAT hfixedA hmissingA
      eta (HierarchyStarredStage H i.castSucc).length
    unfold HierarchySegmentColors
    dsimp only
    rw [starredEq i.castSucc, ← hcut]
    exact htransport
  -- Affected Gamma colors can occur in this range only before X.
  have terminalTransfer := @helper_terminalTransfer_696 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett base C alpha beta sigma X hfixedPrefix
      hstoredFirst hgammaCutoff corrT baseT hcoreT terminalData starredEq unaffected
  have coreNotClosed := @helper_coreNotClosed_479 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C sigma X hfixedPrefix hrouteX hretained hAX
      hAXstrict equalTrees lastZero TnToA hXT hAT
  exact @helper_continuation_810 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx alpha beta hne z sigma hsigma X houtside hweak hmod hmissingA
      TnToA ordinaryToA starredToA treeMissingEq combined corrT hmaximumT baseT hcoreT hclosureT
      terminalData starredEq storedEq stageMissingEq internalSegmentEq terminalTransfer
      coreNotClosed
theorem StableChangeCasesOneTwoSplitTail {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      alpha ∈ TreeMissingColors phi
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) ∧
        beta ∈ TreeMissingColors phi
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)))
    (z : Sum V E) (hpath : TwoColorPathComponent G phi alpha beta z)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hcase :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq) ∨
        (H.dividerCount = 0 ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            (alpha ∈ TreeMissingColors phi A ∧
              alpha ∉ Dn ∧ beta ∉ Dn))))
    (hdisjoint :
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va)))
    (X : TreeSequence G e0)
    (hAX :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      TreeSequenceInitialSegment A X)
    (hAXstrict :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      A.length < X.length)
    (hXB : TreeSequenceInitialSegment X
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)))
    (hfixedPrefix :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        sigma (T.edge t) = phi (T.edge t))
    (hrouteX :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn X) ∨
        ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence sigma seed X))
    (hsuffix : TashkinovAugmentationSequence phi X T)
    (hsplitMissing : alpha ∈ TreeMissingColors sigma X ∧
      beta ∈ TreeMissingColors sigma X)
    (hpenultimateMissing :
      ∀ v, v ∈ TreeSequenceVertexSet
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) →
        MissingColors G sigma v = MissingColors G phi v)
    (hstoredFirst :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta)
    (hgammaCutoff :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
        (alpha ∈ C.good.gamma q eta ∨ beta ∈ C.good.gamma q eta) →
          (HierarchyFirstMissingPosition phi T eta).val ≤ X.length) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
        ∃ corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
          MaximumProperty corrT.replacementETT ∧
            ∃ baseT : HierarchyBase corrT.replacementETT sigma,
              ∃ K : TashkinovHierarchy corrT.replacementETT baseT,
                ∃ goodT : GoodHierarchy K, SameGoodHierarchy C.good goodT := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  have hB : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi
      ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have controls := P2813_T1_BaseControl G k e0 input T phi ett base C ctx
    hB alpha beta hne hmissingPrefix z hpath sigma hsigma hcase hdisjoint
  obtain ⟨hbase, _, hsproper, hsone, houtside⟩ := controls
  have preStepElementary := @helper_preStepElementary_566 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett base C ctx X
  have hfixedA := P2813_T1_DisplayedEdges G k e0 input T phi ett base H C.good
    ctx.proper ctx.oneEdgeUncolored preStepElementary hB alpha beta z sigma hsigma
    hsone hbase houtside
  have changed := StableChangeCasesOneTwo G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hB ctx.largeMissingSet alpha beta hne
    hmissingPrefix z hpath sigma hsigma hcase hdisjoint
  obtain ⟨hweak, hmod, _, hretained⟩ := changed
  change TreeSequenceInitialSegment A X at hAX
  change A.length < X.length at hAXstrict
  change TreeSequenceInitialSegment X B at hXB
  change (∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t)) at hfixedA
  have hmissingA : ∀ v ∈ TreeSequenceVertexSet A,
      MissingColors G sigma v = MissingColors G phi v := by
    intro v hv
    exact hpenultimateMissing v (TreeSequenceInitialSegmentVertexSetSubset hXB
      (TreeSequenceInitialSegmentVertexSetSubset hAX hv))
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) : TreeSequenceInitialSegment S W := by
    refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
  have equalTrees := @helper_equalTrees_615 V E G e0
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    induction d with
    | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    simp [A, q, HierarchyStarredStage, hz, Fin.last]
  have lastPositive (hz : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · have hv := congrArg Fin.val hzero
      simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, q] at hv
      exact (hz hv).elim
    · simp only [A, HierarchyStarredStage, hi, Fin.cases_succ]
      congr 1
      apply Fin.ext
      have hv := congrArg Fin.val hi
      simpa [q] using hv.symm
  have coreToA : TreeSequenceInitialSegment base.core A := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]; exact segRefl _
    · rw [lastPositive hz]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      simpa [he] using segTrans H.coreInsideFirst hs
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (Classical.choice (base.parallel hp).2.2).leftSegment
    · rw [base.nonparallel hp]; exact segRefl _
  have TnToA := segTrans TnToCore coreToA
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    by_cases hz : H.dividerCount = 0
    · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp; omega)
      rw [hj, H.baseStage]; exact TnToA
    · have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
      rw [lastPositive hz]
      convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;>
      simp only [Fin.val_castSucc]; omega
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A :=
    Fin.cases coreToA (fun i => ordinaryToA i.succ) j
  have hXT : TreeSequenceInitialSegment X T :=
    TashkinovAugmentationSequenceInitialSegment phi X T hsuffix
  have hAT := segTrans hAX hXT
  have treeMissingEq (S : TreeSequence G e0) (hSA : TreeSequenceInitialSegment S A) :
      TreeMissingColors sigma S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl
      (fun v hv => hmissingA v (TreeSequenceInitialSegmentVertexSetSubset hSA hv))
  -- Transport the suffix route without fixing its individual edge colors.
  exact @helper_continuation_777 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx alpha beta hne z sigma hsigma X hfixedPrefix hrouteX hsuffix
      hsplitMissing hstoredFirst hgammaCutoff hbase hsproper hsone houtside hweak hmod hretained
      hAX hAXstrict hfixedA hmissingA equalTrees lastZero TnToA ordinaryToA starredToA hXT hAT
      treeMissingEq
end GoldbergSeymour

end
