/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SplitSwapData
public import LeanPool.GoldbergSeymour.GoodHierarchyTerminalPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyLEMStable
public import LeanPool.GoldbergSeymour.GoodHierarchySameDividerTransport
public import LeanPool.GoldbergSeymour.GoodHierarchySameDividerReconstruction
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTransTrees

/-!
# P2880_T1_Outside Prefix Branch

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable abbrev helperCorrMX773.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [inst : Fintype V] →
  [inst_1 : Fintype E] →
  [inst_2 : DecidableEq V] →
  [inst_3 : DecidableEq E] →
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
  let X : TreeSequence G e0 :=
    HierarchyFullTailPrefix C
      (HierarchyPathNumber C.hierarchy - (1 : ℕ));
  let m :
    ExtendedTashkinovTree G k e0
      P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  (ettX :
      ExtendedTashkinovTree G k e0
        P.corresponding.replacementInput X P.coloring) →
  ettX.rounds = m.rounds →
  ettX.series ≍ m.series →
  let seriesCast :
    TashkinovSeries G k
      P.corresponding.replacementETT.rounds e0
      P.corresponding.replacementInput :=
    @Eq.rec Nat
      (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0 input T phi ett)
      (fun (x : Nat)
          (_ :
            @Eq Nat
              (@ExtendedTashkinovTree.rounds V E inst
                inst_1 inst_3 G k e0 input T phi ett)
              x) ↦
        @TashkinovSeries V E inst inst_1 inst_3 G k x e0
          (@CorrespondingExtendedTashkinovTree.replacementInput
            V E inst inst_1 inst_3 G k e0 input T phi
            ett
            (@HierarchyReplacementPresentation.coloring
              V E inst inst_1 inst_2 inst_3 G k e0 input
              T phi ett base C ctx P)
            T
            (@HierarchyReplacementPresentation.corresponding
              V E inst inst_1 inst_2 inst_3 G k e0 input
              T phi ett base C ctx P)))
      (@CorrespondingExtendedTashkinovTree.replacementSeries
        V E inst inst_1 inst_3 G k e0 input T phi ett
        (@HierarchyReplacementPresentation.coloring V E
          inst inst_1 inst_2 inst_3 G k e0 input T phi
          ett base C ctx P)
        T
        (@HierarchyReplacementPresentation.corresponding
          V E inst inst_1 inst_2 inst_3 G k e0 input T
          phi ett base C ctx P))
      (@ExtendedTashkinovTree.rounds V E inst inst_1
        inst_3 G k e0
        (@CorrespondingExtendedTashkinovTree.replacementInput
          V E inst inst_1 inst_3 G k e0 input T phi ett
          (@HierarchyReplacementPresentation.coloring V
            E inst inst_1 inst_2 inst_3 G k e0 input T
            phi ett base C ctx P)
          T
          (@HierarchyReplacementPresentation.corresponding
            V E inst inst_1 inst_2 inst_3 G k e0 input T
            phi ett base C ctx P))
        T
        (@HierarchyReplacementPresentation.coloring V E
          inst inst_1 inst_2 inst_3 G k e0 input T phi
          ett base C ctx P)
        (@CorrespondingExtendedTashkinovTree.replacementETT
          V E inst inst_1 inst_3 G k e0 input T phi ett
          (@HierarchyReplacementPresentation.coloring V
            E inst inst_1 inst_2 inst_3 G k e0 input T
            phi ett base C ctx P)
          T
          (@HierarchyReplacementPresentation.corresponding
            V E inst inst_1 inst_2 inst_3 G k e0 input T
            phi ett base C ctx P)))
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        have := P.corresponding.rungAgreement
        simp_all only);
  m.series = seriesCast →
  (∀ {r s : ℕ} (h : r = s)
      (ser :
        TashkinovSeries G k s e0
          P.corresponding.replacementInput)
      (i : Fin (r + (1 : ℕ))),
      (@Eq.rec Nat s
              (fun (x : Nat) (_ : @Eq Nat s x) ↦
                @TashkinovSeries V E inst inst_1
                  inst_3 G k x e0
                  (@CorrespondingExtendedTashkinovTree.replacementInput
                    V E inst inst_1 inst_3 G k e0
                    input T phi ett
                    (@HierarchyReplacementPresentation.coloring
                      V E inst inst_1 inst_2 inst_3 G
                      k e0 input T phi ett base C ctx
                      P)
                    T
                    (@HierarchyReplacementPresentation.corresponding
                      V E inst inst_1 inst_2 inst_3 G
                      k e0 input T phi ett base C ctx
                      P)))
              ser r
              (@Eq.symm Nat r s h)).data.coloring
          i =
        ser.data.coloring
          (Fin.cast
            (congrArg (fun (z : ℕ) ↦ z + (1 : ℕ)) h)
            i)) →
  CorrespondingExtendedTashkinovTree G k e0 m
    P.coloring X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P X m ettX hroundX hseriesX seriesCast
      hsourceSeries castColor
  exact {
    replacementInput := P.corresponding.replacementInput
    replacementSeries := m.series
    replacementETT := ettX
    rungAgreement := hroundX
    seriesPresentation := hseriesX
    finalGeneratingColoring := m.generatingColoring
    ladderTreesAgree := by intro i; rfl
    storedColorsAgree := by intro i; rfl
    connectingEdgesAgree := by intro i; rfl
    extensionKindsAgree := by intro i; rfl
    replacementProper := by
      intro i
      rw [hsourceSeries]
      rw [castColor P.corresponding.rungAgreement
        P.corresponding.replacementSeries i]
      exact P.corresponding.replacementProper
        (Fin.cast (congrArg (fun r => r + 1)
          P.corresponding.rungAgreement) i)
    replacementOneUncolored := by
      intro i
      rw [hsourceSeries]
      rw [castColor P.corresponding.rungAgreement
        P.corresponding.replacementSeries i]
      exact P.corresponding.replacementOneUncolored
        (Fin.cast (congrArg (fun r => r + 1)
          P.corresponding.rungAgreement) i)
    replacementStable := by
      intro i
      constructor
      · intro f hf h
        rfl
      · intro v hv
        rfl }

private abbrev helperContinuation1640Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (sigma :
        PartialEdgeColoring E k),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring) (HX : TashkinovHierarchy ettX baseX) (hcountX :
        HX.dividerCount = H.dividerCount) (hstagesX :
    ∀ (j : Fin (HX.dividerCount + (1 : ℕ))), HX.stage j.castSucc = H.stage (Fin.cast (
    by omega
    ) j).castSucc ∧ HierarchyStarredStage HX j = HierarchyStarredStage H (Fin.cast (
    by omega
    ) j)) (hpositionsX :
    ∀ (i : Fin HX.dividerCount), (↑(HX.dividerPosition i) : ℕ) = (↑(H.dividerPosition (Fin.cast
        hcountX i)) : ℕ)) (goodX : GoodHierarchy HX) (hcolorsX :
    ∀ (j : Fin (HX.dividerCount + (1 : ℕ))), HierarchyStoredColorsAt HX j =
        HierarchyStoredColorsAt H (Fin.cast (congrArg (fun n : ℕ => n + 1) hcountX) j) ∧
        HierarchyStageMissingColors HX j = HierarchyStageMissingColors H (Fin.cast (congrArg (fun
        n : ℕ => n + 1) hcountX) j) ∧
    ∀ (eta : Fin k), goodX.gamma j eta = P.counterexample.good.gamma (Fin.cast (congrArg (fun n :
        ℕ => n + 1) hcountX) j) eta ∧ HierarchySegmentColors HX j eta ⊆ HierarchySegmentColors H
        (Fin.cast (congrArg (fun n : ℕ => n + 1) hcountX) j) eta) (corrPrefix :
        CorrespondingExtendedTashkinovTree G k e0 m sigma X) (basePrefix : HierarchyBase
        corrPrefix.replacementETT sigma) (KPrefix : TashkinovHierarchy corrPrefix.replacementETT
        basePrefix) (goodPrefix : GoodHierarchy KPrefix) (samePrefix : SameGoodHierarchy goodX
        goodPrefix) (corrFull : CorrespondingExtendedTashkinovTree G k e0 m sigma T) (hmaximumFull
        : MaximumProperty corrFull.replacementETT) (baseFull : HierarchyBase
        corrFull.replacementETT sigma) (KFull : TashkinovHierarchy corrFull.replacementETT
        baseFull) (hsameFull : SameHierarchyStages H KFull) (Ktransport : TashkinovHierarchy
        corrFull.replacementETT baseFull) (hcountTransport : Ktransport.dividerCount =
        KPrefix.dividerCount) (hstagesTransport :
    ∀ (j : Fin (Ktransport.dividerCount + (1 : ℕ))),
    have jo : Fin (KPrefix.dividerCount + (1 : ℕ)) := Fin.cast (
    by omega
    ) j; Ktransport.stage j.castSucc = KPrefix.stage jo.castSucc ∧ HierarchyStarredStage
        Ktransport j = HierarchyStarredStage KPrefix jo ∧ HierarchyStoredColorsAt Ktransport j =
        HierarchyStoredColorsAt KPrefix jo ∧ HierarchyStageMissingColors Ktransport j =
        HierarchyStageMissingColors KPrefix jo) (hpositionsTransport :
    ∀ (i : Fin Ktransport.dividerCount), (↑(Ktransport.dividerPosition i) : ℕ) =
        (↑(KPrefix.dividerPosition (Fin.cast hcountTransport i)) : ℕ)) (goodFull : GoodHierarchy
        Ktransport) (hsamePrefixFull :
    ∀ (j : Fin (Ktransport.dividerCount + (1 : ℕ))),
    have jo : Fin (KPrefix.dividerCount + (1 : ℕ)) := Fin.cast (
    by omega
    ) j;
    ∀ (eta : Fin k), goodFull.gamma j eta = goodPrefix.gamma jo eta),
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 P.corresponding.replacementETT sigma T),
        MaximumProperty corr.replacementETT ∧
    ∃ (newBase : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT newBase) (good : GoodHierarchy K), SameGoodHierarchy
        P.counterexample.good good

private abbrev helperContinuation1844Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k) (S : P2880_T1_SplitSwapData G k e0 input T phi ett base
        C ctx P alpha beta sigma),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring) (hcoreX : baseX.core = P.replacementBase.core) (hclosureX :
        baseX.closure = P.replacementBase.closure) (HX : TashkinovHierarchy ettX baseX) (hcountX :
        HX.dividerCount = H.dividerCount) (hstagesX :
    ∀ (j : Fin (HX.dividerCount + (1 : ℕ))), HX.stage j.castSucc = H.stage (Fin.cast (
    by omega
    ) j).castSucc ∧ HierarchyStarredStage HX j = HierarchyStarredStage H (Fin.cast (
    by omega
    ) j)) (hpositionsX :
    ∀ (i : Fin HX.dividerCount), (↑(HX.dividerPosition i) : ℕ) = (↑(H.dividerPosition (Fin.cast
        hcountX i)) : ℕ)) (goodX : GoodHierarchy HX) (hcolorsX :
    ∀ (j : Fin (HX.dividerCount + (1 : ℕ))), HierarchyStoredColorsAt HX j =
        HierarchyStoredColorsAt H (Fin.cast (congrArg (fun n : ℕ => n + 1) hcountX) j) ∧
        HierarchyStageMissingColors HX j = HierarchyStageMissingColors H (Fin.cast (congrArg (fun
        n : ℕ => n + 1) hcountX) j) ∧
    ∀ (eta : Fin k), goodX.gamma j eta = P.counterexample.good.gamma (Fin.cast (congrArg (fun n :
        ℕ => n + 1) hcountX) j) eta ∧ HierarchySegmentColors HX j eta ⊆ HierarchySegmentColors H
        (Fin.cast (congrArg (fun n : ℕ => n + 1) hcountX) j) eta) (hsigmaProper :
        IsProperEdgeColoring G sigma) (hsigmaOne : IsOneEdgeUncolored sigma e0) (hstableX :
        StableColoring X (TashkinovStoredColors ettX.series.data (Fin.last ettX.rounds))
        P.coloring sigma),
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors m.series.data n;
    ∀ (hstableTn : StableColoring Tn Dn P.coloring sigma) (hmod : ModColoring m sigma) (hroute :
        m.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        sigma Tn T ∨ (m.series.data.kind n = some TashkinovExtensionKind.SE ∨ m.series.data.kind n
        = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), m.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T) (hNT :
        TreeSequenceInitialSegment Tn T) (hNstrict : Tn.length < T.length) (corrPrefix :
        CorrespondingExtendedTashkinovTree G k e0 m sigma X) (basePrefix : HierarchyBase
        corrPrefix.replacementETT sigma) (KPrefix : TashkinovHierarchy corrPrefix.replacementETT
        basePrefix) (goodPrefix : GoodHierarchy KPrefix) (samePrefix : SameGoodHierarchy goodX
        goodPrefix) (hkindX : ettX.series.data.kind (Fin.last ettX.rounds) = m.series.data.kind
        n),
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 P.corresponding.replacementETT sigma T),
        MaximumProperty corr.replacementETT ∧
    ∃ (newBase : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT newBase) (good : GoodHierarchy K), SameGoodHierarchy
        P.counterexample.good good

private theorem helper_hrecolorX_82.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k), P2880_T1_SplitSwapData G k e0 input T phi ett base C
        ctx P alpha beta sigma →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ)); OutsideKempeRecoloring X P.coloring sigma alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S X
  refine ⟨S.distinct, {Sum.inl (T.vertex (Fin.last T.length))}, ?_, ?_⟩
  · intro z hz v hv
    simp only [Finset.mem_singleton] at hz
    subst z
    intro hvX
    exact S.splitOutside v hvX hv
  · intro f
    have hswap := S.swapped
    rw [hswap]
    simp [TwoColorComponentSwap]

private theorem helper_segmentTrans_194.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B
        C → TreeSequenceInitialSegment A C := by
  classical
  intro V E G e0 A B C hAB hBC
  rcases hAB with ⟨hab, hvab, heab⟩
  rcases hBC with ⟨hbc, hvbc, hebc⟩
  refine ⟨le_trans hab hbc, ?_, ?_⟩
  · intro i
    calc
      C.vertex (Fin.castLE (Nat.succ_le_succ hbc)
          (Fin.castLE (Nat.succ_le_succ hab) i)) =
          B.vertex (Fin.castLE (Nat.succ_le_succ hab) i) :=
        hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
      _ = A.vertex i := hvab i
  · intro i
    calc
      C.edge (Fin.castLE hbc (Fin.castLE hab i)) = B.edge (Fin.castLE hab i) :=
        hebc _
      _ = A.edge i := heab i

private theorem helper_hTnCore_213.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
  let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc;
  TreeSequenceInitialSegment Tn P.replacementBase.core := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P m n Tn
  by_cases hpe : m.series.data.kind n = some TashkinovExtensionKind.PE
  · obtain ⟨_, _, ⟨u⟩⟩ := P.replacementBase.parallel hpe
    exact u.leftSegment
  · rw [P.replacementBase.nonparallel hpe]
    exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩

private theorem helper_hstableTn_223.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k), P2880_T1_SplitSwapData G k e0 input T phi ett base C
        ctx P alpha beta sigma →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring),
        StableColoring X (TashkinovStoredColors ettX.series.data (Fin.last ettX.rounds))
        P.coloring sigma →
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors m.series.data n; TreeSequenceVertexSet Tn ⊆
        TreeSequenceVertexSet X → StableColoring Tn Dn P.coloring sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S X m ettX hstableX n Tn
      Dn hTnXvertices
  constructor
  · intro f hf hcontrol
    rcases hf with ⟨v, hv, hinc⟩
    exact S.incidentFixed v (hTnXvertices hv) f hinc
  · intro v hv
    exact hstableX.2 v (hTnXvertices hv)

private theorem helper_hroute_241.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k), P2880_T1_SplitSwapData G k e0 input T phi ett base C
        ctx P alpha beta sigma →
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc; m.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence sigma Tn T ∨ (m.series.data.kind
        n = some TashkinovExtensionKind.SE ∨ m.series.data.kind n = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), m.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S m n Tn
  rcases S.prefixRoute with hp | hs
  · left
    refine ⟨hp.1, ?_⟩
    exact Relation.ReflTransGen.trans hp.2 S.newSuffix
  · right
    refine ⟨hs.1, ?_⟩
    obtain ⟨f, seed, hconn, hadjoin, hseq⟩ := hs.2
    exact ⟨f, seed, hconn, hadjoin,
      Relation.ReflTransGen.trans hseq S.newSuffix⟩

private theorem helper_hNT_259.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring) (_ : TashkinovHierarchy ettX baseX),
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc; TreeSequenceInitialSegment Tn T
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P X m ettX baseX HX n Tn
  have hi : (⟨m.rounds, by omega⟩ : Fin (m.rounds + 2)) = n.castSucc := by
    apply Fin.ext
    rfl
  change TreeSequenceInitialSegment
    (m.series.data.tree n.castSucc) T
  rw [← hi]
  exact m.abovePenultimate

private theorem helper_hNstrict_267.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring) (_ : TashkinovHierarchy ettX baseX),
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc; Tn.length < T.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P X m ettX baseX HX n Tn
  have hi : (⟨m.rounds, by omega⟩ : Fin (m.rounds + 2)) = n.castSucc := by
    apply Fin.ext
    rfl
  change (m.series.data.tree n.castSucc).length < T.length
  rw [← hi]
  exact m.strictAbovePenultimate

private theorem helper_hkindX_358.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring),
        ettX.rounds = m.rounds → ettX.series ≍ m.series →
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds; ettX.series.data.kind (Fin.last
        ettX.rounds) = m.series.data.kind n := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P X m ettX hroundX hseriesX n
  let seriesCastX := hroundX ▸ ettX.series
  have hcastX : HEq seriesCastX ettX.series := by
    have typeLink := congrArg (fun r => TashkinovSeries G k r e0
      P.corresponding.replacementInput) hroundX
    simp [seriesCastX]
  have heqX : seriesCastX = m.series := eq_of_heq (HEq.trans hcastX hseriesX)
  have hkind := congrArg
    (fun s : TashkinovSeries G k m.rounds e0
      P.corresponding.replacementInput => s.data.kind n) heqX
  have castKind {r s : ℕ} (h : r = s)
      (ser : TashkinovSeries G k r e0 P.corresponding.replacementInput)
      (i : Fin (s + 1)) :
      (h ▸ ser).data.kind i =
        ser.data.kind (Fin.cast (congrArg (fun z => z + 1) h.symm) i) := by
    cases h
    rfl
  have hindex : Fin.cast (congrArg (fun z => z + 1) hroundX.symm) n =
      Fin.last ettX.rounds := by
    apply Fin.ext
    simp [n]
  have hkindCast : seriesCastX.data.kind n =
      ettX.series.data.kind (Fin.last ettX.rounds) := by
    rw [castKind hroundX ettX.series n, hindex]
  exact hkindCast.symm.trans hkind

private theorem helper_branch_392.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k), P2880_T1_SplitSwapData G k e0 input T phi ett base C
        ctx P alpha beta sigma →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring), baseX.closure = P.replacementBase.closure →
    ∀ (HX : TashkinovHierarchy ettX baseX) (goodX : GoodHierarchy HX), IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 → StableColoring X (TashkinovStoredColors
        ettX.series.data (Fin.last ettX.rounds)) P.coloring sigma →
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors m.series.data n; StableColoring Tn Dn
        P.coloring sigma → (m.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T ∨ (m.series.data.kind n = some
        TashkinovExtensionKind.SE ∨ m.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), m.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T) →
    ∀ (corrPrefix : CorrespondingExtendedTashkinovTree G k e0 m sigma X) (basePrefix :
        HierarchyBase corrPrefix.replacementETT sigma) (KPrefix : TashkinovHierarchy
        corrPrefix.replacementETT basePrefix) (goodPrefix : GoodHierarchy KPrefix),
        SameGoodHierarchy goodX goodPrefix → ettX.series.data.kind (Fin.last ettX.rounds) =
        m.series.data.kind n → m.series.data.kind n = some TashkinovExtensionKind.PE →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T), MaximumProperty
        corr.replacementETT ∧
    ∃ (newBase : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT newBase), newBase.closure = basePrefix.closure ∧ SameHierarchyStages H
        K := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S X m H ettX baseX
      hclosureX HX goodX hsigmaProper hsigmaOne hstableX n Tn Dn hstableTn hroute corrPrefix
      basePrefix KPrefix goodPrefix samePrefix hkindX hpe
  rcases hroute with ⟨_, hbuilt⟩ | hnonpe
  · have hbaseParallel := P.replacementBase.parallel hpe
    rcases hbaseParallel with ⟨_, _, ⟨union⟩⟩
    have hcoreVertices :
        TreeSequenceVertexSet P.replacementBase.core ⊆
          TreeSequenceVertexSet X :=
      TreeSequenceInitialSegmentVertexSetSubset S.coreInSplit
    have hclosureVertices :
        TreeSequenceVertexSet P.replacementBase.closure ⊆
          TreeSequenceVertexSet X := by
      intro v hv
      apply hcoreVertices
      rw [union.vertexSet]
      exact Finset.mem_union_right _ hv
    have hcombined : CombinedStableColoring Tn
        P.replacementBase.closure Dn P.coloring sigma := by
      constructor
      · exact hstableTn
      · constructor
        · intro f hf _
          rcases hf with ⟨v, hv, hinc⟩
          exact S.incidentFixed v (hclosureVertices hv) f hinc
        · intro v hv
          exact hstableX.2 v (hclosureVertices hv)
    have hsplit := HierarchySplitter G k e0
      P.corresponding.replacementInput T P.coloring sigma m P.maximum
      P.counterexample.positive P.minimumContext.lowerRung
      P.replacementBase H hpe P.minimumContext.proper
      P.minimumContext.oneEdgeUncolored hsigmaProper hsigmaOne
      hcombined hbuilt
    rcases hsplit with ⟨corr, hmaximum, newBase, K, hsame⟩
    have hclosure : newBase.closure = basePrefix.closure := by
      have hclFull := hsame.2.2.2.2.2 hpe
      have hclPrefix := samePrefix.1.2.2.2.2.2 (hkindX.trans hpe)
      exact hclFull.symm.trans (hclosureX.symm.trans hclPrefix)
    exact ⟨corr, hmaximum, newBase, K, hclosure, hsame⟩
  · rcases hnonpe.1 with hse | hre
    · have heq : some TashkinovExtensionKind.SE =
          some TashkinovExtensionKind.PE := hse.symm.trans hpe
      cases heq
    · have heq : some TashkinovExtensionKind.RE =
          some TashkinovExtensionKind.PE := hre.symm.trans hpe
      cases heq

private theorem helper_hseries_463.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (sigma :
        PartialEdgeColoring E k),
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T),
    let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
        corr.replacementInput := cast (congrArg (fun (r : ℕ) ↦ TashkinovSeries G k r e0
        corr.replacementInput) (
    by
          have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    )) corr.replacementSeries; corr.replacementETT.series = replacementSeries := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P sigma m corr replacementSeries
  exact ((cast_eq_iff_heq
    (e := congrArg (fun r => TashkinovSeries G k r e0
      corr.replacementInput) corr.rungAgreement.symm)
    (a := corr.replacementSeries)
    (a' := corr.replacementETT.series)).2
    corr.seriesPresentation.symm).symm

private theorem helper_hkindEq_493.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (sigma :
        PartialEdgeColoring E k),
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T),
    let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
        corr.replacementInput := cast (congrArg (fun (r : ℕ) ↦ TashkinovSeries G k r e0
        corr.replacementInput) (
    by
          have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    )) corr.replacementSeries; (
    ∀ {a b : ℕ} (h : a = b) (s : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (cast (congrArg (fun (r : ℕ) ↦ TashkinovSeries G k r e0 corr.replacementInput) h)
        s).data.kind i = s.data.kind (Fin.cast (
    by omega
    ) i)) → corr.replacementETT.series = replacementSeries →
    ∀ (i : Fin (corr.replacementETT.rounds + (1 : ℕ))), corr.replacementETT.series.data.kind i =
        m.series.data.kind (Fin.cast (
    by
          have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) i) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P sigma m corr replacementSeries castKind
      hseries i
  rw [hseries]
  exact (castKind corr.rungAgreement.symm corr.replacementSeries i).trans
    (corr.extensionKindsAgree
      (Fin.cast (congrArg (fun r => r + 1) corr.rungAgreement) i))

private theorem helper_hkindP_512.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds; m.series.data.kind n = some
        TashkinovExtensionKind.SE ∨ m.series.data.kind n = some TashkinovExtensionKind.RE →
        m.series.data.kind (Fin.last m.rounds) ≠ some TashkinovExtensionKind.PE := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P m n hkind hp
  rcases hkind with hse | hre
  · rw [hp] at hse
    cases hse
  · rw [hp] at hre
    cases hre

private theorem helper_branch_667.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k), P2880_T1_SplitSwapData G k e0 input T phi ett base C
        ctx P alpha beta sigma →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    ∀ (corrPrefix : CorrespondingExtendedTashkinovTree G k e0 m sigma X) (basePrefix :
        HierarchyBase corrPrefix.replacementETT sigma) (KPrefix : TashkinovHierarchy
        corrPrefix.replacementETT basePrefix) (goodPrefix : GoodHierarchy KPrefix),
    ∀ eta ∈ HierarchyStoredColorsAt KPrefix (Fin.last KPrefix.dividerCount),
    let _ : Fin (KPrefix.dividerCount + (1 : ℕ)) := Fin.last KPrefix.dividerCount; eta ∈
        HierarchyStoredColorsAt H q →
    ∀ ⦃c : Fin k⦄, c ∈ goodPrefix.gamma (Fin.last KPrefix.dividerCount) eta →
    ∀ (r : Fin T.length), (HierarchyStarredStage KPrefix (Fin.last KPrefix.dividerCount)).length ≤
        (↑r : ℕ) → (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition sigma T eta) : ℕ) T.length →
        sigma (T.edge r) = some c → alpha ∈ P.counterexample.good.gamma q eta ∨ beta ∈
        P.counterexample.good.gamma q eta → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S X m H q corrPrefix
      basePrefix KPrefix goodPrefix eta heta qP hstoreOld c hcG r hlo hhi hcol haffected
  have hcut := S.gammaCutoff eta hstoreOld haffected
  have hfirst := S.storedFirst eta hstoreOld
  have hrX : r.val < X.length := by
    have hlt := (lt_min_iff.mp hhi).1
    have hle : (HierarchyFirstMissingPosition sigma T eta).val ≤ X.length := by
      rw [hfirst]
      exact hcut
    exact lt_of_lt_of_le hlt hle
  have hprefixCut := HierarchyFirstMissingPositionPrefixCutoff sigma X T
    S.splitInFull eta X.length le_rfl
  let rX : Fin X.length := ⟨r.val, hrX⟩
  have hidx : (Fin.castLE (by have hlen := S.splitInFull.1; omega) rX) = r := by
    apply Fin.ext
    rfl
  have hedge : T.edge r = X.edge rX := by
    have he := S.splitInFull.2.2 rX
    rw [hidx] at he
    exact he.symm
  have hhiX : r.val < min (HierarchyFirstMissingPosition sigma X eta).val X.length := by
    rw [hprefixCut]
    exact (lt_min_iff).2 ⟨(lt_min_iff.mp hhi).1, hrX⟩
  have hsegX : c ∈ HierarchySegmentColors KPrefix qP eta := by
    unfold HierarchySegmentColors
    have hterm : KPrefix.stage qP.succ = X := by
      simpa [qP] using KPrefix.terminalStage
    rw [hterm]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨rX, ?_, hhiX, ?_⟩
    · simpa [rX, qP] using hlo
    · rw [← hedge]
      exact hcol
  have havo := goodPrefix.avoidance qP eta heta hcG
  exact (Finset.mem_sdiff.mp havo).2 hsegX

private theorem helper_branch_700.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k), P2880_T1_SplitSwapData G k e0 input T phi ett base C
        ctx P alpha beta sigma →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    ∀ (corrPrefix : CorrespondingExtendedTashkinovTree G k e0 m sigma X) (basePrefix :
        HierarchyBase corrPrefix.replacementETT sigma) (KPrefix : TashkinovHierarchy
        corrPrefix.replacementETT basePrefix) (goodPrefix : GoodHierarchy KPrefix) (eta : Fin k),
    let qP : Fin (KPrefix.dividerCount + (1 : ℕ)) := Fin.last KPrefix.dividerCount; eta ∈
        HierarchyStoredColorsAt H q → P.counterexample.good.gamma q eta = goodPrefix.gamma qP eta
        → HierarchyStarredStage KPrefix qP = HierarchyStarredStage H q →
    ∀ ⦃c : Fin k⦄, c ∈ goodPrefix.gamma (Fin.last KPrefix.dividerCount) eta →
    ∀ (r : Fin T.length), (HierarchyStarredStage KPrefix (Fin.last KPrefix.dividerCount)).length ≤
        (↑r : ℕ) → (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition sigma T eta) : ℕ) T.length →
        sigma (T.edge r) = some c → ¬(alpha ∈ P.counterexample.good.gamma q eta ∨ beta ∈
        P.counterexample.good.gamma q eta) → False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S X m H q corrPrefix
      basePrefix KPrefix goodPrefix eta qP hstoreOld hgammaOldPrefix hstarOld c hcG r hlo hhi
      hcol haffected
  have hgammaMem : c ∈ P.counterexample.good.gamma q eta := by
    rw [hgammaOldPrefix]
    exact hcG
  have hcnotAlpha : c ≠ alpha := by
    intro he
    apply haffected
    exact Or.inl (he ▸ hgammaMem)
  have hcnotBeta : c ≠ beta := by
    intro he
    apply haffected
    exact Or.inr (he ▸ hgammaMem)
  have hcolOld : P.coloring (T.edge r) = some c := by
    rw [S.swapped] at hcol
    unfold TwoColorComponentSwap at hcol
    split_ifs at hcol with hmem ha hb
    · exact False.elim (hcnotBeta (Option.some.inj hcol).symm)
    · exact False.elim (hcnotAlpha (Option.some.inj hcol).symm)
    · exact hcol
    · exact hcol
  have hltOld : r.val < (HierarchyFirstMissingPosition P.coloring T eta).val := by
    have hlt := (lt_min_iff.mp hhi).1
    rw [S.storedFirst eta hstoreOld] at hlt
    exact hlt
  have hsegOld : c ∈ HierarchySegmentColors H q eta := by
    unfold HierarchySegmentColors
    have hterm : H.stage q.succ = T := by
      convert H.terminalStage using 1
      apply congrArg H.stage
      apply Fin.ext
      simp [q]
    rw [hterm]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨r, ?_, ?_, hcolOld⟩
    · rw [← hstarOld]
      exact hlo
    · exact (lt_min_iff.mpr ⟨hltOld, r.isLt⟩)
  have havo := P.counterexample.good.avoidance q eta hstoreOld hgammaMem
  exact (Finset.mem_sdiff.mp havo).2 hsegOld

private theorem helper_hseriesCast_889.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        V] [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi) (C :
        HierarchyCounterexample base) (ctx : HierarchyMinimumCounterexampleContext G k e0 input T
        phi ett base C) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let _ : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let seriesCast : TashkinovSeries G k P.corresponding.replacementETT.rounds e0
        P.corresponding.replacementInput := @Eq.rec Nat (@ExtendedTashkinovTree.rounds V E inst
        inst_1 inst_3 G k e0 input T phi ett) (fun (x : Nat) (_ : @Eq Nat
        (@ExtendedTashkinovTree.rounds V E inst inst_1 inst_3 G k e0 input T phi ett) x) ↦
        @TashkinovSeries V E inst inst_1 inst_3 G k x e0
        (@CorrespondingExtendedTashkinovTree.replacementInput V E inst inst_1 inst_3 G k e0 input
        T phi ett (@HierarchyReplacementPresentation.coloring V E inst inst_1 inst_2 inst_3 G k e0
        input T phi ett base C ctx P) T (@HierarchyReplacementPresentation.corresponding V E inst
        inst_1 inst_2 inst_3 G k e0 input T phi ett base C ctx P)))
        (@CorrespondingExtendedTashkinovTree.replacementSeries V E inst inst_1 inst_3 G k e0 input
        T phi ett (@HierarchyReplacementPresentation.coloring V E inst inst_1 inst_2 inst_3 G k e0
        input T phi ett base C ctx P) T (@HierarchyReplacementPresentation.corresponding V E inst
        inst_1 inst_2 inst_3 G k e0 input T phi ett base C ctx P)) (@ExtendedTashkinovTree.rounds
        V E inst inst_1 inst_3 G k e0 (@CorrespondingExtendedTashkinovTree.replacementInput V E
        inst inst_1 inst_3 G k e0 input T phi ett (@HierarchyReplacementPresentation.coloring V E
        inst inst_1 inst_2 inst_3 G k e0 input T phi ett base C ctx P) T
        (@HierarchyReplacementPresentation.corresponding V E inst inst_1 inst_2 inst_3 G k e0
        input T phi ett base C ctx P)) T (@HierarchyReplacementPresentation.coloring V E inst
        inst_1 inst_2 inst_3 G k e0 input T phi ett base C ctx P)
        (@CorrespondingExtendedTashkinovTree.replacementETT V E inst inst_1 inst_3 G k e0 input T
        phi ett (@HierarchyReplacementPresentation.coloring V E inst inst_1 inst_2 inst_3 G k e0
        input T phi ett base C ctx P) T (@HierarchyReplacementPresentation.corresponding V E inst
        inst_1 inst_2 inst_3 G k e0 input T phi ett base C ctx P))) (
    by
        have := GoldbergSeymour.TreeSequence.positive T
        have :=
          GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
            (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
        omega
    ); seriesCast ≍ P.corresponding.replacementSeries := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P m seriesCast
  have typeLink :
      TashkinovSeries G k ett.rounds e0 P.corresponding.replacementInput =
        TashkinovSeries G k m.rounds e0 P.corresponding.replacementInput :=
    congrArg (fun r => TashkinovSeries G k r e0
      P.corresponding.replacementInput) P.corresponding.rungAgreement.symm
  simp [seriesCast]

private theorem helper_htree_1031.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (sigma :
        PartialEdgeColoring E k),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring) (_ : TashkinovHierarchy ettX baseX),
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc;
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T),
    let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
        corr.replacementInput := cast (congrArg (fun (r : ℕ) ↦ TashkinovSeries G k r e0
        corr.replacementInput) (
    by
          first
          | omega
          | ( have :=
                GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
              have := GoldbergSeymour.TreeSequence.positive T
              have :=
                GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
                  (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
              all_goals omega)
    )) corr.replacementSeries; (
    ∀ {a b : ℕ} (h : a = b) (s : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (2
        : ℕ))), (cast (congrArg (fun (r : ℕ) ↦ TashkinovSeries G k r e0 corr.replacementInput) h)
        s).data.tree i = s.data.tree (Fin.cast (
    by
              omega
    ) i)) → corr.replacementETT.series = replacementSeries →
    let terminalIndex : Fin corr.replacementETT.rounds := Fin.cast (
    by
        first
        | omega
        | ( have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            have :=
              GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
                (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
            all_goals omega)
    ) (⟨m.rounds - (1 : ℕ),
    have hp : (1 : ℕ) ≤ m.rounds := m.roundsPositive; Decidable.byContradiction fun (a : ¬m.rounds
        - (1 : ℕ) < m.rounds) ↦
    by
            omega
    ⟩ : Fin m.rounds); corr.replacementETT.series.data.tree terminalIndex.succ.castSucc = Tn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P sigma X m ettX baseX HX n Tn corr
      replacementSeries castTree hseries terminalIndex
  rw [hseries]
  calc
    replacementSeries.data.tree terminalIndex.succ.castSucc =
        corr.replacementSeries.data.tree
          (Fin.cast (congrArg (fun r => r + 2) corr.rungAgreement)
            terminalIndex.succ.castSucc) := by
      simpa [replacementSeries] using
        castTree corr.rungAgreement.symm corr.replacementSeries
          terminalIndex.succ.castSucc
    _ = m.series.data.tree n.castSucc := by
      convert corr.ladderTreesAgree
        (Fin.cast corr.rungAgreement terminalIndex) using 1
      · congr 1
      · congr 1
        apply Fin.ext
        have hp : m.rounds - 1 + 1 = m.rounds := by
          exact Nat.sub_add_cancel (by have := m.roundsPositive; omega)
        simp [terminalIndex, hp, n]

private theorem helper_htreeFinal_1056.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (sigma :
        PartialEdgeColoring E k),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring) (_ : TashkinovHierarchy ettX baseX),
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc;
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T),
    let terminalIndex : Fin corr.replacementETT.rounds := Fin.cast (
    by
        first
        | omega
        | ( have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            have :=
              GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
                (GoldbergSeymour.HierarchyReplacementPresentation.corresponding P)
            all_goals omega)
    ) (⟨m.rounds - (1 : ℕ),
    have hp : (1 : ℕ) ≤ m.rounds := m.roundsPositive; Decidable.byContradiction fun (a : ¬m.rounds
        - (1 : ℕ) < m.rounds) ↦
    by
            omega
    ⟩ : Fin m.rounds); corr.replacementETT.series.data.tree terminalIndex.succ.castSucc = Tn →
        corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc = Tn
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P sigma X m ettX baseX HX n Tn corr
      terminalIndex htree
  have hi : (Fin.last corr.replacementETT.rounds).castSucc =
      terminalIndex.succ.castSucc := by
    apply Fin.ext
    have hp : m.rounds - 1 + 1 = m.rounds := by
      exact Nat.sub_add_cancel (by have := m.roundsPositive; omega)
    simp [terminalIndex, hp, corr.rungAgreement]
  rw [hi]
  exact htree

private theorem helper_branch_1125.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (sigma :
        PartialEdgeColoring E k),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring) (_ : TashkinovHierarchy ettX baseX),
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc; ModColoring m sigma →
        TreeSequenceInitialSegment Tn T → Tn.length < T.length →
    ∀ (corrPrefix : CorrespondingExtendedTashkinovTree G k e0 m sigma X) (basePrefix :
        HierarchyBase corrPrefix.replacementETT sigma), ((m.series.data.kind n = some
        TashkinovExtensionKind.SE ∨ m.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), m.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T), MaximumProperty
        corr.replacementETT ∧
    ∃ (newBase : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT newBase), newBase.closure = basePrefix.closure ∧ SameHierarchyStages H
        K := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P sigma X m H ettX baseX HX n Tn hmod hNT
      hNstrict corrPrefix basePrefix hnonpeRoute
  rcases hnonpeRoute with ⟨hkind, f, seed, hconn, hadjoin, hbuilt⟩
  obtain ⟨corr⟩ := hmod.2.2 T hNT hNstrict
    (Or.inr ⟨hkind, f, seed, hconn, hadjoin, hbuilt⟩)
  have hmaximum : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 m sigma hmod T corr P.maximum
  let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds
      e0 corr.replacementInput :=
    cast (congrArg (fun r => TashkinovSeries G k r e0
      corr.replacementInput) corr.rungAgreement.symm)
      corr.replacementSeries
  have castTree {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 2)) :
      (cast (congrArg (fun r => TashkinovSeries G k r e0
        corr.replacementInput) h) s).data.tree i =
        s.data.tree (Fin.cast (congrArg (fun r => r + 2) h.symm) i) := by
    cases h
    rfl
  have castKind {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)) :
      (cast (congrArg (fun r => TashkinovSeries G k r e0
        corr.replacementInput) h) s).data.kind i =
        s.data.kind (Fin.cast (congrArg (fun r => r + 1) h.symm) i) := by
    cases h
    rfl
  have hseries : corr.replacementETT.series = replacementSeries := by
    apply helper_hseries_463
  let terminalIndex : Fin corr.replacementETT.rounds :=
    Fin.cast corr.rungAgreement.symm
      ⟨m.rounds - 1, by have hp := m.roundsPositive; omega⟩
  have htree : corr.replacementETT.series.data.tree
      terminalIndex.succ.castSucc = Tn := by
    apply helper_htree_1031 <;> assumption
  have hkindEq :
    ∀ i : Fin (corr.replacementETT.rounds + 1), corr.replacementETT.series.data.kind i =
        m.series.data.kind (Fin.cast (congrArg (fun r => r + 1) corr.rungAgreement) i) := by
    apply helper_hkindEq_493 <;> assumption
  have htreeFinal : corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
    apply helper_htreeFinal_1056 <;> assumption
  have hkindP : m.series.data.kind (Fin.last m.rounds) ≠
        some TashkinovExtensionKind.PE := by
    apply helper_hkindP_512; assumption
  let newBase : HierarchyBase corr.replacementETT sigma := {
    core := Tn
    closure := basePrefix.closure
    supportPosition := Fin.cast
      (congrArg (fun U : TreeSequence G e0 => U.length + 1)
        htreeFinal.symm) P.replacementBase.supportPosition
    supportPositive := P.replacementBase.supportPositive
    terminalMissingColors := by rfl
    parallel := by
      dsimp
      intro hp
      have hk := hkindEq (Fin.last corr.replacementETT.rounds)
      have hs : m.series.data.kind n =
          some TashkinovExtensionKind.PE := by
        simpa [corr.rungAgreement] using hk.symm.trans hp
      rcases hkind with hse | hre
      · rw [hs] at hse
        cases hse
      · rw [hs] at hre
        cases hre
    nonparallel := by
      dsimp
      intro hn
      have hc := P.replacementBase.nonparallel hkindP
      simp [htreeFinal]}
  let K : TashkinovHierarchy corr.replacementETT newBase := {
    dividerCount := H.dividerCount
    stage := H.stage
    baseStage := by simpa [htreeFinal] using H.baseStage
    terminalStage := H.terminalStage
    nested := H.nested
    strict := H.strict
    dividerPosition := H.dividerPosition
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := H.dividerStage
    coreInsideFirst := by
      have hcoreEq : Tn = P.replacementBase.core := by
        have h := P.replacementBase.nonparallel hkindP
        simpa [m, Tn, n] using h.symm
      simpa [newBase] using hcoreEq ▸ H.coreInsideFirst }
  have hsame : SameHierarchyStages H K := by
    dsimp [SameHierarchyStages, K, newBase]
    have hcoreEq : Tn = P.replacementBase.core := by
      have h := P.replacementBase.nonparallel hkindP
      simpa [m, Tn, n] using h.symm
    refine ⟨hcoreEq.symm, rfl, heq_of_eq rfl, heq_of_eq rfl, ?_, ?_⟩
    · constructor <;> intro hp
      · have hk := hkindEq (Fin.last corr.replacementETT.rounds)
        have hs : corr.replacementETT.series.data.kind
            (Fin.last corr.replacementETT.rounds) =
            m.series.data.kind n := by
          simpa [corr.rungAgreement] using hk
        exact hs ▸ hp
      · have hk := hkindEq (Fin.last corr.replacementETT.rounds)
        have hs : corr.replacementETT.series.data.kind
            (Fin.last corr.replacementETT.rounds) =
            m.series.data.kind n := by
          simpa [corr.rungAgreement] using hk
        exact hs.symm ▸ hp
    · intro hp
      rcases hkind with hse | hre
      · have he : TashkinovExtensionKind.SE = TashkinovExtensionKind.PE :=
          Option.some.inj (hse.symm.trans hp)
        cases he
      · have he : TashkinovExtensionKind.RE = TashkinovExtensionKind.PE :=
          Option.some.inj (hre.symm.trans hp)
        cases he
  exact ⟨corr, hmaximum, newBase, K, rfl, hsame⟩

private theorem helper_hfull_1262.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k), P2880_T1_SplitSwapData G k e0 input T phi ett base C
        ctx P alpha beta sigma →
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (baseX :
        HierarchyBase ettX P.coloring), baseX.closure = P.replacementBase.closure →
    ∀ (HX : TashkinovHierarchy ettX baseX) (goodX : GoodHierarchy HX), IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 → StableColoring X (TashkinovStoredColors
        ettX.series.data (Fin.last ettX.rounds)) P.coloring sigma →
    let n : Fin (m.rounds + (1 : ℕ)) := Fin.last m.rounds;
    let Tn : TreeSequence G e0 := m.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors m.series.data n; StableColoring Tn Dn
        P.coloring sigma → ModColoring m sigma → (m.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence sigma Tn T ∨ (m.series.data.kind
        n = some TashkinovExtensionKind.SE ∨ m.series.data.kind n = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), m.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T) →
        TreeSequenceInitialSegment Tn T → Tn.length < T.length →
    ∀ (corrPrefix : CorrespondingExtendedTashkinovTree G k e0 m sigma X) (basePrefix :
        HierarchyBase corrPrefix.replacementETT sigma) (KPrefix : TashkinovHierarchy
        corrPrefix.replacementETT basePrefix) (goodPrefix : GoodHierarchy KPrefix),
        SameGoodHierarchy goodX goodPrefix → ettX.series.data.kind (Fin.last ettX.rounds) =
        m.series.data.kind n →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T), MaximumProperty
        corr.replacementETT ∧
    ∃ (newBase : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT newBase), newBase.closure = basePrefix.closure ∧ SameHierarchyStages H
        K := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S X m H ettX baseX
      hclosureX HX goodX hsigmaProper hsigmaOne hstableX n Tn Dn hstableTn hmod hroute hNT
      hNstrict corrPrefix basePrefix KPrefix goodPrefix samePrefix hkindX
  by_cases hpe : m.series.data.kind n =
      some TashkinovExtensionKind.PE
  · apply helper_branch_392 <;> assumption
  · rcases hroute with hpeRoute | hnonpeRoute
    · exact False.elim (hpe hpeRoute.1)
    · apply helper_branch_1125 <;> assumption
private theorem helper_hlowerX_1128.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (_ :
        ettX.rounds = m.rounds) {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ettX.rounds → MaximumProperty lower
        → open scoped Classical in LowerRoundProperties lower := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P X m ettX hroundX input' T' generating'
      lower hpos hlt hmax
  have hlt' : lower.rounds < m.rounds := by
    rw [← hroundX]
    exact hlt
  exact P.minimumContext.lowerRung lower hpos hlt' hmax

private theorem helper_continuation_1640.{u_1, u_2} :
    helperContinuation1640Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P sigma X m H ettX baseX HX hcountX
      hstagesX hpositionsX goodX hcolorsX corrPrefix basePrefix KPrefix goodPrefix samePrefix
      corrFull hmaximumFull baseFull KFull hsameFull Ktransport hcountTransport hstagesTransport
      hpositionsTransport goodFull hsamePrefixFull
  have hsameFinal : SameGoodHierarchy P.counterexample.good goodFull := by
    let hcountGood := samePrefix.2.choose
    let hcountFinal : H.dividerCount = Ktransport.dividerCount :=
      hcountX.symm.trans (hcountGood.trans hcountTransport.symm)
    have stageAt {a b : ℕ} (h : a = b)
        (f : Fin (a + 2) → TreeSequence G e0)
        (g : Fin (b + 2) → TreeSequence G e0) (hfg : HEq f g)
        (j : Fin (b + 2)) :
        f (Fin.cast (congrArg (fun z => z + 2) h.symm) j) = g j := by
      cases h
      simpa using congrFun (eq_of_heq hfg) j
    have positionValueAt {a b : ℕ} (h : a = b)
        (f : Fin a → Fin (X.length + 1))
        (g : Fin b → Fin (X.length + 1)) (hfg : HEq f g)
        (j : Fin b) :
        (f (Fin.cast (congrArg (fun z => z) h.symm) j)).val = (g j).val := by
      cases h
      simpa using congrArg Fin.val (congrFun (eq_of_heq hfg) j)
    have hierarchyStageHEq {a b : ℕ} (h : a = b)
        (f : Fin (a + 2) → TreeSequence G e0)
        (g : Fin (b + 2) → TreeSequence G e0)
        (hmid : ∀ i : Fin (a + 1),
          f i.castSucc = g
            (Fin.cast (congrArg (fun z => z + 1) h) i).castSucc)
        (hlast : f (Fin.last (a + 1)) = g (Fin.last (b + 1))) :
        HEq f g := by
      cases h
      apply heq_of_eq
      funext j
      refine Fin.lastCases hlast (fun i => ?_) j
      simpa using hmid i
    have positionFamilyHEq {a b : ℕ} (h : a = b)
        (f : Fin a → Fin (T.length + 1))
        (g : Fin b → Fin (T.length + 1))
        (hmid : ∀ i : Fin a, f i = g (Fin.cast h i)) : HEq f g := by
      cases h
      apply heq_of_eq
      funext i
      exact hmid i
    have hstageMiddle (i : Fin (H.dividerCount + 1)) :
        H.stage i.castSucc = Ktransport.stage
          (Fin.cast (congrArg (fun z => z + 1) hcountFinal) i).castSucc := by
      let ix := Fin.cast (congrArg (fun z => z + 1) hcountX.symm) i
      let ip := Fin.cast (congrArg (fun z => z + 1) hcountGood) ix
      let iu := Fin.cast (congrArg (fun z => z + 1) hcountTransport.symm) ip
      have hx := (hstagesX ix).1
      have hp := stageAt hcountGood HX.stage KPrefix.stage
        samePrefix.1.2.2.1 ip.castSucc
      have hu := (hstagesTransport iu).1
      calc
        H.stage i.castSucc = HX.stage ix.castSucc := by
          convert hx.symm using 1; congr 1
        _ = KPrefix.stage ip.castSucc := by
          convert hp using 1; congr 1
        _ = Ktransport.stage iu.castSucc := by
          convert hu.symm using 1; congr 1
    have hstageFinal : HEq H.stage Ktransport.stage := by
      apply hierarchyStageHEq hcountFinal H.stage Ktransport.stage
        hstageMiddle
      rw [H.terminalStage, Ktransport.terminalStage]
    have hpositionMiddle (i : Fin (H.dividerCount)) :
        (H.dividerPosition i).val =
          (Ktransport.dividerPosition
            (Fin.cast (congrArg (fun z => z) hcountFinal) i)).val := by
      let ix := Fin.cast hcountX.symm i
      let ip := Fin.cast hcountGood ix
      let iu := Fin.cast hcountTransport.symm ip
      have hp := positionValueAt hcountGood HX.dividerPosition
        KPrefix.dividerPosition samePrefix.1.2.2.2.1 ip
      calc
        (H.dividerPosition i).val = (HX.dividerPosition ix).val := by
          have hidx : Fin.cast hcountX ix = i := by
            apply Fin.ext
            simp [ix]
          have hx := hpositionsX ix
          rw [hidx] at hx
          exact hx.symm
        _ = (KPrefix.dividerPosition ip).val := hp
        _ = (Ktransport.dividerPosition iu).val := by
          have hidx : Fin.cast hcountTransport iu = ip := by
            apply Fin.ext
            simp [iu]
          have hu := hpositionsTransport iu
          rw [hidx] at hu
          exact hu.symm
    have hpositionFinal : HEq H.dividerPosition Ktransport.dividerPosition := by
      apply positionFamilyHEq hcountFinal H.dividerPosition
        Ktransport.dividerPosition
      intro i
      apply Fin.ext
      exact hpositionMiddle i
    have hsameStages : SameHierarchyStages H Ktransport := by
      unfold SameHierarchyStages
      dsimp only
      refine ⟨hsameFull.1, hcountFinal, hstageFinal,
        hpositionFinal, ?_, ?_⟩
      · exact hsameFull.2.2.2.2.1
      · intro hp
        exact hsameFull.2.2.2.2.2 hp
    unfold SameGoodHierarchy
    refine ⟨hsameStages, hcountFinal, ?_⟩
    intro j
    let jX := Fin.cast (congrArg (fun z => z + 1) hcountX.symm) j
    let jP := Fin.cast (congrArg (fun z => z + 1) hcountGood) jX
    let jU := Fin.cast (congrArg (fun z => z + 1) hcountTransport.symm) jP
    have hx := hcolorsX jX
    have hp := samePrefix.2.choose_spec jX
    have hu := hstagesTransport jU
    have hjX : Fin.cast (congrArg (fun z => z + 1) hcountX) jX = j := by
      apply Fin.ext
      simp [jX]
    have hjU : Fin.cast (congrArg (fun z => z + 1) hcountTransport) jU = jP := by
      apply Fin.ext
      simp [jU]
    refine ⟨?_, ?_⟩
    · calc
        HierarchyStoredColorsAt H j = HierarchyStoredColorsAt HX jX := by
          rw [← hjX]
          exact hx.1.symm
        _ = HierarchyStoredColorsAt KPrefix jP := hp.1
        _ = HierarchyStoredColorsAt Ktransport jU := by
          rw [← hjU]
          exact hu.2.2.1.symm
    · intro eta heta
      have hgamma := (hx.2.2 eta).1
      rw [hjX] at hgamma
      calc
        P.counterexample.good.gamma j eta = goodX.gamma jX eta :=
          hgamma.symm
        _ = goodPrefix.gamma jP eta := hp.2 eta (by rw [hx.1, hjX]; exact heta)
        _ = goodFull.gamma jU eta := by
          rw [← hjU]
          exact (hsamePrefixFull jU eta).symm
  exact ⟨corrFull, hmaximumFull, baseFull, Ktransport, goodFull, hsameFinal⟩

private theorem helper_continuation_1844.{u_1, u_2} :
    helperContinuation1844Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S X m H q ettX baseX
      hcoreX hclosureX HX hcountX hstagesX hpositionsX goodX hcolorsX hsigmaProper hsigmaOne
      hstableX n Tn Dn hstableTn hmod hroute hNT hNstrict corrPrefix basePrefix KPrefix
      goodPrefix samePrefix hkindX
  have hfull :
      ∃ corr : CorrespondingExtendedTashkinovTree G k e0 m sigma T,
        MaximumProperty corr.replacementETT ∧
        ∃ newBase : HierarchyBase corr.replacementETT sigma,
          ∃ K : TashkinovHierarchy corr.replacementETT newBase,
            newBase.closure = basePrefix.closure ∧ SameHierarchyStages H K := by
    apply helper_hfull_1262 <;> assumption
  rcases hfull with ⟨corrFull, hmaximumFull, baseFull, KFull, hclosure, hsameFull⟩
  have hcoreFull : baseFull.core = basePrefix.core := by
    have hprefixCore := samePrefix.1.1
    have hfullCore := hsameFull.1
    exact hfullCore.symm.trans (hcoreX.symm.trans hprefixCore)
  have hfullRoute : TashkinovAugmentationSequence sigma X T := S.newSuffix
  obtain ⟨Ktransport, hcountTransport, hstagesTransport, hpositionsTransport⟩ :=
    GoodHierarchySameDividerReconstruction G k e0
      P.corresponding.replacementInput T P.coloring sigma m X T
      corrPrefix basePrefix KPrefix corrFull baseFull hcoreFull hfullRoute
  have havoid : ∀ eta : Fin k,
      eta ∈ HierarchyStoredColorsAt KPrefix (Fin.last KPrefix.dividerCount) →
      Disjoint (goodPrefix.gamma (Fin.last KPrefix.dividerCount) eta)
        (Finset.univ.filter fun c => ∃ r : Fin T.length,
        (HierarchyStarredStage KPrefix (Fin.last KPrefix.dividerCount)).length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma T eta).val T.length ∧
          sigma (T.edge r) = some c) := by
    intro eta heta
    let qX : Fin (HX.dividerCount + 1) := Fin.last HX.dividerCount
    let qP : Fin (KPrefix.dividerCount + 1) := Fin.last KPrefix.dividerCount
    have hcountXP : HX.dividerCount = KPrefix.dividerCount := samePrefix.1.2.1
    rcases samePrefix.2 with ⟨hcountGood, hsameGamma⟩
    have hidxXP : Fin.cast (congrArg (fun z : ℕ => z + 1) hcountGood) qX = qP := by
      apply Fin.ext
      simp [qX, qP]
    have hstoreXP : HierarchyStoredColorsAt HX qX =
        HierarchyStoredColorsAt KPrefix qP := by
      simpa [qX, qP, hidxXP] using (hsameGamma qX).1
    have hetaX : eta ∈ HierarchyStoredColorsAt HX qX := by
      rw [hstoreXP]
      exact heta
    have hidxXH : Fin.cast (congrArg (fun z : ℕ => z + 1) hcountX) qX = q := by
      apply Fin.ext
      simp [qX, q]
    have hstoreOld : eta ∈ HierarchyStoredColorsAt H q := by
      have hx := (hcolorsX qX).1
      rw [hidxXH] at hx
      rw [← hx]
      exact hetaX
    have hgammaOldPrefix : P.counterexample.good.gamma q eta =
        goodPrefix.gamma qP eta := by
      have hx := (hcolorsX qX).2.2 eta
      have hp := hsameGamma qX
      simpa [q, qX, qP, hidxXH, hidxXP] using hx.1.symm.trans (hp.2 eta hetaX)
    have stageAt {a b : ℕ} (h : a = b)
        (f : Fin (a + 2) → TreeSequence G e0)
        (g : Fin (b + 2) → TreeSequence G e0) (hfg : HEq f g)
        (j : Fin (b + 2)) : f (Fin.cast (congrArg (fun d => d + 2) h.symm) j) = g j := by
      cases h
      simpa using congrFun (eq_of_heq hfg) j
    let index (j : Fin (HX.dividerCount + 1)) :
        Fin (KPrefix.dividerCount + 1) :=
      Fin.cast (congrArg (fun d : ℕ => d + 1) hcountXP) j
    have stageEq (j : Fin (HX.dividerCount + 1)) :
        HX.stage j.castSucc = KPrefix.stage (index j).castSucc := by
      have hs := stageAt hcountXP HX.stage KPrefix.stage
        samePrefix.1.2.2.1 (index j).castSucc
      convert hs using 1; congr 1
    have hstarXP' (j : Fin (HX.dividerCount + 1)) :
        HierarchyStarredStage HX j = HierarchyStarredStage KPrefix (index j) := by
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [HierarchyStarredStage, index] using samePrefix.1.1
      · have hs := stageEq i.succ
        simpa [HierarchyStarredStage, index] using hs
    have hstarXP : HierarchyStarredStage KPrefix qP =
        HierarchyStarredStage HX qX := by
      have hs := hstarXP' qX
      simpa [index, qX, qP, hidxXP] using hs.symm
    have hstarOld : HierarchyStarredStage KPrefix qP =
        HierarchyStarredStage H q := by
      have hx := (hstagesX qX).2
      have hidx : Fin.cast (congrArg (fun z : ℕ => z + 1) hcountX) qX = q := hidxXH
      exact hstarXP.trans (hx.trans (by simp [hidx]))
    apply Finset.disjoint_left.mpr
    intro c hcG hcSeg
    rcases (Finset.mem_filter.mp hcSeg).2 with ⟨r, hlo, hhi, hcol⟩
    by_cases haffected : alpha ∈ P.counterexample.good.gamma q eta ∨
        beta ∈ P.counterexample.good.gamma q eta
    · exact @helper_branch_667 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@sigma) (@S) (@corrPrefix) (@basePrefix) (@KPrefix) (@goodPrefix) (@eta) (@heta)
        (@hstoreOld) (@c) (@hcG) (@r) (@hlo) (@hhi) (@hcol) (@haffected)
    · exact @helper_branch_700 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta)
        (@sigma) (@S) (@corrPrefix) (@basePrefix) (@KPrefix) (@goodPrefix) (@eta) (@hstoreOld)
        (@hgammaOldPrefix) (@hstarOld) (@c) (@hcG) (@r) (@hlo) (@hhi) (@hcol) (@haffected)
  obtain ⟨goodFull, hsamePrefixFull⟩ :=
    GoodHierarchySameDividerTransport G k e0
      P.corresponding.replacementInput T P.coloring sigma m X T
      corrPrefix basePrefix KPrefix goodPrefix corrFull baseFull
      hcoreFull hclosure Ktransport hcountTransport hstagesTransport
      hfullRoute havoid
  exact @helper_continuation_1640 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@sigma)
      (@ettX) (@baseX) (@HX) (@hcountX) (@hstagesX) (@hpositionsX) (@goodX) (@hcolorsX)
      (@corrPrefix) (@basePrefix) (@KPrefix) (@goodPrefix) (@samePrefix) (@corrFull)
      (@hmaximumFull) (@baseFull) (@KFull) (@hsameFull) (@Ktransport) (@hcountTransport)
      (@hstagesTransport) (@hpositionsTransport) (@goodFull) (@hsamePrefixFull)

private theorem helper_continuation_1969.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k)
        (sigma : PartialEdgeColoring E k) (_ : P2880_T1_SplitSwapData G k e0 input T phi ett base
        C ctx P alpha beta sigma),
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - (1 :
        ℕ));
    let m : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
        P.counterexample.hierarchy;
    ∀ (ettX : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput X P.coloring) (_ :
        MaximumProperty ettX) (_ : ettX.rounds = m.rounds) (_ : ettX.series ≍ m.series) (baseX :
        HierarchyBase ettX P.coloring) (_ : baseX.core = P.replacementBase.core) (_ :
        baseX.closure = P.replacementBase.closure) (HX : TashkinovHierarchy ettX baseX) (hcountX :
        HX.dividerCount = H.dividerCount) (_ :
    ∀ (j : Fin (HX.dividerCount + (1 : ℕ))), HX.stage j.castSucc = H.stage (Fin.cast (
    by
                    omega
    ) j).castSucc ∧ HierarchyStarredStage HX j = HierarchyStarredStage H (Fin.cast (
    by
                  omega
    ) j)) (_ :
    ∀ (i : Fin HX.dividerCount), (↑(HX.dividerPosition i) : ℕ) = (↑(H.dividerPosition (Fin.cast
        hcountX i)) : ℕ)) (goodX : GoodHierarchy HX) (_ :
    ∀ (j : Fin (HX.dividerCount + (1 : ℕ))), HierarchyStoredColorsAt HX j =
        HierarchyStoredColorsAt H (Fin.cast (congrArg (fun n : ℕ => n + 1) hcountX) j) ∧
        HierarchyStageMissingColors HX j = HierarchyStageMissingColors H (Fin.cast (congrArg (fun
        n : ℕ => n + 1) hcountX) j) ∧
    ∀ (eta : Fin k), goodX.gamma j eta = P.counterexample.good.gamma (Fin.cast (congrArg (fun n :
        ℕ => n + 1) hcountX) j) eta ∧ HierarchySegmentColors HX j eta ⊆ HierarchySegmentColors H
        (Fin.cast (congrArg (fun n : ℕ => n + 1) hcountX) j) eta) (_ : OutsideKempeRecoloring X
        P.coloring sigma alpha beta) (_ :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ettX.rounds → MaximumProperty lower
        → (open scoped Classical in LowerRoundProperties lower)),
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 P.corresponding.replacementETT sigma T),
        MaximumProperty corr.replacementETT ∧
    ∃ (newBase : HierarchyBase corr.replacementETT sigma) (K : TashkinovHierarchy
        corr.replacementETT newBase) (good : GoodHierarchy K), SameGoodHierarchy
        P.counterexample.good good := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta sigma S X m H ettX hMPX
      hroundX hseriesX baseX hcoreX hclosureX HX hcountX hstagesX hpositionsX goodX hcolorsX
      hrecolorX hlowerX
  have hlem := HierarchyLEMStable G k e0 P.corresponding.replacementInput X
    P.coloring sigma ettX hMPX (by
      simpa [hroundX] using P.counterexample.positive)
    hlowerX baseX HX goodX P.minimumContext.proper
    P.minimumContext.oneEdgeUncolored alpha beta hrecolorX
  rcases hlem with ⟨hsigmaProper, hsigmaOne, hstableX, hinvariantX,
    corrX, hmaximumX, baseSigmaX, KX, goodSigmaX, hsameX, hclosedX⟩
  let n := Fin.last m.rounds
  let Tn := m.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors m.series.data n
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    apply helper_segmentTrans_194 <;> assumption
  have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
    apply helper_hTnCore_213
  have hTnX : TreeSequenceInitialSegment Tn X :=
    segmentTrans hTnCore S.coreInSplit
  have hTnXvertices : TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet X :=
    TreeSequenceInitialSegmentVertexSetSubset hTnX
  have hstableTn : StableColoring Tn Dn
      P.coloring sigma := by
    apply helper_hstableTn_223 <;> assumption
  have hstableTn' : StableColoring Tn Dn
      (m.series.data.coloring n) sigma := by
    have hcolor : m.series.data.coloring n = P.coloring := by
      simpa [n, m] using m.generatingColoring.symm
    rw [hcolor]
    exact hstableTn
  have hmod : ModColoring m sigma :=
    Td G k e0 P.corresponding.replacementInput T P.coloring m P.maximum
      P.counterexample.positive P.minimumContext.lowerRung sigma hsigmaProper
      hsigmaOne hstableTn'
  have hroute :
      (m.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T) ∨
      ((m.series.data.kind n = some TashkinovExtensionKind.SE ∨
          m.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f : E, ∃ seed : TreeSequence G e0,
          m.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence sigma seed T) := by
    apply helper_hroute_241 <;> assumption
  have hNT : TreeSequenceInitialSegment Tn T := by
    apply helper_hNT_259 <;> assumption
  have hNstrict : Tn.length < T.length := by
    apply helper_hNstrict_267 <;> assumption
  let seriesCast := P.corresponding.rungAgreement.symm ▸
    P.corresponding.replacementSeries
  have hseriesCast : HEq seriesCast P.corresponding.replacementSeries := by
    apply helper_hseriesCast_889
  have hsourceSeries : m.series = seriesCast := by
    exact eq_of_heq (HEq.trans P.corresponding.seriesPresentation
      hseriesCast.symm)
  have castColor :
    ∀ {r s : Nat} (h : r = s) (ser : TashkinovSeries G k s e0 P.corresponding.replacementInput) (i
        : Fin (r + 1)), (h.symm ▸ ser).data.coloring i = ser.data.coloring (Fin.cast (congrArg
        (fun z => z + 1) h) i) := by
    intro r s h ser i
    cases h
    rfl
  let corrMX := @helperCorrMX773 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@ettX) (@hroundX)
      (@hseriesX) (@hsourceSeries) (@castColor)
  obtain ⟨corrPrefix, hinputPrefix, hseriesPrefix, hETTPrefix⟩ :=
    CorrespondingExtendedTashkinovTreeTransTrees G k e0
      P.corresponding.replacementInput T X X P.coloring P.coloring sigma m
      corrMX corrX
  have transportETT {I J : PartialEdgeColoring E k} (h : I = J)
      {F : ExtendedTashkinovTree G k e0 I X sigma}
      {F' : ExtendedTashkinovTree G k e0 J X sigma} (hf : HEq F F') :
      F = h.symm ▸ F' := by
    cases h
    exact eq_of_heq hf
  have transportPrefixPackage {I J : PartialEdgeColoring E k} (h : I = J)
      {F : ExtendedTashkinovTree G k e0 I X sigma}
      {F' : ExtendedTashkinovTree G k e0 J X sigma} (hf : HEq F F')
      (b : HierarchyBase F' sigma) (K : TashkinovHierarchy F' b)
      (good : GoodHierarchy K) (hsame : SameGoodHierarchy goodX good) :
      ∃ b' : HierarchyBase F sigma,
        ∃ K' : TashkinovHierarchy F b',
          ∃ good' : GoodHierarchy K', SameGoodHierarchy goodX good' := by
    cases h
    have heq : F = F' := eq_of_heq hf
    cases heq
    exact ⟨b, K, good, hsame⟩
  have prefixPackage :
      ∃ b : HierarchyBase corrPrefix.replacementETT sigma,
        ∃ K : TashkinovHierarchy corrPrefix.replacementETT b,
          ∃ good : GoodHierarchy K,
            SameGoodHierarchy goodX good := by
    exact transportPrefixPackage hinputPrefix hETTPrefix
      baseSigmaX KX goodSigmaX hsameX
  obtain ⟨basePrefix, KPrefix, goodPrefix, samePrefix⟩ := prefixPackage
  have hkindX : ettX.series.data.kind (Fin.last ettX.rounds) =
      m.series.data.kind n := by
    apply helper_hkindX_358 <;> assumption
  exact @helper_continuation_1844 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@sigma) (@S) (@ettX) (@baseX) (@hcoreX) (@hclosureX) (@HX) (@hcountX) (@hstagesX)
      (@hpositionsX) (@goodX) (@hcolorsX) (@hsigmaProper) (@hsigmaOne) (@hstableX) (@hstableTn)
      (@hmod) (@hroute) (@hNT) (@hNstrict) (@corrPrefix) (@basePrefix) (@KPrefix) (@goodPrefix)
      (@samePrefix) (@hkindX)

theorem P2880_T1_OutsidePrefixBranch
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k) (sigma : PartialEdgeColoring E k)
    (S : P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx P
      alpha beta sigma)
    (_ : ¬ (
      let H := P.counterexample.hierarchy
      let q := Fin.last H.dividerCount
      let m := P.corresponding.replacementETT
      let n := Fin.last m.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := m.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors m.series.data n
      let qualifies := fun (a b : Fin k) =>
        (0 < H.dividerCount ∧ a ∈ TreeMissingColors P.coloring Tnq) ∨
        (H.dividerCount = 0 ∧
          (a ∈ TreeMissingColors P.coloring Tn ∨
            (a ∈ TreeMissingColors P.coloring A ∧ a ∉ Dn ∧ b ∉ Dn)))
      qualifies alpha beta ∨ qualifies beta alpha)) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0
        P.corresponding.replacementETT sigma T,
      MaximumProperty corr.replacementETT ∧
      ∃ newBase : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT newBase,
          ∃ good : GoodHierarchy K,
            SameGoodHierarchy P.counterexample.good good := by
  classical
  let X := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)
  let m := P.corresponding.replacementETT
  let H := P.counterexample.hierarchy
  let q := Fin.last H.dividerCount
  have hprefix := GoodHierarchyTerminalPrefixRepackage G k e0
    P.corresponding.replacementInput T P.coloring P.coloring m P.maximum
    P.replacementBase H P.counterexample.good X S.splitAboveStar.1
    S.splitAboveStar.2 S.splitInFull
  obtain ⟨ettX, hMPX, hroundX, hseriesX, baseX, hcoreX, hclosureX,
    hsuppX, HX, hcountX, hstagesX, hpositionsX, goodX, hcolorsX⟩ := hprefix
  have hrecolorX : OutsideKempeRecoloring X P.coloring sigma alpha beta := by
    apply helper_hrecolorX_82; assumption
  have hlowerX :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), 0 < lower.rounds → lower.rounds < ettX.rounds → MaximumProperty lower →
        ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T') ∧ (
    let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
    let Tnext := lower.series.data.tree (Fin.last (lower.rounds + 1))
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tnext (TashkinovStoredColors lower.series.data n)
        (lower.series.data.coloring n) sigma →
    ∀ alpha beta : Fin k, alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma
        Tnext → TreeInterchangeable G Tnext sigma alpha beta) ∧ ((
    ∀ (q : Fin lower.rounds) (v : V), lower.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → lower.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (j : Fin (lower.rounds + 1)),
        ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring (lower.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        lower.series.data q.succ) (lower.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T' v hvFinal (TashkinovStoredColors lower.series.data j)
        (lower.series.data.coloring j) sigma ∧ (0 < j.val → StableColoring (lower.series.data.tree
        j.castSucc) (TashkinovStoredColors lower.series.data j) (lower.series.data.coloring j)
        sigma)) ∧
    ∀ (q r : Fin lower.rounds) (vq vr : V), q ≠ r → vq ≠ vr → lower.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → lower.series.data.kind r.succ = some TashkinovExtensionKind.PE
        → lower.series.data.chosenVertex q.succ = some vq → lower.series.data.chosenVertex r.succ
        = some vr →
    ∀ (hvq : vq ∈ TreeSequenceVertexSet T') (hvr : vr ∈ TreeSequenceVertexSet T'),
        ETTFirstAppearanceIndex lower vq hvq = ETTFirstAppearanceIndex lower vr hvr → Disjoint
        (lower.series.data.stored q.succ) (lower.series.data.stored r.succ)) ∧ (
    let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
    let Tn := lower.series.data.tree n.castSucc
    ∀ (v : V) (gamma delta : Fin k), lower.series.data.kind n = some TashkinovExtensionKind.PE →
        lower.series.data.chosenVertex n = some v → lower.series.data.gamma n = some gamma →
        lower.series.data.delta n = some delta →
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tn (TashkinovStoredColors lower.series.data n)
        (lower.series.data.coloring n) sigma →
    ∀ w, w ∈ TreeSequenceVertexSet Tn → (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
        (Sum.inl v) ↔ w = v)) ∧ (
    let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
    let Tn := lower.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tn (TashkinovStoredColors lower.series.data n)
        (lower.series.data.coloring n) sigma →
    ∀ delta : Fin k, DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ v, BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v → (
    ∃ w, BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧ TreeVertexOrder Tn w v)
        →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T') (q : Fin lower.rounds) (vi : V),
        (lower.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨ lower.series.data.kind
        q.succ = some TashkinovExtensionKind.SE) → lower.series.data.chosenVertex q.succ = some vi
        → ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 → (v = vi ∨ TreeVertexOrder T' v
        vi)) ∧ (
    let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
    let Tn := lower.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k, IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0
        → StableColoring Tn (TashkinovStoredColors lower.series.data n)
        (lower.series.data.coloring n) sigma → ModColoring lower sigma) := by
    apply helper_hlowerX_1128; assumption
  exact @helper_continuation_1969 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
      (@beta) (@sigma) (@S) (@ettX) (@hMPX) (@hroundX) (@hseriesX) (@baseX) (@hcoreX)
      (@hclosureX) (@HX) (@hcountX) (@hstagesX) (@hpositionsX) (@goodX) (@hcolorsX) (@hrecolorX)
      (@hlowerX)
end GoldbergSeymour

end
