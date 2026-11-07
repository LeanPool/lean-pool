/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.SharedFacts.FullTailTransport

public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceComponentSwap

/-!
# Stable Change Cases One Two Starred Tail

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation835Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
   HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (alpha beta : Fin k),
     alpha ≠ beta →
      alpha ∈
         TreeMissingColors phi (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))) ∧
        beta ∈
         TreeMissingColors phi (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))) →
       ∀ (z : V ⊕ E),
        TwoColorPathComponent G phi alpha beta z →
         ∀ (sigma : PartialEdgeColoring E k),
          sigma = TwoColorComponentSwap G phi alpha beta z →
           (let H : TashkinovHierarchy ett base := C.hierarchy;
            let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
            let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
            let A : TreeSequence G e0 := HierarchyStarredStage H q;
            let Tnq : TreeSequence G e0 :=
             H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
            let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
            let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
            (0 : ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq ∨
             H.dividerCount = (0 : ℕ) ∧
              (alpha ∈ TreeMissingColors phi Tn ∨
               alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn)) →
            (let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
             Disjoint (TwoColorComponent G phi alpha beta z)
              (TwoColorComponent G phi alpha beta (Sum.inl va))) →
             (let H : TashkinovHierarchy ett base := C.hierarchy;
              let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
              ∀ eta ∈ HierarchyStoredColorsAt H q,
               HierarchyFirstMissingPosition sigma T eta =
                HierarchyFirstMissingPosition phi T eta) →
              let H : TashkinovHierarchy ett base := C.hierarchy;
              let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
              let A : TreeSequence G e0 := HierarchyStarredStage H q;
              let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
              let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
              let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
              ColoredVertexSetElementary G phi
                (TreeSequenceVertexSet
                 (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ)))) →
               (∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))) (c : Fin k),
                 c = alpha ∨ c = beta →
                  c ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy r) →
                   TreeColorSetClosed G phi (HierarchyStarredStage C.hierarchy r) { c } →
                    OutsideKempeRecoloring (HierarchyStarredStage C.hierarchy r) phi sigma alpha
                     beta) →
                ModColoring ett sigma →
                 (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
                  (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
                   alpha ∈ TreeMissingColors sigma A ∧ beta ∈ TreeMissingColors sigma A →
                    alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) ∧
                      beta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) →
                     HierarchyWeaklyStable H q sigma →
                      (H.dividerCount = (0 : ℕ) → A = base.core) →
                       TreeSequenceInitialSegment base.core A →
                        TreeSequenceInitialSegment Tn A →
                         TreeSequenceInitialSegment A T →
                          (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                            TreeSequenceInitialSegment (H.stage j.castSucc) A) →
                           (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                             TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
                            (∀ (S : TreeSequence G e0),
                              TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
                               TreeMissingColors sigma S = TreeMissingColors phi S) →
                             ∀ (corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                              MaximumProperty corrT.replacementETT →
                               ∀ (baseT : HierarchyBase corrT.replacementETT sigma)
                                (hcoreT : baseT.core = base.core),
                                baseT.closure = base.closure →
                                 ∀
                                  (terminalData :
                                   corrT.replacementETT.series.data.tree
                                      (Fin.last corrT.replacementETT.rounds).castSucc =
                                     Tn ∧
                                    corrT.replacementETT.series.data.kind
                                       (Fin.last corrT.replacementETT.rounds) =
                                      ett.series.data.kind n ∧
                                     TashkinovStoredColors corrT.replacementETT.series.data
                                       (Fin.last corrT.replacementETT.rounds) =
                                      Dn),
                                  let K : TashkinovHierarchy corrT.replacementETT baseT :=
                                   {
                                    dividerCount := H.dividerCount, stage := H.stage,
                                    baseStage := Eq.trans H.baseStage (Eq.symm terminalData.left),
                                    terminalStage := H.terminalStage, nested := H.nested,
                                    strict := H.strict, dividerPosition := H.dividerPosition,
                                    dividerPositive := H.dividerPositive,
                                    dividerIncreasing := H.dividerIncreasing,
                                    dividerStage := H.dividerStage,
                                    coreInsideFirst :=
                                     Eq.mpr
                                      (id
                                       (congrArg
                                        (fun (_a : TreeSequence G e0) =>
                                         TreeSequenceInitialSegment _a
                                          (H.stage
                                           (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                                        hcoreT))
                                      H.coreInsideFirst :
                                    TashkinovHierarchy corrT.replacementETT baseT };
                                  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                    HierarchyStarredStage K j = HierarchyStarredStage H j) →
                                   (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                     HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j) →
                                    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                      HierarchyStageMissingColors K j =
                                       HierarchyStageMissingColors H j) →
                                     (∀ (f : E) (c : Fin k),
                                       c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
                                      let H : TashkinovHierarchy ett base := C.hierarchy;
                                      let q : Fin (H.dividerCount + (1 : ℕ)) :=
                                       Fin.last H.dividerCount;
                                      HierarchyWeaklyStable H q sigma ∧
                                       ModColoring ett sigma ∧
                                        ∃ (corrT :
                                         CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                                         MaximumProperty corrT.replacementETT ∧
                                          ∃ (baseT : HierarchyBase corrT.replacementETT sigma) (K :
                                           TashkinovHierarchy corrT.replacementETT baseT) (goodT :
                                           GoodHierarchy K), SameGoodHierarchy C.good goodT

private theorem helper_fullBase_401.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (sigma : PartialEdgeColoring E k),
    let _ : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    ModColoring ett sigma →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE →
        CombinedStableColoring Tn base.closure Dn phi sigma) →
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
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    MaximumProperty corr.replacementETT ∧
      ∃ (baseT : HierarchyBase corr.replacementETT sigma),
        baseT.core = base.core ∧ baseT.closure = base.closure := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx sigma H n Tn Dn hsproper hsone hmod
      combined sigmaRoute corrData
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · have hb : TashkinovAugmentationSequence sigma Tn T := by
      rcases sigmaRoute with ⟨_, hseq⟩ | ⟨hk, rest⟩
      · exact hseq
      · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
    obtain ⟨corr, hMP, baseT, K0, hsame⟩ := HierarchySplitter G k e0 input T phi sigma
      ett C.maximum C.positive ctx.lowerRung base H hp ctx.proper ctx.oneEdgeUncolored
      hsproper hsone (combined hp) hb
    exact ⟨corr, hMP, baseT, hsame.1.symm, (hsame.2.2.2.2.2 hp).symm⟩
  · obtain ⟨corr⟩ := hmod.2.2 T ett.abovePenultimate ett.strictAbovePenultimate sigmaRoute
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

private theorem helper_parallelGood_530.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    alpha ∈
          TreeMissingColors phi
            (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))) ∧
        beta ∈
          TreeMissingColors phi
            (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))) →
    ∀ (z : V ⊕ E),
    TwoColorPathComponent G phi alpha beta z →
    ∀ (sigma : PartialEdgeColoring E k),
    sigma = TwoColorComponentSwap G phi alpha beta z →
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let Tnq : TreeSequence G e0 :=
        H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
      (0 : ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq ∨
        H.dividerCount = (0 : ℕ) ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn)) →
    (let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va))) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ)))) →
    alpha ∈ TreeMissingColors sigma A ∧ beta ∈ TreeMissingColors sigma A →
    alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) ∧
        beta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment base.core A →
    TreeSequenceInitialSegment Tn A →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    ¬TreeColorSetMinusClosed G sigma base.core
          ((HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
            (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))) ∧
      (4 : ℕ) ≤
        ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma base.closure) \
            (HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
              (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne hmissingPrefix z hpath sigma
      hsigma hcase hdisjoint H q A n Tn helem hstarMissing hgammaOutside lastZero coreToA TnToA
      treeMissingEq unaffected hp
  by_cases hz : H.dividerCount = 0
  · obtain ⟨hnot, hcard⟩ := C.good.parallelBase hp
    constructor
    · intro hclosed
      apply hnot
      intro c hc
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      obtain ⟨hb, hcol⟩ := Finset.mem_filter.mp hf
      have hm : c ∈ TreeMissingColors sigma base.core := by
        rw [treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset coreToA)]
        exact (Finset.mem_sdiff.mp hc).1
      have hq0 : q = 0 := Fin.ext (by simpa [q] using hz)
      have ha : alpha ∈ TreeMissingColors sigma base.core :=
        lastZero hz ▸ hstarMissing.1
      have hbeta : beta ∈ TreeMissingColors sigma base.core :=
        lastZero hz ▸ hstarMissing.2
      have hga : alpha ∉ (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
        simpa only [hq0] using hgammaOutside.1
      have hgb : beta ∉ (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
        simpa only [hq0] using hgammaOutside.2
      by_cases hfa : c = alpha
      · subst c
        by_cases hfz : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
        · have hs : sigma f = some beta := by
            simp [hsigma, TwoColorComponentSwap, hfz, hcol]
          have hh := hclosed beta (Finset.mem_sdiff.mpr ⟨hbeta, hgb⟩)
          have hmem : f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) beta :=
            Finset.mem_filter.mpr ⟨hb, hs⟩
          rw [hh] at hmem
          exact Finset.notMem_empty f hmem
        · have hs : sigma f = some alpha := by
            simp [hsigma, TwoColorComponentSwap, hfz, hcol]
          have hh := hclosed alpha (Finset.mem_sdiff.mpr ⟨ha, hga⟩)
          have hmem : f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) alpha :=
            Finset.mem_filter.mpr ⟨hb, hs⟩
          rw [hh] at hmem
          exact Finset.notMem_empty f hmem
      · by_cases hfb : c = beta
        · subst c
          by_cases hfz : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
          · have hs : sigma f = some alpha := by
              simp [hsigma, TwoColorComponentSwap, hfz, hcol, hne.symm]
            have hh := hclosed alpha (Finset.mem_sdiff.mpr ⟨ha, hga⟩)
            have hmem : f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) alpha :=
              Finset.mem_filter.mpr ⟨hb, hs⟩
            rw [hh] at hmem
            exact Finset.notMem_empty f hmem
          · have hs : sigma f = some beta := by
              simp [hsigma, TwoColorComponentSwap, hfz, hcol]
            have hh := hclosed beta (Finset.mem_sdiff.mpr ⟨hbeta, hgb⟩)
            have hmem : f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) beta :=
              Finset.mem_filter.mpr ⟨hb, hs⟩
            rw [hh] at hmem
            exact Finset.notMem_empty f hmem
        · have hh := hclosed c (Finset.mem_sdiff.mpr ⟨hm, (Finset.mem_sdiff.mp hc).2⟩)
          have hmem : f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) c :=
            Finset.mem_filter.mpr ⟨hb, (unaffected f c hfa hfb).mpr hcol⟩
          rw [hh] at hmem
          exact Finset.notMem_empty f hmem
    · have hclosure : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
        obtain ⟨u⟩ := (base.parallel hp).2.2
        intro v hv
        apply TreeSequenceInitialSegmentVertexSetSubset coreToA
        rw [u.vertexSet]
        exact Finset.mem_union_right _ hv
      rw [treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA),
        treeMissingEq base.closure hclosure]
      exact hcard
  · have hpos : 0 < H.dividerCount := Nat.pos_of_ne_zero hz
    obtain ⟨inputA, ettA, baseA, KA, goodA, _, hkind, hcount,
      hcoreA, hclosureA, hstageA, hstoredA, _⟩ :=
      (StableChangeCasesOneTwo G k e0 input T phi ett base C
        ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
        ctx.lexicographicMinimality helem ctx.largeMissingSet alpha beta hne
        hmissingPrefix z hpath sigma hsigma hcase hdisjoint).2.2.2 hpos
    have htreeA : ettA.series.data.tree (Fin.last ettA.rounds).castSucc = Tn := by
      rw [← KA.baseStage, hstageA 0]
      have hi : (⟨(0 : Fin (KA.dividerCount + 2)).val,
          by simp only [Fin.val_zero]; omega⟩ :
          Fin (C.hierarchy.dividerCount + 2)) = 0 := Fin.ext (by simp)
      rw [hi]
      exact H.baseStage
    have hs0 := hstoredA 0
    have hi0 : (⟨(0 : Fin (KA.dividerCount + 1)).val,
        by simp only [Fin.val_zero]; omega⟩ :
        Fin (H.dividerCount + 1)) = 0 := Fin.ext (by simp)
    have hgamma : (HierarchyStoredColorsAt KA 0).biUnion (goodA.gamma 0) =
        (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
      have hs : HierarchyStoredColorsAt KA 0 = HierarchyStoredColorsAt H 0 := by
        simpa only [hi0] using hs0.1
      apply Finset.biUnion_congr hs
      intro eta heta
      simpa only [hi0] using hs0.2 eta heta
    have hg := goodA.parallelBase (hkind.trans hp)
    rw [hcoreA, hclosureA, htreeA, hgamma] at hg
    exact hg

private theorem helper_segmentEq_708.{u_1, u_2} :
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
    (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
    TreeSequenceInitialSegment A T →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (H.stage j.castSucc) A) →
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
    (∀ (eta : Fin k),
        HierarchyFirstMissingPosition sigma A eta =
          HierarchyFirstMissingPosition phi A eta) →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑j : ℕ) < H.dividerCount →
    ∀ (eta : Fin k),
    HierarchySegmentColors K j eta = HierarchySegmentColors H j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn Dn hfixed AToT ordinaryToA
      corrT baseT hcoreT terminalData K starredEq firstEqA j hj eta
  let i : Fin (H.dividerCount + 1) := ⟨j.val + 1, by omega⟩
  have hi : i.castSucc = j.succ := Fin.ext rfl
  have hUA : TreeSequenceInitialSegment (H.stage j.succ) A := by
    rw [← hi]
    exact ordinaryToA i
  have cut : min (HierarchyFirstMissingPosition sigma T eta).val (H.stage j.succ).length =
      min (HierarchyFirstMissingPosition phi T eta).val (H.stage j.succ).length := by
    rw [← HierarchyFirstMissingPositionPrefixCutoff sigma A T AToT eta _ hUA.1,
      firstEqA eta, HierarchyFirstMissingPositionPrefixCutoff phi A T AToT eta _ hUA.1]
  unfold HierarchySegmentColors
  dsimp only
  rw [starredEq j, cut]
  apply Finset.filter_congr
  intro c _
  constructor <;> rintro ⟨r, hlo, hhi, hcol⟩ <;> refine ⟨r, hlo, hhi, ?_⟩
  · have he : sigma ((H.stage j.succ).edge r) = phi ((H.stage j.succ).edge r) := by
      rw [← hUA.2.2 r]; exact hfixed _
    exact he.symm.trans hcol
  · have he : sigma ((H.stage j.succ).edge r) = phi ((H.stage j.succ).edge r) := by
      rw [← hUA.2.2 r]; exact hfixed _
    exact he.trans hcol

private theorem helper_weak_543.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (if ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE then
        CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi
          sigma
      else
        StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma) →
    (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    HierarchyWeaklyStable H q sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A hbase hfixed hmissing
  cases hq : q using Fin.cases with
  | zero => exact hbase
  | succ i =>
    have hA : A = H.stage i.succ.castSucc := by
      dsimp only [A]
      rw [hq]
      rfl
    refine ⟨hbase, ?_⟩
    have he : ∀ t : Fin (H.stage i.succ.castSucc).length,
        sigma ((H.stage i.succ.castSucc).edge t) =
          phi ((H.stage i.succ.castSucc).edge t) := hA ▸ hfixed
    have hm : ∀ v ∈ TreeSequenceVertexSet (H.stage i.succ.castSucc),
        MissingColors G sigma v = MissingColors G phi v := by
      simpa only [hA] using hmissing
    exact ⟨fun t _ => he t, hm⟩

private theorem helper_transportPrefix_652.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (S X : TreeSequence G e0),
    TashkinovAugmentationSequence phi S X →
    TreeSequenceInitialSegment X A →
    TashkinovAugmentationSequence sigma S X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A hfixed segTrans treeMissingEq S X hseq
  unfold TashkinovAugmentationSequence at hseq ⊢
  induction hseq with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail U W hSU hUW ih =>
    intro hWA
    obtain ⟨hlen, hseg, c, hcolor, hcm⟩ := hUW
    have hUA := segTrans hseg hWA
    have hcSigma : c ∈ TreeMissingColors sigma U := by
      rw [treeMissingEq U (TreeSequenceInitialSegmentVertexSetSubset hUA)]
      exact hcm
    let t : Fin W.length := Fin.cast hlen.symm (Fin.last U.length)
    have he : sigma (W.edge t) = phi (W.edge t) := by
      rw [← hWA.2.2 t]
      exact hfixed _
    exact Relation.ReflTransGen.tail (ih hUA)
      ⟨hlen, hseg, c, he.trans hcolor, hcSigma⟩

private theorem helper_sigmaRoute_683.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
    sigma = TwoColorComponentSwap G phi alpha beta z →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    alpha ∈ TreeMissingColors sigma A ∧ beta ∈ TreeMissingColors sigma A →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S W →
          TreeSequenceInitialSegment U W →
            S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    TreeSequenceInitialSegment Tn A →
    TreeSequenceInitialSegment A T →
    (∀ {S U : TreeSequence G e0} (psi : PartialEdgeColoring E k),
        TreeSequenceInitialSegment S U →
          TreeMissingColors psi S ⊆ TreeMissingColors psi U) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S T →
          TreeSequenceInitialSegment S A → TashkinovAugmentationSequence sigma S T) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = { f } ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne z sigma hsigma H q A n Tn
      hstarMissing commonPrefix TnToA AToT missingSubset transportSuffix
  rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
    ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, _, _, hseq⟩
  · exact Or.inl ⟨hp, transportSuffix Tn hseq TnToA⟩
  · refine Or.inr ⟨hp, f, seed, hedges, hseed, ?_⟩
    by_cases hlen : seed.length ≤ A.length
    · exact transportSuffix seed hseq
        (commonPrefix (TashkinovAugmentationSequenceInitialSegment phi seed T hseq)
          AToT hlen)
    · have hAS : TreeSequenceInitialSegment A seed :=
        commonPrefix AToT (TashkinovAugmentationSequenceInitialSegment phi seed T hseq)
          (by omega)
      rw [hsigma] at hstarMissing ⊢
      exact TashkinovAugmentationSequenceComponentSwap G k e0 phi alpha beta hne z
        seed T hseq (missingSubset _ hAS hstarMissing.1)
          (missingSubset _ hAS hstarMissing.2)

private theorem helper_terminalAvoid_779.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (sigma : PartialEdgeColoring E k),
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) ∧
        beta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) →
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
    ∀ eta ∈ HierarchyStoredColorsAt H q,
    ∀ c ∈ C.good.gamma q eta,
    c ∈ HierarchySegmentColors K q eta →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma hstoredFirst H q n Tn Dn
      hgammaOutside corrT baseT hcoreT terminalData K starredEq unaffected eta heta c hc hseg
  have hgamma : c ∈ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) :=
    Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩
  have hca : c ≠ alpha := fun he => hgammaOutside.1 (he ▸ hgamma)
  have hcb : c ≠ beta := fun he => hgammaOutside.2 (he ▸ hgamma)
  unfold HierarchySegmentColors at hseg
  dsimp only at hseg
  rw [starredEq q, hstoredFirst eta heta] at hseg
  obtain ⟨_, r, hlo, hhi, hcol⟩ := Finset.mem_filter.mp hseg
  have hold : c ∈ HierarchySegmentColors H q eta :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, hlo, hhi,
      (unaffected _ c hca hcb).mp hcol⟩
  exact (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hc)).2 hold

private theorem helper_continuation_835.{u_1, u_2} :
    helperContinuation835Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne hmissingPrefix z hpath sigma
      hsigma hcase hdisjoint hstoredFirst H q A n Tn Dn helem houtside hmod hfixed hmissing
      hstarMissing hgammaOutside weak lastZero coreToA TnToA AToT ordinaryToA starredToA
      treeMissingEq corrT hmaximumT baseT hcoreT hclosureT terminalData K starredEq storedEq
      stageMissingEq unaffected
  have firstEqA (eta : Fin k) :
      HierarchyFirstMissingPosition sigma A eta = HierarchyFirstMissingPosition phi A eta := by
    exact TreeSequenceFirstMissingPositionCongr hmissing eta
  have segmentEq := @helper_segmentEq_708 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C sigma hfixed AToT ordinaryToA corrT baseT hcoreT
      terminalData starredEq firstEqA
  have terminalAvoid := @helper_terminalAvoid_779 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C alpha beta sigma hstoredFirst hgammaOutside corrT
      baseT hcoreT terminalData starredEq unaffected
  have parallelGood := @helper_parallelGood_530 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C ctx alpha beta hne hmissingPrefix z hpath sigma
      hsigma hcase hdisjoint helem hstarMissing hgammaOutside lastZero coreToA TnToA treeMissingEq
      unaffected
  let goodT : GoodHierarchy K := {
    gamma := C.good.gamma
    twoColors := by
      intro j eta heta
      exact C.good.twoColors j eta (by rw [storedEq j] at heta; exact heta)
    avoidance := by
      intro j eta heta c hc
      have ho : eta ∈ HierarchyStoredColorsAt H j := by rw [← storedEq j]; exact heta
      have old := C.good.avoidance j eta ho hc
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [stageMissingEq j]; exact (Finset.mem_sdiff.mp old).1
      · intro hseg
        by_cases hj : j.val < H.dividerCount
        · rw [segmentEq j hj eta] at hseg
          exact (Finset.mem_sdiff.mp old).2 hseg
        · have hjq : j = q := Fin.ext (by
            have hjlt : j.val < H.dividerCount + 1 := j.isLt
            dsimp [q]
            omega)
          subst j
          exact terminalAvoid eta ho c hc hseg
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
        exact hmissing v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA a.succ)
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
      have hpOld := terminalData.2.1.symm.trans hp
      change ¬ TreeColorSetMinusClosed G sigma baseT.core
          ((HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)) ∧
        4 ≤ ((TreeMissingColors sigma
          (corrT.replacementETT.series.data.tree
            (Fin.last corrT.replacementETT.rounds).castSucc) ∩
          TreeMissingColors sigma baseT.closure) \
            (HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)).card
      rw [hcoreT, hclosureT, terminalData.1, storedEq 0]
      exact parallelGood hpOld
    minusClosed := by
      intro a
      change TreeColorSetMinusClosed G sigma (H.stage a.succ.castSucc)
        ((HierarchyStoredColorsAt K a.succ).biUnion (C.good.gamma a.castSucc))
      rw [storedEq a.succ]
      have hstar : HierarchyStarredStage H a.succ = H.stage a.succ.castSucc := rfl
      rw [← hstar]
      exact P2813_T1_MinusClosedTransport G k e0 _ phi sigma alpha beta hne z hsigma
        ctx.proper ctx.oneEdgeUncolored _ (C.good.minusClosed a)
        (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset
          (starredToA a.succ) hv)) (houtside a.succ) }
  have same : SameGoodHierarchy C.good goodT := by
    refine ⟨?_, rfl, ?_⟩
    · refine ⟨hcoreT.symm, rfl, HEq.rfl, HEq.rfl, ?_, fun _ => hclosureT.symm⟩
      exact ⟨fun hp => terminalData.2.1.trans hp, fun hp => terminalData.2.1.symm.trans hp⟩
    · intro j
      exact ⟨(storedEq j).symm, fun _ _ => rfl⟩
  exact ⟨weak, hmod, corrT, hmaximumT, baseT, K, goodT, same⟩

private theorem helper_continuation_817.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    alpha ∈
          TreeMissingColors phi
            (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))) ∧
        beta ∈
          TreeMissingColors phi
            (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))) →
    ∀ (z : V ⊕ E),
    TwoColorPathComponent G phi alpha beta z →
    ∀ (sigma : PartialEdgeColoring E k),
    sigma = TwoColorComponentSwap G phi alpha beta z →
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let A : TreeSequence G e0 := HierarchyStarredStage H q;
      let Tnq : TreeSequence G e0 :=
        H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
      (0 : ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq ∨
        H.dividerCount = (0 : ℕ) ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn)) →
    (let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va))) →
    (let H : TashkinovHierarchy ett base := C.hierarchy;
      let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ)))) →
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
    ModColoring ett sigma →
    (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    alpha ∈ TreeMissingColors sigma A ∧ beta ∈ TreeMissingColors sigma A →
    alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) ∧
        beta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) →
    HierarchyWeaklyStable H q sigma →
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S W →
          TreeSequenceInitialSegment U W →
            S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    TreeSequenceInitialSegment base.core A →
    TreeSequenceInitialSegment Tn A →
    TreeSequenceInitialSegment A T →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (H.stage j.castSucc) A) →
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
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne hmissingPrefix z hpath sigma
      hsigma hcase hdisjoint hstoredFirst H q A n Tn Dn helem hbase hsproper hsone houtside hmod
      hfixed hmissing hstarMissing hgammaOutside weak segRefl segTrans commonPrefix lastZero
      coreToA TnToA AToT ordinaryToA
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A :=
    Fin.cases coreToA (fun i => ordinaryToA i.succ) j
  have combined (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      CombinedStableColoring Tn base.closure Dn phi sigma := by
    change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma) at hbase
    simpa only [ite_eq_left hp] using hbase
  have treeMissingEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) :
      TreeMissingColors sigma S = TreeMissingColors phi S :=
    Finset.biUnion_congr rfl (fun v hv => hmissing v (hS hv))
  have missingSubset {S U : TreeSequence G e0} (psi : PartialEdgeColoring E k)
      (hSU : TreeSequenceInitialSegment S U) :
      TreeMissingColors psi S ⊆ TreeMissingColors psi U := by
    intro c hc
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSU hv, hvc⟩
  have transportPrefix := @helper_transportPrefix_652 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C sigma hfixed segTrans treeMissingEq
  have transportSuffix (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S T)
      (hSA : TreeSequenceInitialSegment S A) :
      TashkinovAugmentationSequence sigma S T := by
    have hpre := TashkinovAugmentationSequenceRestrict phi S A T hseq hSA AToT
    have htail := TashkinovAugmentationSequenceSuffix phi S A T hseq hSA AToT
    have ht : TashkinovAugmentationSequence sigma A T := by
      rw [hsigma] at hstarMissing ⊢
      exact TashkinovAugmentationSequenceComponentSwap G k e0 phi alpha beta hne z
        A T htail hstarMissing.1 hstarMissing.2
    exact (transportPrefix S A hpre (segRefl A)).trans ht
  have sigmaRoute := @helper_sigmaRoute_683 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C alpha beta hne z sigma hsigma hstarMissing
      commonPrefix TnToA AToT missingSubset transportSuffix
  have corrData (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) :=
    corr.terminalData
  have fullBase := @helper_fullBase_401 V E inferInstance inferInstance inferInstance inferInstance
      G k e0 input T phi ett base C ctx sigma hsproper hsone hmod combined sigmaRoute corrData
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
    rw [terminalData.2.2, starredEq j,
      treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (starredToA j))]
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun a => ?_) j
    · change TreeMissingColors sigma
        (corrT.replacementETT.series.data.tree
          (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
      rw [terminalData.1]
      exact treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA)
    · exact treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA a.succ))
  have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      sigma f = some c ↔ phi f = some c := by
    rw [hsigma]
    by_cases hf : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
    · by_cases ha : phi f = some alpha
      · simp [TwoColorComponentSwap, hf, ha, hca.symm, hcb.symm]
      · by_cases hb : phi f = some beta
        · simp [TwoColorComponentSwap, hf, hb, hne.symm, hca.symm, hcb.symm]
        · simp [TwoColorComponentSwap, hf, ha, hb]
    · simp [TwoColorComponentSwap, hf]
  exact @helper_continuation_835 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx alpha beta hne hmissingPrefix z hpath sigma hsigma hcase
      hdisjoint hstoredFirst helem houtside hmod hfixed hmissing hstarMissing hgammaOutside weak
      lastZero coreToA TnToA AToT ordinaryToA starredToA treeMissingEq corrT hmaximumT baseT
      hcoreT hclosureT terminalData starredEq storedEq stageMissingEq unaffected
theorem StableChangeCasesOneTwoStarredTail {V E : Type*}
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
    (hstarMissing :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      alpha ∈ TreeMissingColors sigma A ∧
        beta ∈ TreeMissingColors sigma A)
    (hgammaOutside :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let Gamma := (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q)
      alpha ∉ Gamma ∧ beta ∉ Gamma)
    (_ :
      ∀ v, v ∈ TreeSequenceVertexSet
          (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) →
        MissingColors G sigma v = MissingColors G phi v)
    (hstoredFirst :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ∀ eta, eta ∈ HierarchyStoredColorsAt H q →
        HierarchyFirstMissingPosition sigma T eta =
          HierarchyFirstMissingPosition phi T eta) :
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
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi
      ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have controls := P2813_T1_BaseControl G k e0 input T phi ett base C ctx
    helem alpha beta hne hmissingPrefix z hpath sigma hsigma hcase hdisjoint
  rcases controls with ⟨hbase, hmissing, hsproper, hsone, houtside⟩
  have preStepElementary := @SharedFacts.FullTailTransport.preStepElementary V E inferInstance
      inferInstance
      inferInstance inferInstance G k e0 input T phi ett base C ctx
  have hfixed := P2813_T1_DisplayedEdges G k e0 input T phi ett base H C.good
    ctx.proper ctx.oneEdgeUncolored preStepElementary helem alpha beta z sigma hsigma
    hsone hbase houtside
  have rebuilt := P2813_T1_PrefixReconstruction G k e0 input T phi ett base C ctx
    sigma hsproper hsone hbase hfixed hmissing
  have hmod : ModColoring ett sigma := rebuilt.1
  change (∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t)) at hfixed
  change (∀ v ∈ TreeSequenceVertexSet A,
    MissingColors G sigma v = MissingColors G phi v) at hmissing
  change alpha ∈ TreeMissingColors sigma A ∧ beta ∈ TreeMissingColors sigma A
    at hstarMissing
  change alpha ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) ∧
    beta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) at hgammaOutside
  have weak := @helper_weak_543 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T phi ett base C sigma hbase hfixed hmissing
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    refine ⟨hSU.1.trans hUW.1, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hSU.1) i)).trans (hSU.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hSU.1 i)).trans (hSU.2.2 i)
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
    · intro i
      exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    induction d with
    | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    have hs := stageSegment j.val (H.dividerCount + 1 - j.val) (by omega)
    have he : (⟨j.val + (H.dividerCount + 1 - j.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
      Fin.ext (by simp only [Fin.val_last]; have := j.isLt; omega)
    simpa [he, H.terminalStage] using hs
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
  have AToT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]
      exact segTrans H.coreInsideFirst (stageToT ⟨1, by omega⟩)
    · rw [lastPositive hz]; exact stageToT _
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    by_cases hz : H.dividerCount = 0
    · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp; omega)
      rw [hj, H.baseStage]; exact TnToA
    · have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
      rw [lastPositive hz]
      convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;>
        simp only [Fin.val_castSucc]; omega
  exact @helper_continuation_817 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx alpha beta hne hmissingPrefix z hpath sigma hsigma hcase
      hdisjoint hstoredFirst helem hbase hsproper hsone houtside hmod hfixed hmissing
      hstarMissing hgammaOutside weak segRefl segTrans commonPrefix lastZero coreToA TnToA AToT
      ordinaryToA
end GoldbergSeymour

end
