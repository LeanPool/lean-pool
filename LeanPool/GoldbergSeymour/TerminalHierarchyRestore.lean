/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceFirstMissingPositionInvariant

public import LeanPool.GoldbergSeymour.HierarchyPrefixData
public import LeanPool.GoldbergSeymour.TerminalStoredColors
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseThreeData
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.GoodHierarchyCommonOriginalBaseTransport
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# P2752_T2_Terminal Hierarchy Restore

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_commonBase_214.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi) (C :
    HierarchyCounterexample base) (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma
    T), let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C
    - (1 : ℕ)); ∀ (old : ExtendedTashkinovTree G k e0 input Bplus phi), old.rounds =
    ett.rounds → old.series ≍ ett.series → ∀ (cp : CorrespondingExtendedTashkinovTree G k e0
    old sigma Bplus) (bp : HierarchyBase cp.replacementETT sigma), ∃ (b : HierarchyBase
    corr.replacementETT sigma), b.core = bp.core ∧ b.closure = bp.closure ∧
    (↑b.supportPosition : ℕ) = (↑bp.supportPosition : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett base C corr Bplus old hr hs cp bp
  cases old with
  | mk rounds positive series above strict below generating =>
    cases hr
    have hseries : series = ett.series := eq_of_heq hs
    cases hseries
    let cp' : CorrespondingExtendedTashkinovTree G k e0 ett sigma Bplus :=
      { replacementInput := cp.replacementInput
        replacementSeries := cp.replacementSeries
        replacementETT := cp.replacementETT
        rungAgreement := cp.rungAgreement
        seriesPresentation := cp.seriesPresentation
        finalGeneratingColoring := cp.finalGeneratingColoring
        ladderTreesAgree := cp.ladderTreesAgree
        storedColorsAgree := cp.storedColorsAgree
        connectingEdgesAgree := cp.connectingEdgesAgree
        extensionKindsAgree := cp.extensionKindsAgree
        replacementProper := cp.replacementProper
        replacementOneUncolored := cp.replacementOneUncolored
        replacementStable := cp.replacementStable }
    exact GoodHierarchyCommonOriginalBaseTransport G k e0 input T phi sigma
      ett Bplus T cp' bp corr

private theorem helper_stageBelow_335.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring
          E k)
      (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
          G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (F : HierarchyPrefixData C (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
          ℕ))) sigma)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
      let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1
          : ℕ));
      ∀ (_ : HierarchyBase corr.replacementETT sigma) (A : TreeSequence G e0)
        (HA : TashkinovHierarchy F.corresponding.replacementETT F.newBase) (j : Fin
            (HA.dividerCount + (1 : ℕ))),
        A = HA.stage j.castSucc → TreeSequenceInitialSegment A Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett base C F corr Bplus newBase A HA j heq
  have trans {A B U : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) (hBU : TreeSequenceInitialSegment B U) :
      TreeSequenceInitialSegment A U := by
    refine ⟨le_trans hAB.1 hBU.1, ?_, ?_⟩
    · intro i
      exact (hBU.2.1 (Fin.castLE (Nat.succ_le_succ hAB.1) i)).trans (hAB.2.1 i)
    · intro i
      exact (hBU.2.2 (Fin.castLE hAB.1 i)).trans (hAB.2.2 i)
  have stages : ∀ (a d : ℕ) (hb : a + d ≤ HA.dividerCount + 1),
      TreeSequenceInitialSegment (HA.stage ⟨a, by omega⟩)
        (HA.stage ⟨a+d, by omega⟩) := by
    intro a d
    induction d with
    | zero => intro hb; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    | succ d ih =>
      intro hb
      exact trans (ih (by omega)) (HA.nested ⟨a+d, by omega⟩)
  have hs := stages j.val (HA.dividerCount + 1 - j.val) (by omega)
  have hl : (⟨j.val + (HA.dividerCount + 1 - j.val), by omega⟩ :
      Fin (HA.dividerCount + 2)) = Fin.last (HA.dividerCount + 1) := by
    apply Fin.ext
    have := j.isLt
    simp
  rw [hl, HA.terminalStage] at hs
  have hj : (⟨j.val, by omega⟩ : Fin (HA.dividerCount + 2)) = j.castSucc :=
    Fin.ext rfl
  rw [hj] at hs
  rw [heq]
  exact hs

private theorem helper_segmentOriginal_459.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring
          E k)
      (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
          G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : HierarchyPrefixData C (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
          ℕ))) sigma),
      (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
        ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
          let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C -
              (1 : ℕ));
          let H : TashkinovHierarchy ett base := C.hierarchy;
          ∀ (newBase : HierarchyBase corr.replacementETT sigma) (hcore : newBase.core = base.core)
            (htree :
              corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
                ett.series.data.tree (Fin.last ett.rounds).castSucc),
            let K : TashkinovHierarchy corr.replacementETT newBase :=
              { dividerCount := H.dividerCount, stage := H.stage, baseStage := Eq.trans
                  H.baseStage (Eq.symm htree),
                terminalStage := H.terminalStage, nested := H.nested, strict := H.strict,
                dividerPosition := H.dividerPosition, dividerPositive := H.dividerPositive,
                dividerIncreasing := H.dividerIncreasing, dividerStage := H.dividerStage,
                coreInsideFirst :=
                  Eq.mpr
                    (id
                      (congrArg
                        (fun (_a : TreeSequence G e0) =>
                          TreeSequenceInitialSegment _a
                            (H.stage
                              (⟨(1 : ℕ), (by omega)⟩ : Fin (H.dividerCount + (2 : ℕ)))))
                        hcore))
                    H.coreInsideFirst :
                TashkinovHierarchy corr.replacementETT newBase };
            (∀ (j : Fin (H.dividerCount + (1 : ℕ))), HierarchyStarredStage K j =
                HierarchyStarredStage H j) →
              (∀ (j : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (H.stage
                  j.castSucc) Bplus) →
                (∀ (eta : Fin k), HierarchyFirstMissingPosition sigma T eta =
                    HierarchyFirstMissingPosition phi T eta) →
                  ∀ (j : Fin (H.dividerCount + (1 : ℕ))) (eta : Fin k),
                    HierarchySegmentColors K j eta = HierarchySegmentColors H j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett base C F hfixed corr Bplus H newBase hcore htree
      K starred ordinaryBelow firstMissing j eta
  have edgeEq (r : Fin (H.stage j.succ).length) :
      sigma ((H.stage j.succ).edge r) = phi ((H.stage j.succ).edge r) := by
    by_cases hj : j.val = H.dividerCount
    · have hi : j.succ = Fin.last (H.dividerCount + 1) := by
        apply Fin.ext
        simp [hj]
      revert r
      rw [hi, H.terminalStage]
      exact hfixed
    · let next : Fin (H.dividerCount + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
      have hi : next.castSucc = j.succ := Fin.ext rfl
      have hseg := ordinaryBelow next
      rw [hi] at hseg
      have he := (F.belowFull.2.2 (Fin.castLE hseg.1 r)).trans (hseg.2.2 r)
      have hf := hfixed (Fin.castLE F.belowFull.1 (Fin.castLE hseg.1 r))
      rw [he] at hf
      exact hf
  unfold HierarchySegmentColors
  dsimp only
  rw [starred j, firstMissing eta]
  apply Finset.filter_congr
  intro c hc
  constructor
  · rintro ⟨r, hlo, hhi, hcol⟩
    exact ⟨r, hlo, hhi, (edgeEq r).symm.trans hcol⟩
  · rintro ⟨r, hlo, hhi, hcol⟩
    exact ⟨r, hlo, hhi, (edgeEq r).trans hcol⟩

private theorem helper_oldMetadata_391.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring
          E k)
      (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
          G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (F : HierarchyPrefixData C (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
          ℕ))) sigma),
      let _ : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
      F.oldETT.series.data.tree (Fin.last F.oldETT.rounds).castSucc = ett.series.data.tree
          (Fin.last ett.rounds).castSucc ∧
        F.oldETT.series.data.kind (Fin.last F.oldETT.rounds) = ett.series.data.kind (Fin.last
            ett.rounds) ∧
          TashkinovStoredColors F.oldETT.series.data (Fin.last F.oldETT.rounds) =
            TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett base C F Bplus
  have transport
      (old : ExtendedTashkinovTree G k e0 input Bplus phi)
      (hr : old.rounds = ett.rounds) (hs : HEq old.series ett.series) :
      old.series.data.tree (Fin.last old.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
      old.series.data.kind (Fin.last old.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) ∧
      TashkinovStoredColors old.series.data (Fin.last old.rounds) =
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
    cases old with
    | mk rounds positive series above strict below generating =>
      cases hr
      cases eq_of_heq hs
      exact ⟨rfl, rfl, rfl⟩
  exact transport F.oldETT F.oldRung F.oldSeries

private theorem helper_coreBelow_472.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring
          E k)
      (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
          G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (F : HierarchyPrefixData C (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
          ℕ))) sigma)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
      let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1
          : ℕ));
      let H : TashkinovHierarchy ett base := C.hierarchy;
      ∀ (newBase : HierarchyBase corr.replacementETT sigma),
        newBase.core = F.newBase.core →
          F.newHierarchy.dividerCount = H.dividerCount →
            (∀ (A : TreeSequence G e0) (HA : TashkinovHierarchy F.corresponding.replacementETT
                F.newBase)
                (j : Fin (HA.dividerCount + (1 : ℕ))), A = HA.stage j.castSucc →
                    TreeSequenceInitialSegment A Bplus) →
              TreeSequenceInitialSegment newBase.core Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett base C F corr Bplus H newBase hcoreP hcount
      stageBelow
  rw [hcoreP]
  have first := F.newHierarchy.coreInsideFirst
  by_cases hq : F.newHierarchy.dividerCount = 0
  · have hi : (⟨1, by omega⟩ : Fin (F.newHierarchy.dividerCount + 2)) =
        Fin.last (F.newHierarchy.dividerCount + 1) := by apply Fin.ext; simp [hq]
    rw [hi, F.newHierarchy.terminalStage] at first
    exact first
  · have next := stageBelow _ F.newHierarchy ⟨1, by omega⟩ rfl
    refine ⟨le_trans first.1 next.1, ?_, ?_⟩
    · intro i
      exact
        (next.2.1 (Fin.castLE (Nat.succ_le_succ first.1) i)).trans (first.2.1 i)
    · intro i
      exact
        (next.2.2 (Fin.castLE first.1 i)).trans (first.2.2 i)

private theorem helper_gammaOriginal_542.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring
          E k)
      (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
          G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (F : HierarchyPrefixData C (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 :
          ℕ))) sigma),
      let H : TashkinovHierarchy ett base := C.hierarchy;
      ∀ (hcount : F.newHierarchy.dividerCount = H.dividerCount),
        let index : Fin (H.dividerCount + (1 : ℕ)) → Fin (F.newHierarchy.dividerCount + (1 : ℕ)) :=
          fun (j : Fin (H.dividerCount + (1 : ℕ))) =>
              Fin.cast (congrArg (fun (n : ℕ) => n + (1 : ℕ)) (Eq.symm hcount)) j;
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
          ∀ eta ∈ HierarchyStoredColorsAt H j, F.newGood.gamma (index j) eta = C.good.gamma j eta
             := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett base C F H hcount index j eta heta
  obtain ⟨hc, hgamma⟩ := F.sameGood.2
  let jo : Fin (F.oldHierarchy.dividerCount + 1) :=
    Fin.cast (congrArg (fun n => n + 1) F.oldCount.symm) j
  have hi : Fin.cast (congrArg (fun n => n + 1) hc) jo = index j := Fin.ext rfl
  have ho : Fin.cast (congrArg (fun n => n + 1) F.oldCount) jo = j := Fin.ext rfl
  have hcolors := F.oldColors jo
  have he : eta ∈ HierarchyStoredColorsAt F.oldHierarchy jo := by
    rw [hcolors.1]
    simpa only [ho] using heta
  have hg := (hgamma jo).2 eta he
  rw [hi] at hg
  exact hg.symm.trans (by simpa only [ho] using (hcolors.2.2 eta).1)

private theorem helper_continuation_562.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring
          E k)
      (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree
          G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (D : HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx),
      ∀ beta ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 :
          ℕ))),
        sigma = TwoColorComponentSwap G phi D.alpha beta (Sum.inl (T.vertex
            D.terminalVertexIndex)) →
          ∀ (F : HierarchyPrefixData C (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1
              : ℕ))) sigma),
            (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
              ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C
                    (HierarchyFullTailLength C - (1 : ℕ));
                let H : TashkinovHierarchy ett base := C.hierarchy;
                (∀ {inp gen : PartialEdgeColoring E k} {U : TreeSequence G e0}
                    (original : ExtendedTashkinovTree G k e0 inp U gen) (W : TreeSequence G e0)
                    (c : CorrespondingExtendedTashkinovTree G k e0 original sigma W),
                    c.replacementETT.series.data.tree (Fin.last c.replacementETT.rounds).castSucc =
                        original.series.data.tree (Fin.last original.rounds).castSucc ∧
                      c.replacementETT.series.data.kind (Fin.last c.replacementETT.rounds) =
                        original.series.data.kind (Fin.last original.rounds)) →
                  ∀ (newBase : HierarchyBase corr.replacementETT sigma),
                    newBase.core = F.newBase.core →
                      newBase.closure = F.newBase.closure →
                        ∀ (hcore : newBase.core = base.core)
                          (htree :
                            corr.replacementETT.series.data.tree (Fin.last
                                corr.replacementETT.rounds).castSucc =
                              ett.series.data.tree (Fin.last ett.rounds).castSucc),
                          corr.replacementETT.series.data.kind (Fin.last
                              corr.replacementETT.rounds) =
                              ett.series.data.kind (Fin.last ett.rounds) →
                            let K : TashkinovHierarchy corr.replacementETT newBase :=
                              { dividerCount := H.dividerCount, stage := H.stage,
                                baseStage := Eq.trans H.baseStage (Eq.symm htree), terminalStage
                                   := H.terminalStage,
                                nested := H.nested, strict := H.strict, dividerPosition :=
                                    H.dividerPosition,
                                dividerPositive := H.dividerPositive, dividerIncreasing :=
                                    H.dividerIncreasing,
                                dividerStage := H.dividerStage,
                                coreInsideFirst :=
                                  Eq.mpr
                                    (id
                                      (congrArg
                                        (fun (_a : TreeSequence G e0) =>
                                          TreeSequenceInitialSegment _a
                                            (H.stage
                                              (⟨(1 : ℕ), (by omega)⟩ :
                                                Fin (H.dividerCount + (2 : ℕ)))))
                                        hcore))
                                    H.coreInsideFirst :
                                TashkinovHierarchy corr.replacementETT newBase };
                            F.oldETT.series.data.tree (Fin.last F.oldETT.rounds).castSucc =
                                  ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
                                F.oldETT.series.data.kind (Fin.last F.oldETT.rounds) =
                                    ett.series.data.kind (Fin.last ett.rounds) ∧
                                  TashkinovStoredColors F.oldETT.series.data (Fin.last
                                      F.oldETT.rounds) =
                                    TashkinovStoredColors ett.series.data (Fin.last ett.rounds) →
                              F.oldETT.series.data.kind (Fin.last F.oldETT.rounds) =
                                  ett.series.data.kind (Fin.last ett.rounds) →
                                SameHierarchyStages H K →
                                  ∀ (hcount : F.newHierarchy.dividerCount = H.dividerCount),
                                    let index :
                                      Fin (H.dividerCount + (1 : ℕ)) → Fin
                                          (F.newHierarchy.dividerCount + (1 : ℕ)) :=
                                      fun (j : Fin (H.dividerCount + (1 : ℕ))) =>
                                      Fin.cast (congrArg (fun (n : ℕ) =>
                                          n + (1 : ℕ)) (Eq.symm hcount)) j;
                                    let _ : Fin H.dividerCount → Fin F.newHierarchy.dividerCount :=
                                      fun (i : Fin H.dividerCount) => Fin.cast (Eq.symm hcount) i;
                                    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                        F.newHierarchy.stage (index j).castSucc = H.stage
                                            j.castSucc) →
                                      (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                          HierarchyStarredStage K j = HierarchyStarredStage H j) →
                                        (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                                            HierarchyStarredStage K j = HierarchyStarredStage
                                                F.newHierarchy (index j)) →
                                          (∀ (A : TreeSequence G e0)
                                              (HA : TashkinovHierarchy
                                                  F.corresponding.replacementETT F.newBase)
                                              (j : Fin (HA.dividerCount + (1 : ℕ))),
                                              A = HA.stage j.castSucc →
                                                  TreeSequenceInitialSegment A Bplus) →
                                            ∃ (newBase : HierarchyBase corr.replacementETT sigma)
                                                (K :
                                              TashkinovHierarchy corr.replacementETT newBase)
                                                  (good : GoodHierarchy K),
                                              SameGoodHierarchy C.good good := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett base C ctx D beta hmissing hsigma F hfixed corr
      Bplus H terminalData newBase hcoreP hclosureP hcore htree hkind K oldMetadata oldKind
      sameStages hcount index internal prefixStage starred starredP stageBelow
  have ordinaryBelow (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) Bplus :=
    stageBelow _ F.newHierarchy (index j) (prefixStage j).symm
  have coreBelow := @helper_coreBelow_472 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi sigma ett base C F corr newBase hcoreP hcount stageBelow
  have starredBelow (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage K j) Bplus := by
    cases j using Fin.cases with
    | zero => exact coreBelow
    | succ i => exact ordinaryBelow i.succ
  have missingEq (A : TreeSequence G e0) (hA : TreeSequenceInitialSegment A Bplus) :
      TreeMissingColors sigma A = TreeMissingColors phi A := by
    unfold TreeMissingColors
    apply Finset.biUnion_congr rfl
    intro v hv
    exact F.invariant.2 v (TreeSequenceInitialSegmentVertexSetSubset hA hv)
  have storedOriginal (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [P2752_T2_TerminalStoredColors ett corr, missingEq _ (starredBelow j), starred j]
  have missingOriginal (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j = HierarchyStageMissingColors H j := by
    cases j using Fin.cases with
    | zero =>
      simp only [HierarchyStageMissingColors, Fin.cases_zero]
      rw [htree]
      exact missingEq _ F.ladderBelow
    | succ i =>
      simp only [HierarchyStageMissingColors, Fin.cases_succ]
      exact missingEq _ (ordinaryBelow i.succ)
  have prefixTree : F.corresponding.replacementETT.series.data.tree
        (Fin.last F.corresponding.replacementETT.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    exact (terminalData F.oldETT Bplus F.corresponding).1.trans oldMetadata.1
  have prefixComputed : TashkinovStoredColors F.corresponding.replacementETT.series.data
        (Fin.last F.corresponding.replacementETT.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
    rw [P2752_T2_TerminalStoredColors F.oldETT F.corresponding]
    exact oldMetadata.2.2
  have storedP (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K j = HierarchyStoredColorsAt F.newHierarchy (index j) := by
    unfold HierarchyStoredColorsAt
    dsimp only
    rw [P2752_T2_TerminalStoredColors ett corr, prefixComputed, starredP j]
  have missingP (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K j =
        HierarchyStageMissingColors F.newHierarchy (index j) := by
    cases j using Fin.cases with
    | zero =>
      have hi : index 0 = 0 := Fin.ext rfl
      simp only [hi, HierarchyStageMissingColors, Fin.cases_zero]
      rw [htree, prefixTree]
    | succ i =>
      have hi : index i.succ = (internal i).succ := Fin.ext rfl
      simp only [hi, HierarchyStageMissingColors, Fin.cases_succ]
      have hs := prefixStage i.succ
      rw [hi] at hs
      exact congrArg (TreeMissingColors sigma) hs.symm
  have gammaOriginal := @helper_gammaOriginal_542 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi sigma ett base C F hcount
  have firstMissing (eta : Fin k) :
      HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition phi T eta := by
    exact T.firstMissingPosition_eq_of_prefix_agreement F.belowFull F.penultimateLength.le
      F.invariant.2 eta
  have segmentOriginal := @helper_segmentOriginal_459 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi sigma ett base C F hfixed corr newBase hcore htree starred
      ordinaryBelow firstMissing
  let good : GoodHierarchy K :=
    { gamma := fun j eta => F.newGood.gamma (index j) eta
      twoColors := by
        intro j eta he
        exact F.newGood.twoColors (index j) eta ((storedP j) ▸ he)
      avoidance := by
        intro j eta he
        have ho : eta ∈ HierarchyStoredColorsAt H j := (storedOriginal j) ▸ he
        rw [gammaOriginal j eta ho, missingOriginal j, segmentOriginal j eta]
        exact C.good.avoidance j eta ho
      disjointPairs := by
        intro j eta theta he ht hne
        exact F.newGood.disjointPairs (index j) eta theta
          ((storedP j) ▸ he) ((storedP j) ▸ ht) hne
      uniqueRefresh := by
        intro i
        have hi : (internal i).succ = index i.succ := Fin.ext rfl
        have hc : (internal i).castSucc = index i.castSucc := Fin.ext rfl
        simpa only [hi, hc, storedP, starredP, prefixStage] using
          F.newGood.uniqueRefresh (internal i)
      parallelBase := by
        dsimp only
        intro hp
        have prefixKind : F.corresponding.replacementETT.series.data.kind
            (Fin.last F.corresponding.replacementETT.rounds) =
          ett.series.data.kind (Fin.last ett.rounds) :=
            (terminalData F.oldETT Bplus F.corresponding).2.trans oldKind
        have hg := F.newGood.parallelBase (prefixKind.trans (hkind.symm.trans hp))
        have hi : index 0 = 0 := Fin.ext rfl
        simpa only [hcoreP, hclosureP, htree, prefixTree, storedP, hi] using hg
      minusClosed := by
        intro i
        have hi : (internal i).succ = index i.succ := Fin.ext rfl
        have hc : (internal i).castSucc = index i.castSucc := Fin.ext rfl
        simpa only [hi, hc, storedP, prefixStage] using
          F.newGood.minusClosed (internal i) }
  refine ⟨newBase, K, good, sameStages, rfl, ?_⟩
  intro j
  refine ⟨(storedOriginal j).symm, ?_⟩
  intro eta he
  exact (gammaOriginal j eta he).symm

theorem P2752_T2_TerminalHierarchyRestore {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeData G k e0 input T phi ett base C ctx)
    (beta : Fin k)
    (hmissing : beta ∈ TreeMissingColors phi
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)))
    (_ : beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex))
    (hsigma : sigma = TwoColorComponentSwap G phi D.alpha beta
      (Sum.inl (T.vertex D.terminalVertexIndex)))
    (F : HierarchyPrefixData C
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) sigma)
    (hfixed : ∀ t : Fin T.length, sigma (T.edge t) = phi (T.edge t))
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) :
    ∃ newBase : HierarchyBase corr.replacementETT sigma,
      ∃ K : TashkinovHierarchy corr.replacementETT newBase,
        ∃ good : GoodHierarchy K, SameGoodHierarchy C.good good := by
  classical
  let Bplus := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  let H := C.hierarchy
  have terminalData := @GoldbergSeymour.CorrespondingExtendedTashkinovTree.terminalTreeKind V E
      inferInstance inferInstance inferInstance G k e0
      sigma
  have commonBase := @helper_commonBase_214 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi sigma ett base C corr
  obtain ⟨newBase, hcoreP, hclosureP, hsupportP⟩ :=
    commonBase F.oldETT F.oldRung F.oldSeries F.corresponding F.newBase
  have sameP := F.sameGood.1
  have hcore : newBase.core = base.core :=
    hcoreP.trans (sameP.1.symm.trans F.oldCore)
  have htree := (terminalData ett T corr).1
  have hkind := (terminalData ett T corr).2
  let K : TashkinovHierarchy corr.replacementETT newBase :=
    { dividerCount := H.dividerCount
      stage := H.stage
      baseStage := H.baseStage.trans htree.symm
      terminalStage := H.terminalStage
      nested := H.nested
      strict := H.strict
      dividerPosition := H.dividerPosition
      dividerPositive := H.dividerPositive
      dividerIncreasing := H.dividerIncreasing
      dividerStage := H.dividerStage
      coreInsideFirst := by rw [hcore]; exact H.coreInsideFirst }
  have oldMetadata := @helper_oldMetadata_391 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi sigma ett base C F
  have oldKind := oldMetadata.2.1
  have sameStages : SameHierarchyStages H K := by
    refine ⟨hcore.symm, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
    · exact ⟨fun h => hkind.trans h, fun h => hkind.symm.trans h⟩
    · intro hp
      have hpOld : F.oldETT.series.data.kind (Fin.last F.oldETT.rounds) =
          some TashkinovExtensionKind.PE := oldKind.trans hp
      exact F.oldClosure.symm.trans ((sameP.2.2.2.2.2 hpOld).trans hclosureP.symm)
  have hcount : F.newHierarchy.dividerCount = H.dividerCount :=
    sameP.2.1.symm.trans F.oldCount
  let index (j : Fin (H.dividerCount + 1)) :
      Fin (F.newHierarchy.dividerCount + 1) :=
    Fin.cast (congrArg (fun n => n + 1) hcount.symm) j
  let internal (i : Fin H.dividerCount) : Fin F.newHierarchy.dividerCount :=
    Fin.cast hcount.symm i
  have applyHEq {n m : ℕ} (f : Fin n → TreeSequence G e0)
      (g : Fin m → TreeSequence G e0) (h : n = m) (hf : HEq f g)
      (i : Fin n) : f i = g (Fin.cast h i) := by
    cases h
    cases hf
    rfl
  have prefixStage (j : Fin (H.dividerCount + 1)) :
      F.newHierarchy.stage (index j).castSucc = H.stage j.castSucc := by
    let jo : Fin (F.oldHierarchy.dividerCount + 1) :=
      Fin.cast (congrArg (fun n => n + 1) F.oldCount.symm) j
    have hs := applyHEq F.oldHierarchy.stage F.newHierarchy.stage
      (congrArg (fun n => n + 2) sameP.2.1) sameP.2.2.1 jo.castSucc
    have hi : Fin.cast (congrArg (fun n => n + 2) sameP.2.1) jo.castSucc =
        (index j).castSucc := Fin.ext rfl
    have ho : Fin.cast (congrArg (fun n => n + 1) F.oldCount) jo = j :=
      Fin.ext rfl
    rw [hi] at hs
    exact hs.symm.trans (by simpa only [ho] using (F.oldStages jo).1)
  have starred (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage H j := by
    cases j using Fin.cases with
    | zero => exact hcore
    | succ i => rfl
  have starredP (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K j = HierarchyStarredStage F.newHierarchy (index j) := by
    cases j using Fin.cases with
    | zero =>
      have hi : index 0 = 0 := Fin.ext rfl
      rw [hi]
      exact hcoreP
    | succ i =>
      have hi : index i.succ = (internal i).succ := Fin.ext rfl
      simp only [hi, HierarchyStarredStage, Fin.cases_succ]
      have hs := prefixStage i.succ
      rw [hi] at hs
      exact hs.symm
  have stageBelow := @helper_stageBelow_335 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi sigma ett base C F corr newBase
  exact @helper_continuation_562 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi sigma ett base C ctx D beta hmissing hsigma F hfixed corr terminalData
      newBase hcoreP hclosureP hcore htree hkind oldMetadata oldKind sameStages hcount
      prefixStage starred starredP stageBelow
end GoldbergSeymour

end
