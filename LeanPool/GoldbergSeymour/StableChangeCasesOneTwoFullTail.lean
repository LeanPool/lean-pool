/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFieldTransport

public import LeanPool.GoldbergSeymour.HierarchyFullBaseTransport

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.SharedFacts.FullTailTransport

public import LeanPool.GoldbergSeymour.SharedFacts.StableChangeCasesOneTwoSplitTail

public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTailAtLeastTwo
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.BaseControl
public import LeanPool.GoldbergSeymour.DisplayedEdges
public import LeanPool.GoldbergSeymour.RecoloredPrefixReconstruction
public import LeanPool.GoldbergSeymour.MinusClosedTransport
public import LeanPool.GoldbergSeymour.PrefixSegmentTransport

/-!
# Stable Change Cases One Two Full Tail

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation1123Conditions.{u_1, u_2} : Prop :=
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
        (∀
          v ∈
           TreeSequenceVertexSet (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))),
          MissingColors G sigma v = MissingColors G phi v) →
         (let H : TashkinovHierarchy ett base := C.hierarchy;
          let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
          ∀ eta ∈ HierarchyStoredColorsAt H q,
           HierarchyFirstMissingPosition sigma T eta = HierarchyFirstMissingPosition phi T eta) →
          let H : TashkinovHierarchy ett base := C.hierarchy;
          let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
          let A : TreeSequence G e0 := HierarchyStarredStage H q;
          let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
          let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
          let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
          let B : TreeSequence G e0 :=
           HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
          (2 : ℕ) ≤ T.length - A.length →
           (if ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE then
             CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
              base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma
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
                (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) =
                   ett.series.data.tree (Fin.last ett.rounds).castSucc ∨
                  ∃ (corr :
                   CorrespondingExtendedTashkinovTree G k e0 ett sigma
                    (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount))),
                   MaximumProperty corr.replacementETT) →
                 (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
                  (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
                   (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → sigma (T.edge t) = phi (T.edge t)) →
                    (∀ {S U W : TreeSequence G e0},
                      TreeSequenceInitialSegment S U →
                       TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
                     (∀ {S U W : TreeSequence G e0},
                       TreeSequenceInitialSegment S W →
                        TreeSequenceInitialSegment U W →
                         S.length ≤ U.length → TreeSequenceInitialSegment S U) →
                      (∀ {S U : TreeSequence G e0},
                        TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
                       (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
                         TreeSequenceInitialSegment
                          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
                          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
                        (∀ (j : Fin (H.dividerCount + (2 : ℕ))),
                          TreeSequenceInitialSegment (H.stage j) T) →
                         (H.dividerCount = (0 : ℕ) → A = base.core) →
                          (H.dividerCount ≠ (0 : ℕ) → A = H.stage q.castSucc) →
                           TreeSequenceInitialSegment base.core A →
                            TreeSequenceInitialSegment Tn base.core →
                             TreeSequenceInitialSegment Tn A →
                              TreeSequenceInitialSegment A T →
                               let H : TashkinovHierarchy ett base := C.hierarchy;
                               let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                               let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
                               let A : TreeSequence G e0 := HierarchyStarredStage H q;
                               let Tnq : TreeSequence G e0 :=
                                H.stage
                                 (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
                               let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
                               let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
                               HierarchyWeaklyStable H q sigma ∧
                                ModColoring ett sigma ∧
                                 (A = Tn ∨
                                   ∃ (inputA : PartialEdgeColoring E k) (ettA :
                                    ExtendedTashkinovTree G k e0 inputA A sigma),
                                    MaximumProperty ettA) ∧
                                  ((0 : ℕ) < H.dividerCount →
                                    ∃ (inputA : PartialEdgeColoring E k) (ettA :
                                     ExtendedTashkinovTree G k e0 inputA A sigma) (baseA :
                                     HierarchyBase ettA sigma) (K : TashkinovHierarchy ettA baseA)
                                     (goodA : GoodHierarchy K),
                                     MaximumProperty ettA ∧
                                      ∃ (hcount : K.dividerCount + (1 : ℕ) = H.dividerCount),
                                       baseA.core = base.core ∧
                                        baseA.closure = base.closure ∧
                                         (∀ (j : Fin (K.dividerCount + (2 : ℕ))),
                                           K.stage j =
                                            H.stage
                                             (⟨(↑j : ℕ), by omega⟩ :
                                              Fin (H.dividerCount + (2 : ℕ)))) ∧
                                          (∀ (j : Fin (K.dividerCount + (1 : ℕ))),
                                            let jH : Fin (H.dividerCount + (1 : ℕ)) :=
                                             (⟨(↑j : ℕ), by omega⟩ :
                                              Fin (H.dividerCount + (1 : ℕ)));
                                            HierarchyStoredColorsAt K j =
                                              HierarchyStoredColorsAt H jH ∧
                                             ∀ eta ∈ HierarchyStoredColorsAt K j,
                                              goodA.gamma j eta = C.good.gamma jH eta) ∧
                                           TreeColorSetMinusClosed G sigma Tnq
                                            (Dnq.biUnion
                                             (C.good.gamma
                                              (⟨C.hierarchy.dividerCount - (1 : ℕ), by omega⟩ :
                                               Fin (C.hierarchy.dividerCount + (1 : ℕ)))))) ∧
                                   ∃ (corrT :
                                    CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
                                    MaximumProperty corrT.replacementETT ∧
                                     ∃ (baseT : HierarchyBase corrT.replacementETT sigma) (K :
                                      TashkinovHierarchy corrT.replacementETT baseT) (goodT :
                                      GoodHierarchy K), SameGoodHierarchy C.good goodT

private theorem helper_segmentEq_489.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (sigma : PartialEdgeColoring E k),
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
    (∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t)) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage j) T) →
    TreeSequenceInitialSegment A T →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (H.stage j.castSucc) A) →
    (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
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
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt H j,
    HierarchySegmentColors K j eta = HierarchySegmentColors H j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma hstoredFirst H q A n Tn Dn fixedA
      missingA stageToT AToT ordinaryToA fixedT corrT baseT hcoreT terminalData K starredEq j eta
      heta
  by_cases hj : j.val < H.dividerCount
  · have hjA : TreeSequenceInitialSegment (H.stage j.succ) A := by
      let js : Fin (H.dividerCount + 1) := ⟨j.val + 1, by omega⟩
      have he : js.castSucc = j.succ := Fin.ext rfl
      simpa only [he] using ordinaryToA js
    have hcut := HierarchyFirstMissingPositionPrefixCutoff sigma A T AToT eta
      (H.stage j.succ).length hjA.1
    have hseg := P2813_T1_PrefixSegmentTransport phi sigma (H.stage j.succ) A T
      hjA AToT fixedA missingA eta (HierarchyStarredStage H j).length
    unfold HierarchySegmentColors
    dsimp only
    rw [starredEq j, ← hcut]
    exact hseg
  · have he : j = q := Fin.ext (by simp [q]; have := j.isLt; omega)
    subst j
    unfold HierarchySegmentColors
    dsimp only
    rw [starredEq q, hstoredFirst eta heta]
    apply Finset.filter_congr
    intro c _
    constructor <;> rintro ⟨t, hlo, hhi, hc⟩ <;> refine ⟨t, hlo, hhi, ?_⟩
    · change sigma ((H.stage q.succ).edge t) = some c at hc
      have hf : sigma ((H.stage q.succ).edge t) = phi ((H.stage q.succ).edge t) := by
        rw [← (stageToT q.succ).2.2 t]
        exact fixedT _
      exact hf.symm.trans hc
    · have hf : sigma ((H.stage q.succ).edge t) = phi ((H.stage q.succ).edge t) := by
        rw [← (stageToT q.succ).2.2 t]
        exact fixedT _
      exact hf.trans hc

private theorem helper_parallelNotClosed_549.{u_1, u_2} :
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
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S W →
          TreeSequenceInitialSegment U W →
            S.length ≤ U.length → TreeSequenceInitialSegment S U) →
    (∀ {S U : TreeSequence G e0},
        TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage j) T) →
    TreeSequenceInitialSegment base.core A →
    TreeSequenceInitialSegment Tn base.core →
    TreeSequenceInitialSegment A T →
    (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    base.core.length <
        (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))).length →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    ¬TreeColorSetMinusClosed G sigma base.core
        ((HierarchyStoredColorsAt H (0 : Fin (H.dividerCount + (1 : ℕ)))).biUnion
          (C.good.gamma (0 : Fin (C.hierarchy.dividerCount + (1 : ℕ))))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma H q A n Tn segTrans commonPrefix
      equalTrees stageToT coreToA TnToCore AToT fixedT treeMissingEq coreStrict hp
  have hseq : TashkinovAugmentationSequence phi Tn T := by
    rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
      ⟨_, hseq⟩ | ⟨hk, rest⟩
    · exact hseq
    · rcases hk with hk | hk <;> rw [hp] at hk <;> cases hk
  have coreToT := segTrans coreToA AToT
  have suffix := TashkinovAugmentationSequenceSuffix phi Tn base.core T
    hseq TnToCore coreToT
  let t : Fin T.length := ⟨base.core.length, by
    have := (stageToT ⟨1, by omega⟩).1
    omega⟩
  let S := TreeSequencePrefix T t.val base.core.positive (Nat.le_of_lt t.isLt)
  let U := TreeSequencePrefix T (t.val + 1) (by have := base.core.positive; omega)
    (Nat.succ_le_of_lt t.isLt)
  have hS : S = base.core := by
    apply (equalTrees (commonPrefix coreToT
      (show TreeSequenceInitialSegment S T from
        ⟨Nat.le_of_lt t.isLt, fun _ => rfl, fun _ => rfl⟩) le_rfl) rfl).symm
  have aug := (TashkinovAugmentationSequencePosition phi base.core T suffix t le_rfl).1
  change TashkinovAugmentation phi S U at aug
  obtain ⟨hlen, hSU, c, hcol, hcm⟩ := aug
  have hcolT : phi (T.edge t) = some c := by
    have he : U.edge (Fin.cast hlen.symm (Fin.last S.length)) = T.edge t := by
      change T.edge _ = T.edge t
      apply congrArg T.edge
      apply Fin.ext
      rfl
    rw [← he]
    exact hcol
  have hcmCore : c ∈ TreeMissingColors phi base.core := hS ▸ hcm
  have hcSigma : c ∈ TreeMissingColors sigma base.core := by
    rw [treeMissingEq base.core coreToA]; exact hcmCore
  have hreserved : c ∉ (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
    intro hc
    obtain ⟨eta, heta, hcg⟩ := Finset.mem_biUnion.mp hc
    have hn : eta ∉ TreeMissingColors phi base.core := (Finset.mem_sdiff.mp heta).2
    have hfirst : base.core.length < (HierarchyFirstMissingPosition phi T eta).val := by
      exact TreeSequenceFirstMissingPositionAfterPrefix coreToT t.isLt hn
    have hseg : c ∈ HierarchySegmentColors H 0 eta := by
      let r : Fin (H.stage (0 : Fin (H.dividerCount + 1)).succ).length :=
        ⟨base.core.length, coreStrict⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, r, le_rfl, Nat.lt_min.mpr ⟨hfirst, coreStrict⟩, ?_⟩
      have he : Fin.castLE (stageToT (0 : Fin (H.dividerCount + 1)).succ).1 r = t := Fin.ext rfl
      rw [← (stageToT (0 : Fin (H.dividerCount + 1)).succ).2.2 r, he]
      exact hcolT
    exact (Finset.mem_sdiff.mp (C.good.avoidance 0 eta heta hcg)).2 hseg
  have hboundary : T.edge t ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) := by
    clear * - T t base coreToT
    obtain ⟨i, hi⟩ := T.attaches t
    let old : Fin (base.core.length + 1) := ⟨i.val, i.isLt⟩
    let it : Fin (T.length + 1) := Fin.castLE (Nat.succ_le_succ coreToT.1) old
    have hOld : T.vertex it = base.core.vertex old := coreToT.2.1 old
    have hNew : T.vertex t.succ ∉ TreeSequenceVertexSet base.core := by
      intro hv
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨j, hj⟩ := hv
      have he := T.vertex_injective (hj.symm.trans (coreToT.2.1 j).symm)
      have hval := congrArg Fin.val he
      have := j.isLt
      change base.core.length + 1 = j.val at hval
      omega
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨T.vertex it, ?_, T.vertex t.succ, hNew, ?_⟩
    · rw [hOld]
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨old, rfl⟩
    · have he : Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt)) = it := Fin.ext rfl
      rw [hi, he]
      exact Sym2.eq_swap
  intro hclosed
  have hf : T.edge t ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet base.core) c :=
    Finset.mem_filter.mpr ⟨hboundary, (fixedT t).trans hcolT⟩
  rw [hclosed c (Finset.mem_sdiff.mpr ⟨hcSigma, hreserved⟩)] at hf
  exact Finset.notMem_empty _ hf

private theorem helper_coreStrict_772.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (2 : ℕ) ≤ T.length - A.length →
    (∀ {S U : TreeSequence G e0},
        TreeSequenceInitialSegment S U → S.length = U.length → S = U) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    base.core.length <
      (H.stage (⟨(1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))).length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A htwo equalTrees lastZero
  by_cases hz : H.dividerCount = 0
  · have he : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
        Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
    rw [he, H.terminalStage]
    change 2 ≤ T.length - A.length at htwo
    rw [lastZero hz] at htwo
    omega
  · by_contra hnot
    have hlen : base.core.length = (H.stage ⟨1, by omega⟩).length := by
      have := H.coreInsideFirst.1
      omega
    have he := equalTrees H.coreInsideFirst hlen
    let i : Fin H.dividerCount := ⟨0, by omega⟩
    obtain ⟨eta, ⟨heta, hgamma, _⟩, _⟩ := C.good.uniqueRefresh i
    have hstage : H.stage i.succ.castSucc = base.core := by
      exact he.symm
    have hstar : HierarchyStarredStage H i.castSucc = base.core := rfl
    rw [hstage, hstar, Finset.sdiff_self, Finset.biUnion_empty] at hgamma
    have hempty : C.good.gamma i.succ eta = ∅ := Finset.subset_empty.mp hgamma
    have hcard := C.good.twoColors i.succ eta heta
    rw [hempty, Finset.card_empty] at hcard
    omega

private theorem helper_sigmaRoute_1064.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (sigma : PartialEdgeColoring E k),
    (∀
        v ∈
          TreeSequenceVertexSet
            (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ))),
        MissingColors G sigma v = MissingColors G phi v) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let B : TreeSequence G e0 :=
      HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
    (if ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE then
        CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          base.closure (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi
          sigma
      else
        StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma) →
    TreeSequenceInitialSegment B T →
    T.length = B.length + (1 : ℕ) →
    (∀ (t : Fin T.length), sigma (T.edge t) = phi (T.edge t)) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn T ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = { f } ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C sigma hpenultimateMissing n Tn Dn B hbase BToT
      hBlen fixedT
  rcases P2813_T1_TerminalRoute G k e0 input T phi ett with
    ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
  · exact Or.inl ⟨hp, TashkinovAugmentationSequenceColoringTransport phi sigma
      Tn B T hseq BToT hBlen (fun t _ => fixedT t) hpenultimateMissing⟩
  · obtain ⟨c, hc, hcol⟩ := hcontrol
    exact Or.inr ⟨hp, f, seed, hedges, hseed,
      TashkinovAugmentationSequenceColoringTransport phi sigma seed B T
        hseq BToT hBlen (fun t _ => fixedT t) hpenultimateMissing⟩

private theorem helper_continuation_1123.{u_1, u_2} :
    helperContinuation1123Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha beta hne z sigma hsigma
      hpenultimateMissing hstoredFirst H q A n Tn Dn B htwo hbase sigmaProper sigmaOne outside
      hmod prefixPresentation fixedA missingA htailEdges segTrans commonPrefix equalTrees
      stageSegment stageToT lastZero lastPositive coreToA TnToCore TnToA AToT
  have ordinaryToA (index : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage index.castSucc) A := by
    exact H.stageInitialSegmentOfStarredStage index (Fin.last H.dividerCount) (Fin.le_last _)
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    exact H.starredStageInitialSegmentOfLE j (Fin.last H.dividerCount) (Fin.le_last _)
  have BToT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hBlen : T.length = B.length + 1 := by
    change 2 ≤ T.length - A.length at htwo
    change T.length = min (A.length + ((T.length - A.length) - 1)) T.length + 1
    have := AToT.1
    omega
  have fixedT (t : Fin T.length) : sigma (T.edge t) = phi (T.edge t) := by
    by_cases ht : t.val < A.length
    · let ta : Fin A.length := ⟨t.val, ht⟩
      have he : Fin.castLE AToT.1 ta = t := Fin.ext rfl
      rw [← he, AToT.2.2 ta]
      exact fixedA ta
    · exact htailEdges t (by omega)
  have weak : HierarchyWeaklyStable H q sigma := by
    have allWeak (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma := by
      refine Fin.cases hbase (fun i => ⟨hbase, ?_⟩) j
      refine ⟨?_, ?_⟩
      · intro t _
        rw [← (ordinaryToA i.succ).2.2 t]
        exact fixedA _
      · intro v hv
        exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA i.succ) hv)
    exact allWeak q
  have treeMissingEq (S : TreeSequence G e0) (hSA : TreeSequenceInitialSegment S A) :
      TreeMissingColors sigma S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv =>
      missingA v (TreeSequenceInitialSegmentVertexSetSubset hSA hv))
  have combined (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      CombinedStableColoring Tn base.closure Dn phi sigma := by
    change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma else
        StableColoring Tn Dn phi sigma) at hbase
    simpa only [hp, ite_true] using hbase
  have sigmaRoute := @helper_sigmaRoute_1064 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C sigma hpenultimateMissing hbase BToT hBlen fixedT
  have corrData (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) :=
    corr.terminalData
  have fullBase := base.fullTransport C.maximum ctx.lowerRung H ctx.proper
      ctx.oneEdgeUncolored sigma sigmaProper sigmaOne hmod combined sigmaRoute
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
    refine Fin.cases ?_ (fun i => ?_) j
    · change TreeMissingColors sigma
        (corrT.replacementETT.series.data.tree
          (Fin.last corrT.replacementETT.rounds).castSucc) = TreeMissingColors phi Tn
      rw [terminalData.1]
      exact treeMissingEq Tn TnToA
    · exact treeMissingEq _ (ordinaryToA i.succ)
  have segmentEq := @helper_segmentEq_489 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C sigma hstoredFirst fixedA missingA stageToT AToT
      ordinaryToA fixedT corrT baseT hcoreT terminalData starredEq
  -- The first refresh prevents the core from being the whole first stage.
  have coreStrict := @helper_coreStrict_772 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C htwo equalTrees lastZero
  have parallelNotClosed := @helper_parallelNotClosed_549 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett base C sigma segTrans commonPrefix
      equalTrees stageToT coreToA TnToCore AToT fixedT treeMissingEq coreStrict
  let goodT : GoodHierarchy K := C.good.transportOfFields K rfl storedEq stageMissingEq
    (fun index color member => (segmentEq index color member).subset)
    (fun index => H.segmentMissingColors_eq_of_agreement K index index rfl
      (starredEq index.castSucc)
      (fun vertex member => missingA vertex
        (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA index.succ)
          (Finset.mem_sdiff.mp member).1)))
    (by
      intro parallel
      have oldParallel : ett.series.data.kind n = some TashkinovExtensionKind.PE :=
        terminalData.2.1.symm.trans parallel
      constructor
      · change ¬ TreeColorSetMinusClosed G sigma baseT.core
          ((HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0))
        rw [hcoreT, storedEq 0]
        exact parallelNotClosed oldParallel
      · change 4 ≤ ((TreeMissingColors sigma
          (corrT.replacementETT.series.data.tree
            (Fin.last corrT.replacementETT.rounds).castSucc) ∩
          TreeMissingColors sigma baseT.closure) \
            (HierarchyStoredColorsAt K 0).biUnion (C.good.gamma 0)).card
        have closureMissing : TreeMissingColors sigma base.closure =
            TreeMissingColors phi base.closure := by
          unfold TreeMissingColors
          exact Finset.biUnion_congr rfl (combined oldParallel).2.2
        rw [terminalData.1, hclosureT, storedEq 0, treeMissingEq Tn TnToA, closureMissing]
        exact (C.good.parallelBase oldParallel).2)
    (by
      intro index
      change TreeColorSetMinusClosed G sigma (H.stage index.succ.castSucc)
        ((HierarchyStoredColorsAt K index.succ).biUnion (C.good.gamma index.castSucc))
      rw [storedEq index.succ]
      apply P2813_T1_MinusClosedTransport G k e0 _ phi sigma alpha beta hne z hsigma
        ctx.proper ctx.oneEdgeUncolored _ (C.good.minusClosed index)
      · intro vertex member
        exact missingA vertex
          (TreeSequenceInitialSegmentVertexSetSubset (ordinaryToA index.succ) member)
      · exact outside index.succ)
  have same : SameGoodHierarchy C.good goodT := by
    refine ⟨?_, rfl, ?_⟩
    · refine ⟨hcoreT.symm, rfl, HEq.rfl, HEq.rfl, ?_, fun _ => hclosureT.symm⟩
      exact ⟨fun hp => terminalData.2.1.trans hp, fun hp => terminalData.2.1.symm.trans hp⟩
    · intro j
      exact ⟨(storedEq j).symm, fun _ _ => rfl⟩
  have prefixMaximum : A = Tn ∨
      ∃ inputA : PartialEdgeColoring E k,
        ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma, MaximumProperty ettA := by
    rcases prefixPresentation with he | ⟨corrA, hMPA⟩
    · exact Or.inl he
    · exact Or.inr ⟨corrA.replacementInput, corrA.replacementETT, hMPA⟩
  refine ⟨weak, hmod, prefixMaximum, ?_, corrT, hmaximumT, baseT, K, goodT, same⟩
  intro hq
  have positive : 0 < H.dividerCount := hq
  have last : A = H.stage q.castSucc := lastPositive (by omega)
  obtain ⟨ettA, baseA, KA, goodA, maximumA, count, core, closure, stages, colors, minus⟩ :=
    GoodHierarchyLastPrefixRepackage G k e0 corrT.replacementInput T sigma sigma
      corrT.replacementETT hmaximumT baseT K goodT positive A last
  have gammaAgreement : goodT.gamma = C.good.gamma := rfl
  refine ⟨corrT.replacementInput, ettA, baseA, KA, goodA, maximumA, count,
    core.trans hcoreT, closure.trans hclosureT, stages, ?_, ?_⟩
  · intro index
    refine ⟨(colors index).1.trans (storedEq _), ?_⟩
    intro color member
    rw [← gammaAgreement]
    exact (colors index).2 color
  · rw [gammaAgreement, storedEq] at minus
    exact minus
theorem StableChangeCasesOneTwoFullTail {V E : Type*}
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
    (htailEdges :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      ∀ t : Fin T.length, A.length ≤ t.val →
        sigma (T.edge t) = phi (T.edge t))
    (hpenultimateMissing :
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
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dnq := HierarchyStoredColorsAt H q
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
        (A = Tn ∨
            ∃ inputA : PartialEdgeColoring E k,
              ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma, MaximumProperty ettA) ∧
          (∀ hq : 0 < H.dividerCount,
              ∃ inputA : PartialEdgeColoring E k,
                ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
                  ∃ baseA : HierarchyBase ettA sigma,
                    ∃ K : TashkinovHierarchy ettA baseA,
                      ∃ goodA : GoodHierarchy K,
                        MaximumProperty ettA ∧
                          ∃ hcount : K.dividerCount + 1 = H.dividerCount,
                            baseA.core = base.core ∧
                              baseA.closure = base.closure ∧
                                (∀ j : Fin (K.dividerCount + 2),
                                    K.stage j = H.stage ⟨j.val, by omega⟩) ∧
                                  (∀ j : Fin (K.dividerCount + 1),
                                      let jH : Fin (H.dividerCount + 1) := ⟨j.val, by omega⟩
                                      HierarchyStoredColorsAt K j =
                                          HierarchyStoredColorsAt H jH ∧
                                        ∀ eta ∈ HierarchyStoredColorsAt K j,
                                          goodA.gamma j eta = C.good.gamma jH eta) ∧
                                    TreeColorSetMinusClosed G sigma Tnq
                                      (Dnq.biUnion
                                        (C.good.gamma
                                          ⟨C.hierarchy.dividerCount - 1, by omega⟩))) ∧
            (∃ corrT : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
              MaximumProperty corrT.replacementETT ∧
                ∃ baseT : HierarchyBase corrT.replacementETT sigma,
                  ∃ K : TashkinovHierarchy corrT.replacementETT baseT,
                    ∃ goodT : GoodHierarchy K, SameGoodHierarchy C.good goodT) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi
    ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality ctx.largeMissingSet
  have htwo : 2 ≤ T.length - A.length :=
    HierarchyCounterexampleTailAtLeastTwo G k e0 input T phi
    ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality ctx.largeMissingSet
  obtain ⟨hbase, missingA, sigmaProper, sigmaOne, outside⟩ :=
    P2813_T1_BaseControl G k e0 input T phi ett base C ctx helem
      alpha beta hne hmissingPrefix z hpath sigma hsigma hcase hdisjoint
  have preStepElementary := @SharedFacts.FullTailTransport.preStepElementary V E inferInstance
      inferInstance
      inferInstance inferInstance G k e0 input T phi ett base C ctx
  have fixedA := P2813_T1_DisplayedEdges G k e0 input T phi ett base H C.good
    ctx.proper ctx.oneEdgeUncolored preStepElementary helem alpha beta z sigma hsigma
    sigmaOne hbase outside
  obtain ⟨hmod, prefixPresentation⟩ := P2813_T1_PrefixReconstruction
    G k e0 input T phi ett base C ctx sigma sigmaProper sigmaOne hbase fixedA missingA
  change (∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t)) at fixedA
  change (∀ v ∈ TreeSequenceVertexSet A,
    MissingColors G sigma v = MissingColors G phi v) at missingA
  change (∀ t : Fin T.length, A.length ≤ t.val →
    sigma (T.edge t) = phi (T.edge t)) at htailEdges
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    exact hSU.trans hUW
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W) (hUW : TreeSequenceInitialSegment U W)
      (hlen : S.length ≤ U.length) : TreeSequenceInitialSegment S U := by
    exact hUW.of_common_extension hSW hlen
  have equalTrees := @SharedFacts.StableChangeCasesOneTwoSplitTail.equalTrees V E G e0
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    exact H.stageInitialSegmentOfLE _ _ (by change a ≤ a + d; exact Nat.le_add_right _ _)
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    exact H.stageInitialSegment j
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    have hq : q = 0 := Fin.ext (by simpa [q] using hz)
    simp only [A, hq, HierarchyStarredStage]
    rfl
  have lastPositive (hz : H.dividerCount ≠ 0) : A = H.stage q.castSucc := by
    have hq : q ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp only [q, Fin.val_last, Fin.val_zero] at this
      exact hz this
    dsimp only [A]
    rw [← Fin.succ_pred q hq]
    rfl
  have coreToA : TreeSequenceInitialSegment base.core A := by
    exact H.coreInitialSegmentOfStarredStage (Fin.last H.dividerCount)
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    exact base.lastRoundInitialSegmentCore
  have TnToA := segTrans TnToCore coreToA
  have AToT : TreeSequenceInitialSegment A T := by
    exact H.lastStarredInitialSegment
  exact @helper_continuation_1123 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx alpha beta hne z sigma hsigma hpenultimateMissing
      hstoredFirst htwo hbase sigmaProper sigmaOne outside hmod prefixPresentation fixedA
      missingA htailEdges segTrans commonPrefix equalTrees stageSegment stageToT lastZero
      lastPositive coreToA TnToCore TnToA AToT
end GoldbergSeymour

end
