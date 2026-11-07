/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData

public import LeanPool.GoldbergSeymour.HierarchySituationTwoReorderedTreesCertified.Preparation1
public import LeanPool.GoldbergSeymour.Td

/-!
# HierarchySituationTwoReorderedTreesCertified: supporting constructions, part 2

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.HierarchySituationTwoReorderedTreesCertifiedPreparation

/-- Dependent contract shared by the hierarchy construction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation1782Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (D :
        HierarchySituationTwoTailData G k e0 input T phi ett base C ctx),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
    let P : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (segmentTrans :
    ∀ {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z
        → TreeSequenceInitialSegment X Z) (prefixEq :
    ∀ {X Y : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y), X = TreeSequencePrefix Y
        X.length X.positive (
    by
         first
         | omega
         | (
           have := GoldbergSeymour.TreeSequence.positive X
           have := GoldbergSeymour.TreeSequence.positive Y
           have := hXY.1
           have := GoldbergSeymour.TreeSequence.positive X
           have := GoldbergSeymour.TreeSequence.positive Y
           all_goals omega)
    )) (stageSegment :
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) (hAstage : (0 : ℕ) < H.dividerCount → A = H.stage
        (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (hcoreA : TreeSequenceInitialSegment base.core A) (hBlen
        : B.length = T.length - (2 : ℕ)) (hm : (3 : ℕ) ≤ T.length) (hAB :
        TreeSequenceInitialSegment A B) (hTnB : TreeSequenceInitialSegment Tn B),
    let r : Fin T.length := (⟨T.length - (2 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let f : E := T.edge r;
    let g : E := T.edge D.lastEdgeIndex;
    let y : V := T.vertex D.penultimateVertexIndex;
    let z : V := T.vertex D.terminalVertexIndex;
    ∀ (hr : (↑r : ℕ) + (2 : ℕ) = T.length) (hOrigP : TreeSequenceAdjoinEdge B f P) (hOrigT :
        TreeSequenceAdjoinEdge P g T) (adjoinSets :
    ∀ {X U : TreeSequence G e0} {e : E}, TreeSequenceAdjoinEdge X e U → TreeSequenceVertexSet U =
        (insert (U.vertex (Fin.last U.length)) (TreeSequenceVertexSet X) : Finset V) ∧
        TreeSequenceEdgeSet U = (insert e (TreeSequenceEdgeSet X) : Finset E)) (hyB : y ∉
        TreeSequenceVertexSet B) (hyz : y ≠ z) (ig : Fin ((↑D.lastEdgeIndex : ℕ) + (1 : ℕ))) (M :
        TreeSequence G e0) (hBM : TreeSequenceAdjoinEdge B g M) (hMz : M.vertex (Fin.last
        M.length) = z) (hMV : TreeSequenceVertexSet M = (insert z (TreeSequenceVertexSet B) :
        Finset V)) (hME : TreeSequenceEdgeSet M = (insert g (TreeSequenceEdgeSet B) : Finset E))
        (if_ : Fin ((↑r : ℕ) + (1 : ℕ))) (S : TreeSequence G e0) (hMS : TreeSequenceAdjoinEdge M f
        S) (hSy : S.vertex (Fin.last S.length) = y) (hTV : TreeSequenceVertexSet T = (insert z
        (insert y (TreeSequenceVertexSet B) : Finset V) : Finset V)) (hTE : TreeSequenceEdgeSet T
        = (insert g (insert f (TreeSequenceEdgeSet B) : Finset E) : Finset E)) (hfB : f ∉
        TreeSequenceEdgeSet B) (hfg : f ≠ g),
    let R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx D := helperR1556
        G k e0 input T phi ett base C ctx D hm hr hOrigP hOrigT adjoinSets hyB hyz M hBM hMz hMV
        hME S hMS hSy hTV hTE hfB hfg;
    ∀ (hboundaryPE : B = Tn → ett.series.data.kind n = some TashkinovExtensionKind.PE) (routes :
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn M ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        n = some TashkinovExtensionKind.RE) ∧
    ∃ (e : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ e } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn e seed ∧ TashkinovAugmentationSequence phi seed M) ∧
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn S ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        n = some TashkinovExtensionKind.RE) ∧
    ∃ (e : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ e } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn e seed ∧ TashkinovAugmentationSequence phi seed S)),
    ∃ (R : HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx D),
    have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    have B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
        (B = Tn → ett.series.data.kind n = some TashkinovExtensionKind.PE) ∧ (ett.series.data.kind
        n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence phi Tn R.minus ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed R.minus) ∧
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        phi Tn R.star ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed R.star) ∧
    ∃ (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus), MaximumProperty
        corrMinus.replacementETT ∧
    ∃ (baseMinus : HierarchyBase corrMinus.replacementETT phi), baseMinus.core = base.core ∧
        baseMinus.closure = base.closure ∧ (↑baseMinus.supportPosition : ℕ) =
        (↑base.supportPosition : ℕ) ∧
    ∃ (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus) (hMinusCount :
        HMinus.dividerCount = C.hierarchy.dividerCount), (
    ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))), HMinus.stage j.castSucc = C.hierarchy.stage
        (Fin.cast (
    by omega
    ) j).castSucc) ∧ (
    ∀ (j : Fin HMinus.dividerCount), (↑(HMinus.dividerPosition j) : ℕ) =
        (↑(C.hierarchy.dividerPosition (Fin.cast hMinusCount j)) : ℕ)) ∧
    ∃ (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star), MaximumProperty
        corrStar.replacementETT ∧
    ∃ (baseStar : HierarchyBase corrStar.replacementETT phi), baseStar.core = base.core ∧
        baseStar.closure = base.closure ∧ (↑baseStar.supportPosition : ℕ) = (↑base.supportPosition
        : ℕ) ∧
    ∃ (HStar : TashkinovHierarchy corrStar.replacementETT baseStar) (hStarCount :
        HStar.dividerCount = C.hierarchy.dividerCount), (
    ∀ (j : Fin (HStar.dividerCount + (1 : ℕ))), HStar.stage j.castSucc = C.hierarchy.stage
        (Fin.cast (
    by omega
    ) j).castSucc) ∧
    ∀ (j : Fin HStar.dividerCount), (↑(HStar.dividerPosition j) : ℕ) =
        (↑(C.hierarchy.dividerPosition (Fin.cast hStarCount j)) : ℕ)

theorem helper_continuation_1782.{u_1, u_2} :
    helperContinuation1782Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H A ell B P n Tn segmentTrans prefixEq
      stageSegment hAstage hcoreA hBlen hm hAB hTnB r f g y z hr hOrigP hOrigT adjoinSets hyB hyz
      ig M hBM hMz hMV hME if_ S hMS hSy hTV hTE hfB hfg R hboundaryPE routes
  have hmod : ModColoring ett phi := by
    apply Td G k e0 input T phi ett C.maximum C.positive ctx.lowerRung phi
      ctx.proper ctx.oneEdgeUncolored
    rw [← ett.generatingColoring]
    exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  have hNM : TreeSequenceInitialSegment Tn M :=
    segmentTrans hTnB hBM.choose_spec.1
  have hNS : TreeSequenceInitialSegment Tn S :=
    segmentTrans hNM hMS.choose_spec.1
  have hMlen : M.length = B.length + 1 := hBM.choose
  have hSlen : S.length = M.length + 1 := hMS.choose
  obtain ⟨corrM⟩ := hmod.2.2 M hNM
    (by change Tn.length < M.length; have := hTnB.1; omega) routes.1
  obtain ⟨corrS⟩ := hmod.2.2 S hNS
    (by change Tn.length < S.length; have := hTnB.1; omega) routes.2
  have hMPM := MaximumPropertyTransport G k e0 ett phi hmod M corrM C.maximum
  have hMPS := MaximumPropertyTransport G k e0 ett phi hmod S corrS C.maximum
  have hlastB : TreeSequenceInitialSegment
      (H.stage (Fin.last H.dividerCount).castSucc) B := by
    exact helper_hlastB_1310 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hAstage) (@hm)
        (@hAB) (@hTnB) (@ig) (@M) (@if_) (@S)
  have hstageB (i : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage i.castSucc) B := by
    exact @helper_hstageB_1323 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@segmentTrans)
        (@stageSegment) (@hm) (@ig) (@M) (@if_) (@S) (@hlastB) (@i)
  have terminalTree (X : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X) :
      corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
    exact corr.terminalData.1
  have copyHierarchy (X : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X)
      (hBX : TreeSequenceInitialSegment B X) (hstrictBX : B.length < X.length) :
      ∃ bx : HierarchyBase corr.replacementETT phi,
        bx.core = base.core ∧ bx.closure = base.closure ∧
        bx.supportPosition.val = base.supportPosition.val ∧
        ∃ K : TashkinovHierarchy corr.replacementETT bx,
          ∃ hcount : K.dividerCount = H.dividerCount,
            (∀ j : Fin (K.dividerCount + 1),
              K.stage j.castSucc = H.stage
                (Fin.cast (congrArg (fun d => d + 1) hcount) j).castSucc) ∧
            ∀ j : Fin K.dividerCount,
              (K.dividerPosition j).val =
                (H.dividerPosition (Fin.cast hcount j)).val := by
    exact @helper_copyHierarchy_812 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett base C ctx D segmentTrans prefixEq hcoreA hBlen hm hAB ig M if_ S
        hMlen hSlen hlastB hstageB terminalTree X corr hBX hstrictBX
  obtain ⟨baseM, hcoreM, hclosureM, hsupportM, HM, hcountM, hstageM, hpositionM⟩ :=
    copyHierarchy M corrM hBM.choose_spec.1 (by omega)
  obtain ⟨baseS, hcoreS, hclosureS, hsupportS, HS, hcountS, hstageS, hpositionS⟩ :=
    copyHierarchy S corrS (segmentTrans hBM.choose_spec.1 hMS.choose_spec.1) (by omega)
  exact ⟨R, hboundaryPE, routes.1, routes.2, corrM, hMPM,
    baseM, hcoreM, hclosureM, hsupportM, HM, hcountM, hstageM, hpositionM,
    corrS, hMPS, baseS, hcoreS, hclosureS, hsupportS, HS, hcountS, hstageS, hpositionS⟩

theorem helper_continuation_941.{u_1, u_2} :
    helperContinuation941Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H A ell B P n Tn segmentTrans
      commonPrefix equalTrees prefixSegment prefixEq stageSegment stageToT hAstage hcoreA hBlen
      hPlen hm hBT hPT hBP hAB hTnB r f g y z hr hgpos hypos hzpos hOrigP hOrigT hPy hTz
      vertexMem adjoinSets adjoinVertex hzB hyB hyz ig hig higbound
  let igB : Fin (B.length + 1) := ⟨ig.val, higbound⟩
  have hgends : G.ends g = s(z, B.vertex igB) := by
    exact helper_hgends_1058 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hm) (@hBT) (@hr)
        (@hgpos) (@hypos) (@hzpos) (@ig) (@hig) (@higbound)
  have hgBoundary : g ∈ BoundaryEdges G (TreeSequenceVertexSet B) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨B.vertex igB, vertexMem _ _, z, hzB, ?_⟩
    exact hgends.trans (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨M, hBM⟩ := TreeSequenceBoundaryEdgeAppendExists B g hgBoundary
  -- The adjoin relation fixes the edge; the endpoint argument fixes its fresh vertex.
  have hMz : M.vertex (Fin.last M.length) = z :=
    adjoinVertex hBM hzB (vertexMem B igB) hgends
  have hMV : TreeSequenceVertexSet M = insert z (TreeSequenceVertexSet B) := by
    simpa [hMz] using (adjoinSets hBM).1
  have hME : TreeSequenceEdgeSet M = insert g (TreeSequenceEdgeSet B) :=
    (adjoinSets hBM).2
  have hyM : y ∉ TreeSequenceVertexSet M := by simpa [hMV, hyz] using hyB
  obtain ⟨if_, hif⟩ := T.attaches r
  have hifbound : if_.val < B.length + 1 := by have := if_.isLt; omega
  let ifB : Fin (B.length + 1) := ⟨if_.val, hifbound⟩
  have hfends : G.ends f = s(y, B.vertex ifB) := by
    exact helper_hfends_1083 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hm) (@hBT) (@hr)
        (@hgpos) (@hypos) (@ig) (@if_) (@hif) (@hifbound)
  have hfBoundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet M) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨B.vertex ifB, ?_, y, hyM, ?_⟩
    · rw [hMV]; exact Finset.mem_insert_of_mem (vertexMem _ _)
    · exact hfends.trans (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨S, hMS⟩ := TreeSequenceBoundaryEdgeAppendExists M f hfBoundary
  have hSy : S.vertex (Fin.last S.length) = y := by
    apply adjoinVertex hMS hyM
    · rw [hMV]; exact Finset.mem_insert_of_mem (vertexMem B ifB)
    · exact hfends
  have hPV : TreeSequenceVertexSet P = insert y (TreeSequenceVertexSet B) := by
    simpa [hPy] using (adjoinSets hOrigP).1
  have hPE : TreeSequenceEdgeSet P = insert f (TreeSequenceEdgeSet B) :=
    (adjoinSets hOrigP).2
  have hTV : TreeSequenceVertexSet T = insert z (insert y (TreeSequenceVertexSet B)) := by
    simpa [hTz, hPV] using (adjoinSets hOrigT).1
  have hTE : TreeSequenceEdgeSet T = insert g (insert f (TreeSequenceEdgeSet B)) := by
    simpa [hPE] using (adjoinSets hOrigT).2
  have hfB : f ∉ TreeSequenceEdgeSet B := by
    exact helper_hfB_1110 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hm) (@hBT)
        (@hr) (@hgpos) (@hypos) (@hzpos) (@ig) (@if_)
  have hfg : f ≠ g := by
    intro hh
    have hi := congrArg Fin.val (T.edge_injective hh)
    omega
  let R : HierarchySituationTwoReorderedTrees
      G k e0 input T phi ett base C ctx D := by
    exact @helperR1556 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hm) (@hr) (@hOrigP)
        (@hOrigT) (@adjoinSets) (@hyB) (@hyz) (@M) (@hBM) (@hMz) (@hMV) (@hME) (@S) (@hMS) (@hSy)
        (@hTV) (@hTE) (@hfB) (@hfg)
  have stableClosed (X : TreeSequence G e0) (colors : Finset (Fin k))
      (old new : PartialEdgeColoring E k)
      (ho : IsProperEdgeColoring G old) (huo : IsOneEdgeUncolored old e0)
      (hn : IsProperEdgeColoring G new) (hun : IsOneEdgeUncolored new e0)
      (hstable : StableColoring X colors old new)
      (hclosed : ColoredVertexSetClosed G old (TreeSequenceVertexSet X)) :
      ColoredVertexSetClosed G new (TreeSequenceVertexSet X) := by
    exact helper_stableClosed_938 G k e0 X colors old new ho huo
        hn hun hstable hclosed
  have stepRoute (j : Fin (ett.rounds + 1)) (hj : j ≠ 0) :
      (ett.series.data.kind j = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence (ett.series.data.coloring j)
          (ett.series.data.tree j.castSucc) (ett.series.data.tree j.succ)) ∨
      ((ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind j = some TashkinovExtensionKind.RE) ∧
        ColoredVertexSetClosed G (ett.series.data.coloring j)
          (TreeSequenceVertexSet (ett.series.data.tree j.castSucc)) ∧
        ∃ (e : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges j = {e} ∧
          TreeSequenceAdjoinEdge (ett.series.data.tree j.castSucc) e seed ∧
          TashkinovAugmentationSequence (ett.series.data.coloring j)
            seed (ett.series.data.tree j.succ)) := by
    exact helper_stepRoute_542 G k e0 input T phi ett stableClosed j hj
  let Z := ett.series.data.tree n.succ
  have hTZ : TreeSequenceInitialSegment T Z := by
    convert ett.belowFinal using 1
    apply congrArg ett.series.data.tree
    apply Fin.ext
    rfl
  have hnzero : n ≠ 0 := by
    exact helper_hnzero_1202 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hm) (@ig) (@if_)
  have terminalRoute := stepRoute n hnzero
  rw [← ett.generatingColoring] at terminalRoute
  change (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence phi Tn Z) ∨
    ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) ∧
      ∃ (e : E) (seed : TreeSequence G e0),
        ett.series.data.connectingEdges n = {e} ∧
          TreeSequenceAdjoinEdge Tn e seed ∧
          TashkinovAugmentationSequence phi seed Z) at terminalRoute
  have seedToT (e : E) (seed : TreeSequence G e0)
      (hkind : ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE)
      (he : ett.series.data.connectingEdges n = {e})
      (ha : TreeSequenceAdjoinEdge Tn e seed) :
      TreeSequenceInitialSegment seed T := by
    exact @helper_seedToT_936 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx D segmentTrans commonPrefix prefixSegment stageToT hm hBT hTnB
        hr hgpos hypos hzpos ig if_ e seed hkind he ha
  have oneStep {X Y : TreeSequence G e0}
      (hseq : TashkinovAugmentationSequence phi X Y)
      (hlen : Y.length = X.length + 1) : TashkinovAugmentation phi X Y := by
    exact @helper_oneStep_1228 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@equalTrees) (@hm)
        (@ig) (@if_) (@X) (@Y) (@hseq) (@hlen)
  have hfinalAug : TashkinovAugmentation phi P T := by
    exact @helper_hfinalAug_1019 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx D segmentTrans commonPrefix hBlen hPlen hm hBT hPT hBP hTnB
        hr hgpos hypos hzpos ig if_ hTZ hnzero terminalRoute seedToT oneStep
  have hthetaP : D.theta ∈ TreeMissingColors phi P := by
    exact helper_hthetaP_1244 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@hOrigT) (@hfinalAug)
  have hthetaB : D.theta ∈ TreeMissingColors phi B := by
    exact helper_hthetaB_1250 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D) (@hPV) (@hthetaP)
  -- A nonparallel terminal seed cannot begin exactly at B: its old tree is closed.
  have hboundaryPE : B = Tn → ett.series.data.kind n = some TashkinovExtensionKind.PE := by
    exact helper_hboundaryPE_1258 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
        (@D)
        (@hgBoundary) (@terminalRoute) (@hthetaB)
  have augmentOfAdjoin {X U : TreeSequence G e0} {e : E} {c : Fin k}
      (ha : TreeSequenceAdjoinEdge X e U) (he : phi e = some c)
      (hc : c ∈ TreeMissingColors phi X) : TashkinovAugmentation phi X U := by
    rcases ha with ⟨hl, hs, hedge⟩
    exact ⟨hl, hs, c, hedge ▸ he, hc⟩
  have hBMaug : TashkinovAugmentation phi B M :=
    augmentOfAdjoin hBM D.thetaOnLastEdge hthetaB
  have routes :
      ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn M) ∨
        ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (e : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = {e} ∧
              TreeSequenceAdjoinEdge Tn e seed ∧
              TashkinovAugmentationSequence phi seed M)) ∧
      ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn S) ∨
        ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (e : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = {e} ∧
              TreeSequenceAdjoinEdge Tn e seed ∧
              TashkinovAugmentationSequence phi seed S)) := by
    exact @helper_routes_692 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett base C ctx D segmentTrans commonPrefix equalTrees hBlen hPlen hm hBT hPT
        hBP hTnB hr hgpos hypos hzpos hOrigP ig M hBM if_ S hMS hPE hTZ hnzero terminalRoute
        seedToT oneStep hboundaryPE augmentOfAdjoin hBMaug
  exact @helper_continuation_1782 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
      (@segmentTrans) (@prefixEq) (@stageSegment) (@hAstage) (@hcoreA) (@hBlen) (@hm) (@hAB)
      (@hTnB) (@hr) (@hOrigP) (@hOrigT) (@adjoinSets) (@hyB) (@hyz) (@ig) (@M) (@hBM) (@hMz)
      (@hMV) (@hME) (@if_) (@S) (@hMS) (@hSy) (@hTV) (@hTE) (@hfB) (@hfg) (@hboundaryPE) (@routes)
theorem helper_continuation_891.{u_1, u_2} :
    helperContinuation891Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H A ell B P n Tn segmentRefl segmentTrans
      commonPrefix equalTrees prefixSegment prefixEq stageSegment stageToT hAstage hAT hcoreA
      hell htwo hAlen hBlen hPlen hm hBT
  have hPT : TreeSequenceInitialSegment P T := prefixSegment _ _ _ _
  have hBP : TreeSequenceInitialSegment B P := commonPrefix hBT hPT (by omega)
  have hAB : TreeSequenceInitialSegment A B := commonPrefix hAT hBT (by omega)
  have hTnB : TreeSequenceInitialSegment Tn B := by
    exact base.lastRoundInitialSegmentCore.trans (hcoreA.trans hAB)
  let r : Fin T.length := ⟨T.length - 2, by omega⟩
  let f := T.edge r
  let g := T.edge D.lastEdgeIndex
  let y := T.vertex D.penultimateVertexIndex
  let z := T.vertex D.terminalVertexIndex
  have hr : r.val + 2 = T.length := by dsimp [r]; omega
  have hgpos := D.lastEdgePosition
  have hypos := D.penultimateVertexPosition
  have hzpos := D.terminalVertexPosition
  have hOrigP : TreeSequenceAdjoinEdge B f P := by
    refine ⟨by omega, hBP, ?_⟩
    change T.edge _ = T.edge r
    congr 1
    apply Fin.ext
    change B.length = r.val
    omega
  have hOrigT : TreeSequenceAdjoinEdge P g T := by
    refine ⟨by omega, hPT, ?_⟩
    apply congrArg T.edge
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_last]
    omega
  have hPy : P.vertex (Fin.last P.length) = y := by
    change T.vertex _ = T.vertex D.penultimateVertexIndex
    congr 1
    apply Fin.ext
    change P.length = D.penultimateVertexIndex.val
    omega
  have hTz : T.vertex (Fin.last T.length) = z := by
    apply congrArg T.vertex
    apply Fin.ext
    exact hzpos.symm
  have vertexMem (X : TreeSequence G e0) (i : Fin (X.length + 1)) :
      X.vertex i ∈ TreeSequenceVertexSet X := by simp [TreeSequenceVertexSet]
  have freshLast {X U : TreeSequence G e0} {e : E}
      (ha : TreeSequenceAdjoinEdge X e U) :
      U.vertex (Fin.last U.length) ∉ TreeSequenceVertexSet X := by
    rcases ha with ⟨hl, hs, he⟩
    intro hv
    obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hv
    have hh := U.vertex_injective ((hs.2.1 i).trans hi)
    have hhval := congrArg Fin.val hh
    simp only [Fin.val_castLE, Fin.val_last] at hhval
    omega
  have adjoinSets {X U : TreeSequence G e0} {e : E}
      (ha : TreeSequenceAdjoinEdge X e U) :
      TreeSequenceVertexSet U = insert (U.vertex (Fin.last U.length))
          (TreeSequenceVertexSet X) ∧
        TreeSequenceEdgeSet U = insert e (TreeSequenceEdgeSet X) := by
    exact @helper_adjoinSets_322 V E inferInstance inferInstance inferInstance inferInstance G k
        e0 input T phi ett base C ctx D hm X U e ha
  have adjoinVertex {X U : TreeSequence G e0} {e : E} {v w : V}
      (ha : TreeSequenceAdjoinEdge X e U)
      (hv : v ∉ TreeSequenceVertexSet X) (hw : w ∈ TreeSequenceVertexSet X)
      (hends : G.ends e = s(v, w)) : U.vertex (Fin.last U.length) = v := by
    rcases ha with ⟨hl, hs, he⟩
    obtain ⟨i, hi⟩ := U.attaches (Fin.cast hl.symm (Fin.last X.length))
    have hil : i.val < X.length + 1 := by simpa using i.isLt
    let ix : Fin (X.length + 1) := ⟨i.val, hil⟩
    have hvold : U.vertex (Fin.castLT i (by omega)) = X.vertex ix := hs.2.1 ix
    have hnew : (Fin.cast hl.symm (Fin.last X.length)).succ =
        Fin.last U.length := by apply Fin.ext; simp; omega
    rw [he, hnew, hvold] at hi
    rcases Sym2.eq_iff.mp (hi.symm.trans hends) with hh | hh
    · exact hh.1
    · exact False.elim (hv (hh.2 ▸ vertexMem X ix))
  have hzB : z ∉ TreeSequenceVertexSet B := by
    intro hz
    obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hz
    have hidx := T.vertex_injective ((hBT.2.1 i).trans hi)
    have hv := congrArg Fin.val hidx
    simp only [Fin.val_castLE] at hv
    omega
  have hyB : y ∉ TreeSequenceVertexSet B := by
    rw [← hPy]
    exact freshLast hOrigP
  have hyz : y ≠ z := by
    intro hh
    have hi := congrArg Fin.val (T.vertex_injective hh)
    omega
  obtain ⟨ig, hig⟩ := T.attaches D.lastEdgeIndex
  have higbound : ig.val < B.length + 1 := by
    have hine : ig.val ≠ D.penultimateVertexIndex.val := by
      intro hh
      apply D.lastEdgeNotIncidentPenultimate
      change T.vertex D.penultimateVertexIndex ∈ G.ends g
      rw [hig]
      apply Sym2.mem_iff.mpr
      right
      congr 1
      apply Fin.ext
      exact hh.symm
    omega
  exact @helper_continuation_941 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett base C ctx D segmentTrans commonPrefix equalTrees prefixSegment prefixEq
      stageSegment stageToT hAstage hcoreA hBlen hPlen hm hBT hPT hBP hAB hTnB hr hgpos hypos
      hzpos hOrigP hOrigT hPy hTz vertexMem adjoinSets adjoinVertex hzB hyB hyz ig hig higbound

end GoldbergSeymour.HierarchySituationTwoReorderedTreesCertifiedPreparation

end
