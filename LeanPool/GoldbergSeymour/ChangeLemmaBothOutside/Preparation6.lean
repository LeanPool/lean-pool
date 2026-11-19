/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TerminalRoute

public import LeanPool.GoldbergSeymour.HierarchyPathNumberPrefix
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLessFacts
public import LeanPool.GoldbergSeymour.ChangeLemmaBothOutside.Preparation1
public import LeanPool.GoldbergSeymour.GoodHierarchyTerminalPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyFieldTransport
public import LeanPool.GoldbergSeymour.SharedFacts.MixedChangeTransport.Preparation2

/-!
# ChangeLemmaBothOutside: supporting constructions, part 6

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.ChangeLemmaBothOutsidePreparation

theorem helper_continuation_4653.{u_1, u_2} :
    helperContinuation4653Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hminimal alpha beta hne H q
      A n Tn Dn ia ib vb ell yLength Y segRefl segTrans coreToA TnToA AToT ordinaryToA starredToA
      hElementaryY hb vertexY hbY hAia hAib halphaA hbetaA horder habIndex B BToT ABstrict
      BstrictT rpB aboveB strictB belowB genB hMPB baseB hcoreB HB hcountB hstagesB hdividersB
      goodB hgoodB ettB outsideStored hDn sigma behavior unaffected fixedValue sigmaProper
      sigmaOne missingBefore sigmaNotElementary missingA treeMissingEq stable stableTn TnToB
      TnStrictB notControlled terminalRoute
  have treeControlled (t : Fin Tn.length) :
      phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta := by
    exact @helper_treeControlled_1302 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hone) (@alpha)
        (@beta) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB)
        (@notControlled) (@t)
  have augmentationControlled (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S B) (t : Fin B.length)
      (ht : S.length ≤ t.val) :
      phi (B.edge t) ≠ some alpha ∧ phi (B.edge t) ≠ some beta := by
    exact @helper_augmentationControlled_640 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@AToT) (@hElementaryY) (@hb) (@vertexY) (@hbY) (@hAib) (@halphaA) (@horder) (@BToT)
        (@BstrictT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB) (@S) (@hseq)
        (@t) (@ht)
  have allControlled (t : Fin B.length) :
      phi (B.edge t) ≠ some alpha ∧ phi (B.edge t) ≠ some beta := by
    exact @helper_allControlled_1331 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@HB) (@TnToB)
        (@terminalRoute) (@treeControlled) (@augmentationControlled) (@t)
  have edgesFixed (t : Fin B.length) : sigma (B.edge t) = phi (B.edge t) :=
    fixedValue _ (allControlled t).1 (allControlled t).2
  have routeTransport (S : TreeSequence G e0) (hs : TashkinovAugmentationSequence phi S B) :
      TashkinovAugmentationSequence sigma S B := by
    exact @SharedFacts.MixedChangeTransport.routeTransport (@V) (@E) inferInstance
      inferInstance inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett)
      (@base) (@C) (@alpha) (@beta) (@segTrans) (@hAib) (@BToT) (@missingBefore)
      (@edgesFixed) (@S) (@hs)
  have replacement :
      ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B,
        MaximumProperty corr.replacementETT ∧
        ∃ baseS : HierarchyBase corr.replacementETT sigma,
          ∃ HS : TashkinovHierarchy corr.replacementETT baseS,
            SameHierarchyStages HB HS := by
    exact @helper_replacement_742 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
        (@hlower) (@alpha) (@beta) (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB)
        (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@sigmaProper) (@sigmaOne) (@stable) (@stableTn)
        (@TnToB) (@TnStrictB) (@terminalRoute) (@routeTransport)
  obtain ⟨corr, hMPS, baseS, HS, hsame⟩ := replacement
  have storedS : TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) = Dn := by
    exact corr.terminalData.2.2
  have hrS : corr.replacementETT.rounds = ett.rounds := corr.rungAgreement
  have stageBToA (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HB.stage j.castSucc) A := by
    rw [(hstagesB j).1]
    exact ordinaryToA _
  have starBToA (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage HB j) A := by
    rw [(hstagesB j).2]
    exact starredToA _
  have stageBToB (j : Fin (HB.dividerCount + 2)) :
      TreeSequenceInitialSegment (HB.stage j) B := by
    exact HB.stageInitialSegment j
  have closureBToA (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
    exact @helper_closureBToA_1398 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@hcoreB) (@hp)
  have minusEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) (D : Finset (Fin k)) :
      TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D := by
    exact @helper_minusEq_1405 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@halphaA) (@hbetaA) (@unaffected) (@treeMissingEq) (@S) (@hS) (@D)
  -- Only stored colors require a transported first-missing cutoff.
  have firstEq (eta : Fin k) (he : eta ∈ Dn) :
      HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta := by
    exact @helper_firstEq_1458 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hAib) (@hDn) (@behavior) (@eta) (@he)
  have parallel (isParallel : ettB.series.data.kind (Fin.last ettB.rounds) =
      some TashkinovExtensionKind.PE) :
      ¬TreeColorSetMinusClosed G sigma baseB.core
          ((HierarchyStoredColorsAt HB 0).biUnion (goodB.gamma 0)) ∧
        4 ≤ ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma baseB.closure) \
          (HierarchyStoredColorsAt HB 0).biUnion (goodB.gamma 0)).card := by
    rw [treeMissingEq _ TnToA.vertexSet_subset, treeMissingEq _ (closureBToA isParallel),
      minusEq _ (by rw [hcoreB]; exact coreToA.vertexSet_subset)]
    exact goodB.parallelBase isParallel
  have minus (index : Fin HB.dividerCount) :
      TreeColorSetMinusClosed G sigma (HB.stage index.succ.castSucc)
        ((HierarchyStoredColorsAt HB index.succ).biUnion (goodB.gamma index.castSucc)) := by
    rw [minusEq _ (stageBToA index.succ).vertexSet_subset]
    exact goodB.minusClosed index
  let goodS : GoodHierarchy HS := goodB.transportOfColoringAgreement HS hsame storedS
    (fun index => treeMissingEq _ (stageBToA index).vertexSet_subset)
    (fun index => treeMissingEq _ (starBToA index).vertexSet_subset)
    (fun _ color member => congrArg Fin.val (firstEq color (Finset.mem_sdiff.mp member).1))
    (fun index position => by
      have initial := stageBToB index.succ
      have fixed := edgesFixed (Fin.castLE initial.1 position)
      rw [initial.2.2] at fixed
      exact fixed)
    (fun index vertex member => missingA vertex
      ((stageBToA index.succ).vertexSet_subset (Finset.mem_sdiff.mp member).1)) parallel minus
  let CS : HierarchyCounterexample baseS :=
    { positive := by rw [hrS]; exact C.positive
      hierarchy := HS
      good := goodS
      maximum := hMPS
      notElementary := sigmaNotElementary }
  have hstarLast : HierarchyStarredStage HS (Fin.last HS.dividerCount) = A := by
    exact hsame.lastStarredStage_eq.trans
      (H.lastStarredStage_eq_of_agreement HB hcountB (fun index => (hstagesB index).2))
  have hlastOrd : HS.stage (Fin.last HS.dividerCount).castSucc = H.stage q.castSucc := by
    have stage := (hstagesB (Fin.last HB.dividerCount)).1
    have index : Fin.cast (congrArg (fun count : ℕ => count + 1) hcountB)
        (Fin.last HB.dividerCount) = q := Fin.ext hcountB
    exact hsame.lastOrdinaryStage_eq.trans (by simpa only [index] using stage)
  -- Path candidates restrict to the shorter prefix; the second measure decreases strictly.
  have pathLe : HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
    exact H.pathNumber_le_of_prefix HS
      (congrArg (fun S : TreeSequence G e0 => S.length) hstarLast) BToT ABstrict
  have tailLess : B.length - (HS.stage (Fin.last HS.dividerCount).castSucc).length <
      T.length - (H.stage q.castSucc).length := by
    rw [hlastOrd]
    have hlen := (ordinaryToA q).1
    omega
  have hless : HierarchyCounterexampleLess (HierarchyCounterexampleMeasure CS)
      (HierarchyCounterexampleMeasure C) := by
    exact HierarchyCounterexampleLess.of_le_of_lt pathLe tailLess
  exact hminimal CS hrS (hsame.2.1.symm.trans hcountB) hless

theorem helper_finish_4308.{u_1, u_2} :
    helperFinish4308Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hminimal alpha beta hne
      hmissingPrefix horderedUnused hlocation H q A n Tn Dn ia ib va vb ell yLength Y segRefl
      segTrans commonPrefix coreToA TnToA AToT ordinaryToA starredToA hmissingY hElementaryY ha
      hb vertexY haY hbY hout hAia hAib halphaA hbetaA horder habIndex havb B BToT AToB ABstrict
      BToY BstrictT rpB aboveB strictB belowB genB hMPB hsB baseB hcoreB hclosureB hsupportB HB
      hcountB hstagesB hdividersB goodB hgoodB ettB missingSubset outsideStored hDn
  by_contra hcomponents
  let K := TwoColorComponent G phi alpha beta (Sum.inl vb)
  let sigma := TwoColorComponentSwap G phi alpha beta (Sum.inl vb)
  have hdisjoint : Disjoint (TwoColorComponent G phi alpha beta (Sum.inl va)) K :=
    (TwoColorComponentsDisjoint G phi alpha beta (Sum.inl va) (Sum.inl vb)).resolve_left
      hcomponents
  have haK : Sum.inl va ∉ K := by
    intro h
    exact Set.disjoint_left.mp hdisjoint (show Sum.inl va ∈
      TwoColorComponent G phi alpha beta (Sum.inl va) from rfl) h
  have behavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper
    (Sum.inl vb)
  have edgeOfVertex {v : V} {f : E} (hv : Sum.inl v ∈ K)
      (hf : Incident G v f) (hc : phi f = some alpha ∨ phi f = some beta) :
      Sum.inr f ∈ K := by
    have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr f) (Sum.inl v) :=
      ⟨hf, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  have unaffected (f : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      sigma f = some c ↔ phi f = some c := by
    exact @helper_unaffected_1187 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@ha) (@hb) (@f) (@c) (@hca) (@hcb)
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    simp [sigma, TwoColorComponentSwap, ha, hb]
  have sigmaProper : IsProperEdgeColoring G sigma :=
    TwoColorComponentSwapProper G phi alpha beta hne hproper _
  have sigmaOne : IsOneEdgeUncolored sigma e0 := by
    exact @helper_sigmaOne_1202 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hone) (@alpha)
        (@beta) (@hne) (@ha) (@hb) (@unaffected)
  have vertexB (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
      T.vertex i ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haB : va ∈ TreeSequenceVertexSet B := vertexB ia (le_of_lt habIndex)
  have hbB : vb ∈ TreeSequenceVertexSet B := vertexB ib le_rfl
  -- Elementarity fixes missing sets before the swapped endpoint, even inside its component.
  have missingBefore (v : V) (hv : v ∈ TreeSequenceVertexSet B) (hvb : v ≠ vb) :
      MissingColors G sigma v = MissingColors G phi v := by
    exact @SharedFacts.MixedChangeTransport.notMissingBeforeFirstPosition (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@hElementaryY) (@ha) (@hb) (@haY) (@hbY) (@hAib) (@BToY) (@haK) (@behavior)
        (@edgeOfVertex) (@v) (@hv) (@hvb)
  have hnewa : alpha ∈ MissingColors G sigma va := by
    rw [behavior.1 va haK]
    exact ha.1
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
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv => missingA v (hS hv))
  have stable (S : TreeSequence G e0) (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A)
      (D : Finset (Fin k)) (hD : alpha ∉ D ∧ beta ∉ D) :
      StableColoring S D phi sigma := by
    exact @helper_stable_1247 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@halphaA)
        (@hbetaA) (@unaffected) (@missingA) (@S) (@hS) (@D) (@hD)
  have stableTn : StableColoring Tn Dn phi sigma :=
    stable Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA) Dn hDn
  have TnToB := segTrans TnToA AToB
  have TnStrictB : Tn.length < B.length := lt_of_le_of_lt TnToA.1 ABstrict
  have notControlled (c : Fin k) (hc : c = alpha ∨ c = beta) :
      c ∉ TreeMissingColors phi Tn ∪ Dn := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases hc with rfl | rfl
      · exact halphaA (missingSubset TnToA hm)
      · exact hbetaA (missingSubset TnToA hm)
    · rcases hc with rfl | rfl
      · exact hDn.1 hm
      · exact hDn.2 hm
  -- Nonparallel extensions retain the certified connecting edge and one-edge seed.
  have terminalRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn B) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence phi seed B ∧
          phi f ≠ some alpha ∧ phi f ≠ some beta) := by
    let terminalTree : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds
        roundsPositive := rpB
        series := ett.series
        abovePenultimate := aboveB
        strictAbovePenultimate := strictB
        belowFinal := belowB
        generatingColoring := genB }
    exact terminalTree.terminalRouteAvoiding alpha beta notControlled
  exact @helper_continuation_4653 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@hminimal) (@alpha) (@beta) (@hne) (@segRefl) (@segTrans) (@coreToA) (@TnToA)
      (@AToT) (@ordinaryToA) (@starredToA) (@hElementaryY) (@hb) (@vertexY) (@hbY) (@hAia)
      (@hAib) (@halphaA) (@hbetaA) (@horder) (@habIndex) (@BToT) (@ABstrict) (@BstrictT) (@rpB)
      (@aboveB) (@strictB) (@belowB) (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@hcountB)
      (@hstagesB) (@hdividersB) (@goodB) (@hgoodB) (@outsideStored) (@hDn) (@behavior)
      (@unaffected) (@fixedValue) (@sigmaProper) (@sigmaOne) (@missingBefore)
      (@sigmaNotElementary) (@missingA) (@treeMissingEq) (@stable) (@stableTn) (@TnToB)
      (@TnStrictB) (@notControlled) (@terminalRoute)
theorem helper_continuation_4272.{u_1, u_2} :
    helperContinuation4272Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hminimal alpha beta hne
      hmissingPrefix horderedUnused hlocation H q A n Tn Dn ia ib va vb ell yLength Y segRefl
      segTrans commonPrefix lastPositive coreToA TnToA AToT ordinaryToA starredToA YToT hmissingY
      hElementaryY ha hb vertexY haY hbY hout hAia hAib missingNotA
  have halphaA : alpha ∉ TreeMissingColors phi A := missingNotA alpha ia ha.1 haY hout.1
  have hbetaA : beta ∉ TreeMissingColors phi A := missingNotA beta ib hb.1 hbY hout.2
  have horder := horderedUnused (Or.inl halphaA)
  have habIndex : ia.val < ib.val := by
    obtain ⟨i, j, hi, hj, hij⟩ := horder.1
    have hei := T.vertex_injective hi
    have hej := T.vertex_injective hj
    simpa [hei, hej] using hij
  have havb : va ≠ vb := by
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
    exact @helper_BstrictT_1127 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
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
  have missingSubset {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U) :
      TreeMissingColors phi S ⊆ TreeMissingColors phi U := by
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSU hv, hcv⟩
  have outsideStored (hcase :
      (0 < H.dividerCount ∧ (alpha ∈ TreeMissingColors phi (H.stage ⟨H.dividerCount, by omega⟩) ∨
        Disjoint ({alpha, beta} : Finset (Fin k)) (HierarchyStoredColorsAt H q))) ∨
      (H.dividerCount = 0 ∧ (alpha ∈ TreeMissingColors phi Tn ∨
        Disjoint ({alpha, beta} : Finset (Fin k)) Dn))) :
      alpha ∉ Dn ∧ beta ∉ Dn := by
    exact @helper_outsideStored_1149 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@lastPositive) (@TnToA) (@hAib) (@halphaA) (@hbetaA) (@rpB) (@aboveB) (@strictB)
        (@belowB) (@genB) (@baseB) (@HB) (@missingSubset) (@hcase)
  have finish (hDn : alpha ∉ Dn ∧ beta ∉ Dn) :
      TwoColorComponent G phi alpha beta (Sum.inl va) =
        TwoColorComponent G phi alpha beta (Sum.inl vb) := by
    exact @helper_finish_4308 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone) (@hlower)
        (@hminimal) (@alpha) (@beta) (@hne) (@hmissingPrefix) (@horderedUnused) (@hlocation)
        (@segRefl) (@segTrans) (@commonPrefix) (@coreToA) (@TnToA) (@AToT) (@ordinaryToA)
        (@starredToA) (@hmissingY) (@hElementaryY) (@ha) (@hb) (@vertexY) (@haY) (@hbY) (@hout)
        (@hAia) (@hAib) (@halphaA) (@hbetaA) (@horder) (@habIndex) (@havb) (@BToT) (@AToB)
        (@ABstrict) (@BToY) (@BstrictT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@hMPB)
        (@hsB) (@baseB) (@hcoreB) (@hclosureB) (@hsupportB) (@HB) (@hcountB) (@hstagesB)
        (@hdividersB) (@goodB) (@hgoodB) (@missingSubset) (@outsideStored) (@hDn)
  exact ⟨fun h => finish (outsideStored (Or.inl h)),
    fun h => finish (outsideStored (Or.inr h))⟩

end GoldbergSeymour.ChangeLemmaBothOutsidePreparation

end
