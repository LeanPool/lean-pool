/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AlgorithmFiveSixFixedRootRefresh

public import LeanPool.GoldbergSeymour.FiniteStrictGrowthReachesTerminal

public import LeanPool.GoldbergSeymour.ParallelSpecialClosurePreparation

public import LeanPool.GoldbergSeymour.TashkinovClosureOfRouteAndAllMissingClosed

/-!
# Current Elementary Or Good Hierarchy Construction Large

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_193.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → TechnicalInductionContext G k e0 ett.rounds
        → MaximumDegree G + (1 : ℕ) ≤ k → (11 : ℕ) ≤ TashkinovOrder G →
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree terminal.castSucc;
    let _ : TreeSequence G e0 := ett.series.data.tree terminal.succ; (2 : ℕ) * ett.rounds + (11 :
        ℕ) ≤ (TreeMissingColors generating Tn).card →
    let base : HierarchyBase ett generating := Classical.choice (HierarchyBaseExists ett); (
    ∀ {A B C : TreeSequence G e0}, TashkinovAugmentationSequence generating A B →
        TashkinovAugmentationSequence generating B C → TashkinovAugmentationSequence generating A
        C) →
    let _ : TreeSequence G e0 → Finset V → Prop := fun (J : TreeSequence G e0) (X : Finset V) =>
    ∃ (U : TreeSequence G e0), TreeSequenceVertexSet U = X ∧
    ∃ (corrU : CorrespondingExtendedTashkinovTree G k e0 ett generating U), MaximumProperty
        corrU.replacementETT ∧
    ∃ (baseU : HierarchyBase corrU.replacementETT generating), baseU.core = base.core ∧
        baseU.closure = base.closure ∧ (↑baseU.supportPosition : ℕ) = (↑base.supportPosition : ℕ)
        ∧
    ∃ (H : TashkinovHierarchy corrU.replacementETT baseU) (good : GoodHierarchy H),
        TreeColorSetMinusClosed G generating U ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))) ∧ TashkinovAugmentationSequence generating J U ∧
        (ett.series.data.kind terminal = some TashkinovExtensionKind.PE → base.core.length <
        U.length) ∧ (ett.series.data.kind terminal ≠ some TashkinovExtensionKind.PE → Tn.length <
        U.length);
    let _ : Finset V → Prop := fun (X : Finset V) =>
    ∃ (U : TreeSequence G e0), TreeSequenceVertexSet U = X ∧ TreeColorSetClosed G generating U
        (TreeMissingColors generating U); ett.series.data.kind terminal = some
        TashkinovExtensionKind.PE → ColoredVertexSetElementary G generating (TreeSequenceVertexSet
        T) ∨
    ∃ (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett generating
        U), MaximumProperty corrU.replacementETT ∧
    ∃ (baseU : HierarchyBase corrU.replacementETT generating) (H : TashkinovHierarchy
        corrU.replacementETT baseU) (_ : GoodHierarchy H), TreeColorSetClosed G generating U
        (TreeMissingColors generating U) ∧ TreeSequenceVertexSet U = TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP ctx hdegree hlarge terminal Tn F hbound
      base routeTrans State Terminal hk
  have prep := ParallelSpecialClosurePreparation G k e0 input T generating ett ctx hMP
    hk base hdegree (by simpa [Tn, terminal] using hbound)
  rcases prep with ⟨hTNCore, hlen, hElem | package⟩
  · exact Or.inl hElem
  · rcases package with ⟨U, corrU, hMPU, hroute, hinit, hlenU, baseU, hbc, hbl, hbs, H, hzero,
      hstage0,
      hstageU, good, hgood, hdisj, hminus, hcard, hterm⟩
    have hanchor : TashkinovAugmentationSequence generating Tn base.core := hTNCore
    let grow : ∀ X, State base.core X → ¬ Terminal X →
        ∃ Y, State base.core Y ∧ X ⊂ Y := by
      intro X hstate hnot
      rcases hstate with ⟨U0, hU0, corr, hMPc, basec, hbc', hbl', hbs', Hc, goodc,
          hminusc, hroutec, hsizec⟩
      have hbase : base.core.length < U0.length :=
        hsizec.1 (by simpa [terminal] using hk)
      have htn : Tn.length < U0.length :=
        lt_trans hlen hbase
      have hmissing :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current →
    ∀ (base' : HierarchyBase current generating') (K : TashkinovHierarchy current base'),
        GoodHierarchy K → 2 * current.rounds + 11 ≤ (TreeMissingColors generating'
        (current.series.data.tree (Fin.last current.rounds).castSucc)).card := by
        intro input' T' generating' current heq hmax base' K good'
        have cctx : TechnicalInductionContext G k e0 current.rounds :=
          heq.symm ▸ ctx
        exact TechnicalCurrentLadderMissingBoundLarge G k e0 input' T'
          generating' current hmax cctx hdegree hlarge
      have hnotc : ¬ TreeColorSetClosed G generating U0
          (TreeMissingColors generating U0) := by
        intro hc
        apply hnot
        exact ⟨U0, hU0, hc⟩
      have hres := AlgorithmFiveSixFixedRootRefresh G k e0 input T generating
        ett ctx hMP base hdegree hlarge hmissing U0 corr hMPc basec hbc' hbl' hbs'
        Hc goodc hminusc hnotc base.core
        (Or.inl ⟨hk, rfl, hanchor⟩)
        (by
          constructor
          · exact fun _ => hbase
          · intro h
            have hn : ett.series.data.kind terminal ≠ some TashkinovExtensionKind.PE := by
              simpa using h
            exact (hn hk).elim) hroutec
      rcases hres with
          ⟨a,b,c,d,e,g,f,W,ha,hb,hc,hd,he,hf,hg,hh,hi,hj,hk',hl,hm,hn,ho,hp,hq,hr,hs,ht,hu,pack⟩
      rcases pack with ⟨corrW,hMPW,hrouteW,baseW,hbcW,hblW,hbsW,HW,hcountW,rW⟩
      rcases rW with ⟨r1,r2,r3,r4,r5,r6,r7,r8,goodW,s1,s2,s3,nested⟩
      rcases nested with ⟨V',corrV,hMPV,hlenV,hrouteV,baseV,hbcV,hblV,hbsV,KV,hcountV,rV⟩
      rcases rV with ⟨v1,v2,v3,v4,v5,v6,v7,goodV,v8,v9,v10,hminusV⟩
      refine ⟨TreeSequenceVertexSet s3, ?_, ?_⟩
      · exact ⟨s3, rfl, V', corrV, hrouteV, baseV, hbcV, hblV, hbsV,
          goodV, hminusV, hlenV, ⟨fun _ => lt_trans hbase hMPV,
            fun _ => lt_trans htn hMPV⟩⟩
      · have hs : TreeSequenceVertexSet U0 ⊂ TreeSequenceVertexSet s3 :=
          TreeSequenceInitialSegmentVertexSetStrict
            (by
              have hz := hbsV.nested (Fin.last hbsV.dividerCount)
              have hl : hbsV.stage (Fin.last hbsV.dividerCount).castSucc = U0 := v1
              have hr : hbsV.stage (Fin.last hbsV.dividerCount).succ = s3 := v3
              rw [hl, hr] at hz
              exact hz) hMPV
        simpa [hU0] using hs
    have hinitState : State base.core (TreeSequenceVertexSet U) := by
      exact ⟨U, rfl, corrU, hMPU, baseU, hbc, hbl, hbs, H, good,
        hterm, hroute, ⟨fun _ => hlenU,
          fun _ => lt_trans hlen hlenU⟩⟩
    have hterm := FiniteStrictGrowthReachesTerminal
      (State base.core) Terminal grow hinitState
    rcases hterm with ⟨X, hstateX, hterminalX⟩
    rcases hterminalX with ⟨UF, hXF, hclosedF⟩
    rcases hstateX with ⟨UX, hUX, corrX, hMPX, baseX, hbcX, hblX, hbsX, HX, goodX,
      hminusX, hrouteX, hsizeX⟩
    have hclosedUX : TreeColorSetClosed G generating UX
        (TreeMissingColors generating UX) := by
      simpa [TreeColorSetClosed, TreeMissingColors, hXF, hUX] using hclosedF
    refine Or.inr ⟨UX, corrX, hMPX, baseX, HX, goodX, hclosedUX, ?_⟩
    have hfinalPE : TashkinovClosure generating Tn F := by
      have cert := ett.series.certified terminal
      generalize ht : terminal = z at cert
      cases cert with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
        have hz : terminal = 0 := by simp [ht]
        have hv := congrArg Fin.val hz
        simp [terminal] at hv
        have hp := ett.roundsPositive
        omega
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
        have hi : i.succ = terminal := by simp [ht]
        have hk' := hk
        rw [← hi, currentKind] at hk'
        simp at hk'
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          gamma gammaRule secondStable secondStableProper secondStableOneUncolored
          secondStableRelation exitWitness currentColoring currentProper
          currentOneUncolored currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma closedExtension orderedExtension
          strictExtension =>
        have hi : i.succ = terminal := by simp [ht]
        have heq : generating = ett.series.data.coloring i.succ := by
          calc
            generating = ett.series.data.coloring terminal := ett.generatingColoring
            _ = ett.series.data.coloring i.succ := by rw [hi]
        simpa [Tn, F, heq, hi] using closedExtension
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
        have hi : i.succ = terminal := by simp [ht]
        have hk' := hk
        rw [← hi, currentKind] at hk'
        simp at hk'
    have hvertex : TreeSequenceVertexSet UX = TreeSequenceVertexSet F := by
      have hcu : TashkinovClosure generating Tn UX :=
        TashkinovClosureOfRouteAndAllMissingClosed generating Tn UX
          (routeTrans hTNCore hrouteX) hclosedUX
      exact TashkinovClosureVertexSetUnique generating Tn UX F
        hcu hfinalPE
    exact hvertex

private theorem helper_branch_322.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett → TechnicalInductionContext G k e0 ett.rounds
        → MaximumDegree G + (1 : ℕ) ≤ k → (11 : ℕ) ≤ TashkinovOrder G →
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree terminal.castSucc;
    let _ : TreeSequence G e0 := ett.series.data.tree terminal.succ; ModColoring ett generating →
        (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors generating Tn).card →
    let base : HierarchyBase ett generating := Classical.choice (HierarchyBaseExists ett);
        (ett.series.data.kind terminal = some TashkinovExtensionKind.PE → Tn.length <
        base.core.length) →
    let _ : TreeSequence G e0 → Finset V → Prop := fun (J : TreeSequence G e0) (X : Finset V) =>
    ∃ (U : TreeSequence G e0), TreeSequenceVertexSet U = X ∧
    ∃ (corrU : CorrespondingExtendedTashkinovTree G k e0 ett generating U), MaximumProperty
        corrU.replacementETT ∧
    ∃ (baseU : HierarchyBase corrU.replacementETT generating), baseU.core = base.core ∧
        baseU.closure = base.closure ∧ (↑baseU.supportPosition : ℕ) = (↑base.supportPosition : ℕ)
        ∧
    ∃ (H : TashkinovHierarchy corrU.replacementETT baseU) (good : GoodHierarchy H),
        TreeColorSetMinusClosed G generating U ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))) ∧ TashkinovAugmentationSequence generating J U ∧
        (ett.series.data.kind terminal = some TashkinovExtensionKind.PE → base.core.length <
        U.length) ∧ (ett.series.data.kind terminal ≠ some TashkinovExtensionKind.PE → Tn.length <
        U.length);
    let _ : Finset V → Prop := fun (X : Finset V) =>
    ∃ (U : TreeSequence G e0), TreeSequenceVertexSet U = X ∧ TreeColorSetClosed G generating U
        (TreeMissingColors generating U); ¬ett.series.data.kind terminal = some
        TashkinovExtensionKind.PE → ColoredVertexSetElementary G generating (TreeSequenceVertexSet
        T) ∨
    ∃ (U : TreeSequence G e0) (corrU : CorrespondingExtendedTashkinovTree G k e0 ett generating
        U), MaximumProperty corrU.replacementETT ∧
    ∃ (baseU : HierarchyBase corrU.replacementETT generating) (H : TashkinovHierarchy
        corrU.replacementETT baseU) (_ : GoodHierarchy H), TreeColorSetClosed G generating U
        (TreeMissingColors generating U) ∧ TreeSequenceVertexSet U = TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP ctx hdegree hlarge terminal Tn F hmod
      hbound base hstrict State Terminal hk
  obtain ⟨J, U, corrU, hanch, hroute, hinit, hstrictU, hstrictN, hMPU,
    baseU, hrest⟩ := (AlgorithmFiveFiveBaseStage G k e0 input T generating ett hMP hmod base
    (fun h => hstrict h) (fun h => by
      exfalso
      apply hk
      simpa [terminal] using h) hbound (by
      intro h
      exfalso
      apply hk
      simpa [terminal] using h))
  rcases hrest with ⟨hbc,hbl,hbs,H,hrest⟩
  rcases hrest with ⟨hzero,hstage0,hstageU,hrest⟩
  rcases hrest with ⟨good,⟨⟨hgood,hdisj,hpe⟩,hterm⟩⟩
  have hanch2 :
      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
      ∃ f : E, ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f J := by
    rcases hanch with hbad | hgood
    · exfalso
      apply hk
      simpa [terminal] using hbad.1
    · exact hgood
  let grow : ∀ (X : Finset V), State J X → ¬ Terminal X →
        ∃ (Y : Finset V), State J Y ∧ X ⊂ Y := by
      intro X hstate hnot
      rcases hstate with ⟨U0,hU0,corr,hMPc,basec,hbc',hbl',hbs',Hc,goodc,hminusc,hroutec,hsizec⟩
      have htn : Tn.length < U0.length :=
        hsizec.2 (by simpa [terminal] using hk)
      have hnotc : ¬ TreeColorSetClosed G generating U0
          (TreeMissingColors generating U0) := by
        intro hc
        apply hnot
        exact ⟨U0,hU0,hc⟩
      have hmissing :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (current : ExtendedTashkinovTree G k e0 input' T'
        generating'), current.rounds = ett.rounds → MaximumProperty current →
    ∀ (base' : HierarchyBase current generating') (K : TashkinovHierarchy current base'),
        GoodHierarchy K → 2 * current.rounds + 11 ≤ (TreeMissingColors generating'
        (current.series.data.tree (Fin.last current.rounds).castSucc)).card := by
        intro input' T' generating' current heq hmax base' K good'
        exact TechnicalCurrentLadderMissingBoundLarge G k e0 input' T' generating'
          current hmax (heq.symm ▸ ctx) hdegree hlarge
      have hres := AlgorithmFiveSixFixedRootRefresh G k e0 input T generating ett ctx
        hMP base hdegree hlarge hmissing U0 corr hMPc basec hbc' hbl' hbs' Hc goodc
        hminusc hnotc J (Or.inr hanch2)
          ⟨(fun h => False.elim (hk (by simpa [terminal] using h))), fun _ => htn⟩ hroutec
      rcases hres with
          ⟨a,b,c,d,e,g,f,W,ha,hb,hc,hd,he,hf,hg,hh,hi,hj,hk',hl,hm,hn,ho,hp,hq,hr,hs,ht,hu,pack⟩
      rcases pack with ⟨corrW,hMPW,hrouteW,baseW,hbcW,hblW,hbsW,HW,hcountW,rW⟩
      rcases rW with ⟨r1,r2,r3,r4,r5,r6,r7,r8,goodW,s1,s2,s3,nested⟩
      rcases nested with ⟨V',corrV,hMPV,hlenV,hrouteV,baseV,hbcV,hblV,hbsV,KV,hcountV,rV⟩
      rcases rV with ⟨v1,v2,v3,v4,v5,v6,v7,goodV,v8,v9,v10,hminusV⟩
      refine ⟨TreeSequenceVertexSet s3, ?_, ?_⟩
      · exact ⟨s3,rfl,V',corrV,hrouteV,baseV,hbcV,hblV,hbsV,goodV,hminusV,
          hlenV,⟨fun h => False.elim (hk (by simpa [terminal] using h)),
            fun _ => lt_trans htn hMPV⟩⟩
      · have hs : TreeSequenceVertexSet U0 ⊂ TreeSequenceVertexSet s3 :=
          TreeSequenceInitialSegmentVertexSetStrict
            (by
              have hz := hbsV.nested (Fin.last hbsV.dividerCount)
              have hl : hbsV.stage (Fin.last hbsV.dividerCount).castSucc = U0 := v1
              have hr : hbsV.stage (Fin.last hbsV.dividerCount).succ = s3 := v3
              rw [hl, hr] at hz
              exact hz) hMPV
        simpa [hU0] using hs
  have hinitState : State J (TreeSequenceVertexSet U) :=
    ⟨U,rfl,corrU,hMPU,baseU,hbc,hbl,hbs,H,good,hterm,hroute,
      ⟨fun h => False.elim (hk (by simpa [terminal] using h)),
        fun _ => hstrictN (by simpa [terminal] using hk)⟩⟩
  rcases FiniteStrictGrowthReachesTerminal (State J) Terminal grow hinitState with
    ⟨X,hstateX,hterminalX⟩
  rcases hterminalX with ⟨UF,hXF,hclosedF⟩
  rcases hstateX with ⟨UX,hUX,corrX,hMPX,baseX,hbcX,hblX,hbsX,HX,goodX,hminusX,hrouteX,hsizeX⟩
  have hclosedUX : TreeColorSetClosed G generating UX
      (TreeMissingColors generating UX) := by
    simpa [TreeColorSetClosed,TreeMissingColors,hXF,hUX] using hclosedF
  refine Or.inr ⟨UX,corrX,hMPX,baseX,HX,goodX,hclosedUX,?_⟩
  have hfinalJ : TashkinovClosure generating J F := by
    have cert := ett.series.certified terminal
    generalize ht : terminal = z at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
      have hz : terminal = 0 := by simp [ht]
      have hv := congrArg Fin.val hz
      simp [terminal] at hv
      have hp := ett.roundsPositive
      omega
    | SE i pp po pc pn nr choice sa cc cs ce ck cv co cd cg ad ae closed ordered strict =>
      have hi : i.succ = terminal := by simp [ht]
      obtain ⟨f,hf,hfad⟩ := hanch2.2
      have he : f = choice.edge := by
        apply Finset.singleton_injective
        calc
          ({f} : Finset E) = ett.series.data.connectingEdges (Fin.last ett.rounds) := hf.symm
          _ = ett.series.data.connectingEdges terminal := by rfl
          _ = ett.series.data.connectingEdges i.succ := by rw [hi]
          _ = {choice.edge} := ce
      have hj : TreeSequenceAdjoinEdge Tn choice.edge J := by
        simpa [Tn,hi,he] using hfad
      have hae : TreeSequenceAdjoinEdge Tn choice.edge ad := by
        simpa [Tn,hi] using ae
      have hJ : J = ad := TreeSequenceAdjoinEdgeUnique Tn choice.edge J ad hj hae
      rw [ett.generatingColoring]
      simpa [hJ, F, hi] using closed
    | PE i pp po pc pn nr choice sa gamma gr ss sp so sr ew cc cp co cs ce ck cv coo cd cg closed
        ordered strict =>
      exact (hk (by simpa [ht] using ck)).elim
    | RE i pp po pc pn av cc cs ce ck cv coo cd cg ad ae closed ordered strict =>
      have hi : i.succ = terminal := by simp [ht]
      obtain ⟨f,hf,hfad⟩ := hanch2.2
      have he : f = av.edge := by
        apply Finset.singleton_injective
        calc
          ({f} : Finset E) = ett.series.data.connectingEdges (Fin.last ett.rounds) := hf.symm
          _ = ett.series.data.connectingEdges terminal := by rfl
          _ = ett.series.data.connectingEdges i.succ := by rw [hi]
          _ = {av.edge} := ce
      have hj : TreeSequenceAdjoinEdge Tn av.edge J := by
        simpa [Tn,hi,he] using hfad
      have hae : TreeSequenceAdjoinEdge Tn av.edge ad := by
        simpa [Tn,hi] using ae
      have hJ : J = ad := TreeSequenceAdjoinEdgeUnique Tn av.edge J ad hj hae
      rw [ett.generatingColoring]
      simpa [hJ, F, hi] using closed
  have hvertex := TashkinovClosureVertexSetUnique generating J UX F
    (TashkinovClosureOfRouteAndAllMissingClosed generating J UX hrouteX hclosedUX)
    hfinalJ
  exact hvertex

theorem CurrentElementaryOrGoodHierarchyConstructionLarge
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    ColoredVertexSetElementary G generating (TreeSequenceVertexSet T) \/
      exists (U : TreeSequence G e0)
          (corrU : CorrespondingExtendedTashkinovTree
            G k e0 ett generating U),
        MaximumProperty corrU.replacementETT /\
          exists baseU : HierarchyBase corrU.replacementETT generating,
            exists H : TashkinovHierarchy corrU.replacementETT baseU,
              exists _ : GoodHierarchy H,
                TreeColorSetClosed G generating U
                  (TreeMissingColors generating U) /\
                TreeSequenceVertexSet U =
                  TreeSequenceVertexSet
                    (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
  classical
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree terminal.castSucc
  let F : TreeSequence G e0 := ett.series.data.tree terminal.succ
  have terminalFacts := ett.coloringProperties
  have hmod : ModColoring ett generating := by
    apply ctx.currentSix ett rfl hMP
    · exact terminalFacts.1
    · exact terminalFacts.2
    · simpa only [ett.generatingColoring] using
        (sc2 G e0 Tn
        (TashkinovStoredColors ett.series.data terminal)).refl
          ⟨generating, terminalFacts⟩
  have hbound : 2 * ett.rounds + 11 ≤ (TreeMissingColors generating Tn).card := by
    simpa [terminal, Tn] using
      (TechnicalCurrentLadderMissingBoundLarge G k e0 input T generating ett
        hMP ctx hdegree hlarge)
  let base : HierarchyBase ett generating := Classical.choice (HierarchyBaseExists ett)
  have hstrict :
      ett.series.data.kind terminal = some TashkinovExtensionKind.PE →
      Tn.length < base.core.length := by
    intro hk
    exact (ParallelCoreAugmentationStrict ett base hk).2
  have routeTrans {A B C : TreeSequence G e0}
      (hAB : TashkinovAugmentationSequence generating A B)
      (hBC : TashkinovAugmentationSequence generating B C) :
      TashkinovAugmentationSequence generating A C := by
    exact Relation.ReflTransGen.trans hAB hBC
  by_cases hk : ett.series.data.kind terminal = some TashkinovExtensionKind.PE
  · exact @helper_branch_193 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating ett hMP ctx hdegree hlarge hbound routeTrans hk
  · exact @helper_branch_322 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating ett hMP ctx hdegree hlarge hmod hbound hstrict hk
end GoldbergSeymour

end
