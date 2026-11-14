/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TashkinovClosureTransport

public import LeanPool.GoldbergSeymour.TashkinovSeriesTerminalRoute

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceFirstMissingPositionInvariant

public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.HierarchyFieldTransport
public import LeanPool.GoldbergSeymour.GoodHierarchySameDividerTransport
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.LowerRoundProperties

/-!
# Step1Case Two Outside Prefix Hierarchy

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable abbrev helperRep474.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (mu : PartialEdgeColoring E k) →
  (C : TreeSequence G e0) →
  (newInput : PartialEdgeColoring E k) →
  (newSeries : TashkinovSeries G k ett.rounds e0 newInput) →
  (1 : ℕ) ≤ ett.1 →
  TreeSequenceInitialSegment
      (newSeries.data.tree
        (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ))))
      C →
  (newSeries.data.tree
          (⟨ett.1, by omega⟩ :
            Fin (ett.1 + (2 : ℕ)))).length <
      C.length →
  TreeSequenceInitialSegment C
      (newSeries.data.tree (Fin.last (ett.1 + (1 : ℕ)))) →
  mu = newSeries.data.coloring (Fin.last ett.1) →
  ExtendedTashkinovTree G k e0 newInput C mu := by
  classical
  intro V E _ _ _ G k e0 input T phi ett mu C newInput newSeries rp above strict below gen
  exact ⟨ett.rounds, rp, newSeries, above, strict, below, gen⟩

private noncomputable abbrev helperBaseC598.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq V] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (base : HierarchyBase ett phi) →
  (mu : PartialEdgeColoring E k) →
  (C : TreeSequence G e0) →
  let Tn : TreeSequence G e0 :=
    ett.series.data.tree (Fin.last ett.rounds).castSucc;
  (newInput : PartialEdgeColoring E k) →
  (newSeries : TashkinovSeries G k ett.rounds e0 newInput) →
  (rp : (1 : ℕ) ≤ ett.1) →
  (above :
      TreeSequenceInitialSegment
        (newSeries.data.tree
          (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ))))
        C) →
  (strict :
      (newSeries.data.tree
            (⟨ett.1, by omega⟩ :
              Fin (ett.1 + (2 : ℕ)))).length <
        C.length) →
  (below :
      TreeSequenceInitialSegment C
        (newSeries.data.tree
          (Fin.last (ett.1 + (1 : ℕ))))) →
  (gen :
      mu =
        newSeries.data.coloring (Fin.last ett.1)) →
  let rep :
    ExtendedTashkinovTree G k e0 newInput C mu :=
    helperRep474 G k e0 input T phi ett mu C
      newInput newSeries rp above strict below
      gen;
  (htree :
      newSeries.data.tree
          (Fin.last ett.rounds).castSucc =
        Tn) →
  newSeries.data.kind (Fin.last ett.rounds) =
      ett.series.data.kind
        (Fin.last ett.rounds) →
  (ett.series.data.kind
          (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE →
      newSeries.data.chosenVertex
          (Fin.last ett.rounds) =
        ett.series.data.chosenVertex
          (Fin.last ett.rounds)) →
  (ett.series.data.kind
          (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE →
      TashkinovClosure mu
        (TreeSequencePrefix Tn
          (↑base.supportPosition : ℕ)
          base.supportPositive
          (Nat.le_of_lt_succ
            base.supportPosition.isLt))
        base.closure) →
  let _ :
    Fin
      ((newSeries.data.tree
            (Fin.last
                ett.rounds).castSucc).length +
        (1 : ℕ)) :=
    Fin.cast
      (congrArg
        (fun S : TreeSequence G e0 =>
          S.length + 1)
        htree.symm)
      base.supportPosition;
  HierarchyBase rep mu := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base mu C Tn newInput newSeries rp above strict below
      gen rep htree hkind chosenAgree closureMu pos
  exact {
    core := base.core
    closure := base.closure
    supportPosition := pos
    supportPositive := by simpa [pos] using base.supportPositive
    terminalMissingColors := rfl
    parallel := by
      dsimp only [rep]
      intro hp
      have hpOld := hkind.symm.trans hp
      obtain ⟨hv, hc, hu⟩ := base.parallel hpOld
      refine ⟨?_, ?_, ?_⟩
      · rw [chosenAgree hpOld]
        have hvertex : (newSeries.data.tree (Fin.last ett.rounds).castSucc).vertex pos =
            Tn.vertex base.supportPosition := by
          dsimp [pos]
          generalize ht : newSeries.data.tree (Fin.last ett.rounds).castSucc = S at htree ⊢
          cases htree
          rfl
        rw [hvertex]; exact hv
      · simpa [pos, htree] using closureMu hpOld
      · simpa [htree] using hu
    nonparallel := by
      dsimp only [rep]
      intro hp
      exact (base.nonparallel (fun h => hp (hkind.trans h))).trans htree.symm }

private noncomputable abbrev helperKC712.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [ Fintype V] →
  [ Fintype E] →
  [ DecidableEq V] →
  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  (e0 : E) →
  (input : PartialEdgeColoring E k) →
  (T : TreeSequence G e0) →
  (phi : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T phi) →
  (0 : ℕ) < ett.rounds →
  (base : HierarchyBase ett phi) →
  (H : TashkinovHierarchy ett base) →
  (mu : PartialEdgeColoring E k) →
  (Bminus C : TreeSequence G e0) →
  Bminus.length < C.length →
  TreeSequenceInitialSegment C T →
  (∀ {S U W : TreeSequence G e0},
      TreeSequenceInitialSegment S U →
        TreeSequenceInitialSegment U W →
          TreeSequenceInitialSegment S W) →
  let Tn : TreeSequence G e0 :=
    ett.series.data.tree
      (Fin.last ett.rounds).castSucc;
  TreeSequenceInitialSegment base.core Bminus →
  TreeSequenceInitialSegment Bminus C →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
      TreeSequenceInitialSegment
        (H.stage j.castSucc) Bminus) →
  (newInput : PartialEdgeColoring E k) →
  (newSeries :
      TashkinovSeries G k ett.rounds e0
        newInput) →
  (rp : (1 : ℕ) ≤ ett.1) →
  (above :
      TreeSequenceInitialSegment
        (newSeries.data.tree
          (⟨ett.1, by omega⟩ :
            Fin (ett.1 + (2 : ℕ))))
        C) →
  (strict :
      (newSeries.data.tree
            (⟨ett.1, by omega⟩ :
              Fin
                (ett.1 +
                  (2 : ℕ)))).length <
        C.length) →
  (below :
      TreeSequenceInitialSegment C
        (newSeries.data.tree
          (Fin.last
            (ett.1 + (1 : ℕ))))) →
  (gen :
      mu =
        newSeries.data.coloring
          (Fin.last ett.1)) →
  let rep :
    ExtendedTashkinovTree G k e0
      newInput C mu :=
    helperRep474 G k e0 input T
      phi ett mu C newInput
      newSeries rp above strict
      below gen;
  (htree :
      newSeries.data.tree
          (Fin.last
              ett.rounds).castSucc =
        Tn) →
  (hkind :
      newSeries.data.kind
          (Fin.last
            ett.rounds) =
        ett.series.data.kind
          (Fin.last
            ett.rounds)) →
  (chosenAgree :
      ett.series.data.kind
            (Fin.last
              ett.rounds) =
          some
            TashkinovExtensionKind.PE →
        newSeries.data.chosenVertex
            (Fin.last
              ett.rounds) =
          ett.series.data.chosenVertex
            (Fin.last
              ett.rounds)) →
  (closureMu :
      ett.series.data.kind
            (Fin.last
              ett.rounds) =
          some
            TashkinovExtensionKind.PE →
        TashkinovClosure mu
          (TreeSequencePrefix
            Tn
            (↑base.supportPosition :
              ℕ)
            base.supportPositive
            (Nat.le_of_lt_succ
              base.supportPosition.isLt))
          base.closure) →
  let baseC :
    HierarchyBase rep
      mu :=
    helperBaseC598 G k e0
      input T phi ett base
      mu C newInput
      newSeries rp above
      strict below gen
      htree hkind
      chosenAgree
      closureMu;
  let stageC :
    Fin
        (H.dividerCount +
          (2 : ℕ)) →
      TreeSequence G e0 :=
    fun
      (j :
        Fin
          (H.dividerCount +
            (2 : ℕ))) ↦
    if
        (↑j : ℕ) =
          H.dividerCount +
            (1 : ℕ) then
      C
    else H.stage j;
  (∀
      (j :
        Fin
          (H.dividerCount +
            (2 : ℕ))),
      (↑j : ℕ) ≤
          H.dividerCount →
        stageC j =
          H.stage j) →
  stageC
        (Fin.last
          (H.dividerCount +
            (1 : ℕ))) =
      C →
  (∀
      (i :
        Fin
          H.dividerCount),
      (↑(H.dividerPosition
              i) :
          ℕ) ≤
        C.length) →
  TashkinovHierarchy
    rep baseC := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H mu Bminus C hBCstrict hCT segTrans Tn
      coreToB hBtoC stageToB newInput newSeries rp above strict below gen rep htree hkind
      chosenAgree closureMu baseC stageC stageOld stageLast divBound
  exact {
    dividerCount := H.dividerCount
    stage := stageC
    baseStage := by
      rw [stageOld 0 (by simp), H.baseStage]
      exact htree.symm
    terminalStage := stageLast
    nested := by
      intro j
      rw [stageOld j.castSucc (by have := j.isLt; simp; omega)]
      by_cases hj : j.val = H.dividerCount
      · have he : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
        rw [he, stageLast]
        exact segTrans (stageToB j) hBtoC
      · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
        exact H.nested j
    strict := by
      intro j
      rw [stageOld j.castSucc (by have := j.isLt; simp; omega)]
      by_cases hj : j.val = H.dividerCount
      · have he : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
        rw [he, stageLast]
        exact lt_of_le_of_lt (stageToB j).1 hBCstrict
      · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
        exact H.strict j
    dividerPosition := fun i => ⟨(H.dividerPosition i).val, Nat.lt_succ_of_le (divBound i)⟩
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := by
      intro i
      rw [stageOld ⟨i.val + 1, by omega⟩
        (by change i.val + 1 ≤ H.dividerCount; omega), H.dividerStage i]
      rw [TreeSequencePrefix, TreeSequencePrefix]
      congr 1
      · funext x
        exact hCT.2.1 (Fin.castLE (Nat.succ_le_succ (divBound i)) x)
      · funext x
        exact hCT.2.2 (Fin.castLE (divBound i) x)
    coreInsideFirst := by
      by_cases hd : H.dividerCount = 0
      · have he : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
            Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
        rw [he, stageLast]
        exact segTrans coreToB hBtoC
      · rw [stageOld ⟨1, by omega⟩ (by change 1 ≤ H.dividerCount; omega)]
        exact H.coreInsideFirst }

private theorem helper_peSupport_740.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    {r : ℕ} {inp : PartialEdgeColoring E k} (s : TashkinovSeries G k r e0 inp)
    (q : Fin r),
  s.data.kind q.succ = some TashkinovExtensionKind.PE →
  ∃ (v : V) (u : V) (f : E),
  s.data.chosenVertex q.succ = some v ∧
    s.data.connectingEdges q.succ = ({ f } : Finset E) ∧
      v ∈ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
        u ∉ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧ G.ends f = s(v, u) := by
  classical
  intro V E _ _ _ G k e0 r inp s q hp
  have step := s.certified q.succ
  generalize hi : q.succ = i at step
  cases step with
  | initial _ _ _ _ _ kind =>
    rw [hi, kind] at hp; cases hp
  | SE j _ _ _ _ _ choice _ coloring stored edges kind =>
    rw [hi, kind] at hp; cases hp
  | RE j _ _ _ _ available coloring stored edges kind =>
    rw [hi, kind] at hp; cases hp
  | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
      edges kind vertex outside delta gammaEq closure ordered strict =>
    simpa only [hi] using
      (show ∃ v u f, s.data.chosenVertex j.succ = some v ∧
        s.data.connectingEdges j.succ = {f} ∧
        v ∈ TreeSequenceVertexSet (s.data.tree j.succ.castSucc) ∧
        u ∉ TreeSequenceVertexSet (s.data.tree j.succ.castSucc) ∧
        G.ends f = s(v, u) from
        ⟨choice.vertex, choice.otherEndpoint, choice.edge, vertex, edges,
          choice.vertexDefective.1, choice.otherOutside, choice.edgeEnds⟩)

lemma Step1CaseTwoOutsidePrefixHierarchy {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      (open scoped Classical in LowerRoundProperties lower))
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (_ : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (beta gamma : Fin k) (hbeta : beta ∉ TreeMissingColors phi T)
    (mu : PartialEdgeColoring E k)
    (_ : gamma ≠ beta)
    (hproperMu : IsProperEdgeColoring G mu)
    (honeMu : IsOneEdgeUncolored mu e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi mu)
    (Bminus C : TreeSequence G e0)
    (hfixed : ∀ e, TreeIncidentEdge Bminus e → mu e = phi e)
    (hmissingFixed : ∀ v, v ∈ TreeSequenceVertexSet Bminus →
      MissingColors G mu v = MissingColors G phi v)
    (_ : gamma ∈ MissingColors G phi
      (C.vertex (Fin.last C.length)))
    (_ : beta ∈ MissingColors G mu
      (C.vertex (Fin.last C.length)))
    (f₃ : E) (_ : Incident G (C.vertex (Fin.last C.length)) f₃)
    (_ : mu f₃ = some gamma)
    (_ : ∀ v, v ∈ TreeSequenceVertexSet C → ∀ eta,
      eta ≠ gamma → eta ≠ beta →
      (eta ∈ MissingColors G mu v ↔ eta ∈ MissingColors G phi v))
    (hgammaReserved : gamma ∉ (HierarchyStoredColorsAt H
      (Fin.last H.dividerCount)).biUnion
        (good.gamma (Fin.last H.dividerCount)))
    (hAB : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) Bminus)
    (hBCstrict : Bminus.length < C.length)
    (hCT : TreeSequenceInitialSegment C T)
    (hBC : ∃ g, TreeSequenceAdjoinEdge Bminus g C) :
    ∃ (corrC : CorrespondingExtendedTashkinovTree G k e0 ett mu C)
      (baseC : HierarchyBase corrC.replacementETT mu)
      (KC : TashkinovHierarchy corrC.replacementETT baseC)
      (goodC : GoodHierarchy KC),
      ModColoring ett mu ∧
      MaximumProperty corrC.replacementETT ∧
      ((ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence mu
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) C) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence mu seed C)) ∧
      KC.dividerCount = H.dividerCount ∧
      2 * corrC.replacementETT.rounds + 11 ≤
        (TreeMissingColors mu
          (corrC.replacementETT.series.data.tree
            (Fin.last corrC.replacementETT.rounds).castSucc)).card ∧
      gamma ∉ (HierarchyStoredColorsAt KC
        (Fin.last KC.dividerCount)).biUnion
          (goodC.gamma (Fin.last KC.dividerCount)) ∧
      beta ∉ (HierarchyStoredColorsAt KC
        (Fin.last KC.dividerCount)).biUnion
          (goodC.gamma (Fin.last KC.dividerCount)) := by
  classical
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    exact hSU.trans hUW
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  have lastZero (h : H.dividerCount = 0) : A = base.core := by
    simp [A, HierarchyStarredStage, h, Fin.last]
  have coreToA : TreeSequenceInitialSegment base.core A := by
    exact H.coreInitialSegmentOfStarredStage (Fin.last H.dividerCount)
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    exact base.lastRoundInitialSegmentCore
  have coreToB := segTrans coreToA hAB
  have TnToB := segTrans TnToCore coreToB
  obtain ⟨g, hattach⟩ := hBC
  obtain ⟨hlenC, hBtoC, hg⟩ := hattach
  have TnToC := segTrans TnToB hBtoC
  have TnStrictC : Tn.length < C.length := lt_of_le_of_lt TnToB.1 hBCstrict
  have stageToB (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) Bminus := by
    exact (H.stageInitialSegmentOfStarredStage j (Fin.last H.dividerCount) (Fin.le_last _)).trans
      hAB
  have starredToB (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) Bminus := by
    exact (H.starredStageInitialSegmentOfLE j (Fin.last H.dividerCount) (Fin.le_last _)).trans
      hAB
  have vertexMem (S : TreeSequence G e0) (i : Fin (S.length + 1)) :
      S.vertex i ∈ TreeSequenceVertexSet S := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  have fixedC (j : Fin C.length) : mu (C.edge j) = phi (C.edge j) := by
    obtain ⟨i, hi⟩ := C.attaches j
    let ib : Fin (Bminus.length + 1) := ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩
    have hv : C.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) = Bminus.vertex ib := by
      exact hBtoC.2.1 ib
    apply hfixed
    refine ⟨Bminus.vertex ib, vertexMem _ _, ?_⟩
    change Bminus.vertex ib ∈ G.ends (C.edge j)
    rw [hi, hv]
    exact Sym2.mem_mk_right _ _
  have missingEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus) :
      TreeMissingColors mu S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    apply Finset.biUnion_congr rfl
    intro v hv
    exact hmissingFixed v (hS hv)
  have hmod : ModColoring ett mu :=
    Td G k e0 input T phi ett hMP hpositive hlower mu hproperMu honeMu
      (by simpa [ett.generatingColoring] using hstable)
  have terminalRoute :
      (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence mu Tn C) ∨
      ((ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence mu seed C) := by
    exact ett.series.terminalRouteColoringTransport hpositive phi ett.generatingColoring
      C TnToC TnStrictC (segTrans hCT ett.belowFinal) mu Bminus hBtoC hlenC
      (fun t _ => fixedC t) hmissingFixed
  obtain ⟨corrC⟩ := hmod.2.2 C TnToC TnStrictC terminalRoute
  have hMPC := MaximumPropertyTransport G k e0 ett mu hmod C corrC hMP
  refine ⟨corrC, ?_⟩
  rcases corrC with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
    hedges, hkinds, hproper, hone, hstableSeries⟩
  cases newETT with
  | mk r rp series above strict below gen =>
    cases hr
    have heq : series = newSeries := eq_of_heq hs
    cases heq
    let rep := @helperRep474 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@ett) (@mu) (@C) (@newInput) (@newSeries) (@rp) (@above) (@strict)
        (@below) (@gen)
    let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
    have hq : q.succ = Fin.last ett.rounds := Fin.ext (by simp [q]; omega)
    have htree : newSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
      simpa only [hq, Tn] using htrees q
    have hkind := hkinds (Fin.last ett.rounds)
    have chosenAgree (hp : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE) :
        newSeries.data.chosenVertex (Fin.last ett.rounds) =
          ett.series.data.chosenVertex (Fin.last ett.rounds) := by
      obtain ⟨v, u, f, hv, hf, hvin, huout, hends⟩ :=
        helper_peSupport_740 G k e0 ett.series q (by simpa [hq] using hp)
      obtain ⟨v', u', f', hv', hf', hvin', huout', hends'⟩ :=
        helper_peSupport_740 G k e0 newSeries q (by simpa [hq] using hkind.trans hp)
      have hedge : f' = f := by
        have hh := hedges q.succ
        rw [hf', hf] at hh
        simpa using hh
      have hvEq : v' = v := by
        rcases Sym2.eq_iff.mp (hends'.symm.trans (hedge ▸ hends)) with h | h
        · exact h.1
        · have hin : v ∈ TreeSequenceVertexSet (newSeries.data.tree q.succ.castSucc) := by
            simpa [hq, htree, Tn] using hvin
          exact False.elim (huout' (h.2 ▸ hin))
      simpa [hq] using hv'.trans ((congrArg some hvEq).trans hv.symm)
    have closureVertices (hp : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE) :
        TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet Bminus := by
      obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hp
      intro v hv
      apply TreeSequenceInitialSegmentVertexSetSubset coreToB
      rw [u.vertexSet]
      exact Finset.mem_union_right _ hv
    -- The closure need not be an ordered prefix of the core.
    have closureMu (hp : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE) :
        TashkinovClosure mu
          (TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
            (Nat.le_of_lt_succ base.supportPosition.isLt)) base.closure := by
      exact TashkinovClosure.transport_of_fixed hfixed hmissingFixed
        (closureVertices hp) (base.parallel hp).2.1
    let pos : Fin ((newSeries.data.tree (Fin.last ett.rounds).castSucc).length + 1) :=
      Fin.cast (congrArg (fun S : TreeSequence G e0 => S.length + 1) htree.symm)
        base.supportPosition
    let baseC := @helperBaseC598 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@mu) (@C) (@newInput) (@newSeries)
        (@rp) (@above) (@strict) (@below) (@gen) (@htree) (@hkind) (@chosenAgree) (@closureMu)
    refine ⟨baseC, ?_⟩
    let stageC : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
      fun j => if j.val = H.dividerCount + 1 then C else H.stage j
    have stageOld (j : Fin (H.dividerCount + 2)) (hj : j.val ≤ H.dividerCount) :
        stageC j = H.stage j := by
      exact ite_eq_right (show j.val ≠ H.dividerCount + 1 by omega)
    have stageLast : stageC (Fin.last (H.dividerCount + 1)) = C := by
      simp only [stageC, Fin.val_last, ite_true]
    have divBound (i : Fin H.dividerCount) : (H.dividerPosition i).val ≤ C.length :=
      H.dividerPosition_le_of_stage_prefix i ((stageToB i.succ).trans hBtoC)
    let KC := @helperKC712 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive) (@base) (@H) (@mu) (@Bminus) (@C)
        (@hBCstrict) (@hCT) (@segTrans) (@coreToB) (@hBtoC) (@stageToB) (@newInput) (@newSeries)
        (@rp) (@above) (@strict) (@below) (@gen) (@htree) (@hkind) (@chosenAgree) (@closureMu)
        (@stageOld) (@stageLast) (@divBound)
    have ordinaryEq (j : Fin (H.dividerCount + 1)) :
        KC.stage j.castSucc = H.stage j.castSucc :=
      stageOld j.castSucc (Nat.le_of_lt_succ j.isLt)
    have starredEq (j : Fin (H.dividerCount + 1)) :
        HierarchyStarredStage KC j = HierarchyStarredStage H j := by
      refine Fin.cases rfl (fun i => ordinaryEq i.succ) j
    have terminalMissing : TreeMissingColors mu Tn = TreeMissingColors phi Tn :=
      missingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToB)
    have storedEq : TashkinovStoredColors newSeries.data (Fin.last ett.rounds) =
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
      unfold TashkinovStoredColors
      simp only [hstored, ← hgen, ← ett.generatingColoring, htree, terminalMissing]
      rfl
    have nextPrefix (j : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (KC.stage j.succ) (H.stage j.succ) := by
      change TreeSequenceInitialSegment (stageC j.succ) (H.stage j.succ)
      by_cases last : j.val = H.dividerCount
      · have index : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
        rw [index, stageLast, H.terminalStage]
        exact hCT
      · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
        exact TreeSequenceInitialSegment.refl _
    let goodC : GoodHierarchy KC := good.transportOfPrefixColoringAgreement KC rfl rfl rfl
      htree hkind storedEq Bminus hfixed hmissingFixed coreToB closureVertices ordinaryEq starredEq
      stageToB starredToB hCT hBtoC hlenC fixedC nextPrefix
    have indexedStoredEq (j : Fin (H.dividerCount + 1)) :
        HierarchyStoredColorsAt KC j = HierarchyStoredColorsAt H j :=
      H.storedColors_eq_of_agreement KC j j storedEq (starredEq j)
        (missingEq _ (starredToB j).vertexSet_subset)
    refine ⟨KC, goodC, hmod, hMPC, terminalRoute, rfl, ?_, ?_, ?_⟩
    · change 2 * ett.rounds + 11 ≤
        (TreeMissingColors mu (newSeries.data.tree (Fin.last ett.rounds).castSucc)).card
      rw [htree, terminalMissing]
      exact hlarge
    · change gamma ∉ (HierarchyStoredColorsAt KC (Fin.last H.dividerCount)).biUnion
        (good.gamma (Fin.last H.dividerCount))
      rw [indexedStoredEq]
      exact hgammaReserved
    · change beta ∉ (HierarchyStoredColorsAt KC (Fin.last H.dividerCount)).biUnion
        (good.gamma (Fin.last H.dividerCount))
      rw [indexedStoredEq]
      intro hb
      obtain ⟨eta, he, hbe⟩ := Finset.mem_biUnion.mp hb
      have hm := (GoodHierarchyReservedDisjoint good (Fin.last H.dividerCount)).1 eta he hbe
      obtain ⟨v, hv, hbv⟩ := Finset.mem_biUnion.mp hm
      apply hbeta
      exact Finset.mem_biUnion.mpr ⟨v,
        TreeSequenceInitialSegmentVertexSetSubset
          (segTrans (segTrans (starredToB _) hBtoC) hCT) hv, hbv⟩
end GoldbergSeymour

end
