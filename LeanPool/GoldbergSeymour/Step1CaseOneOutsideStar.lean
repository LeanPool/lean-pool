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
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColors
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.OutsideExitTransport
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColorsSubsetLast
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Case One Outside Star

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_chosenAgree_381.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (hpositive : (0 : ℕ) < ett.rounds) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (_ : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (_ : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ))
      (_ : (↑i₂ : ℕ) ≤ T.length),
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    (∀ {r : ℕ} {inp : PartialEdgeColoring E k} (s : TashkinovSeries G k r e0 inp)
        (q : Fin r),
        s.data.kind q.succ = some TashkinovExtensionKind.PE →
          ∃ (v : V) (u : V) (f : E),
            s.data.chosenVertex q.succ = some v ∧
              s.data.connectingEdges q.succ = ({ f } : Finset E) ∧
                v ∈ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
                  u ∉ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
                    G.ends f = s(v, u)) →
    ∀ (newInput : PartialEdgeColoring E k)
      (newSeries : TashkinovSeries G k ett.rounds e0 newInput),
    (∀ (i : Fin (ett.rounds + (1 : ℕ))),
        newSeries.data.connectingEdges i = ett.series.data.connectingEdges i) →
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    q.succ = Fin.last ett.rounds →
    newSeries.data.tree (Fin.last ett.rounds).castSucc = Tn →
    newSeries.data.kind (Fin.last ett.rounds) = ett.series.data.kind (Fin.last ett.rounds) →
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
    newSeries.data.chosenVertex (Fin.last ett.rounds) =
      ett.series.data.chosenVertex (Fin.last ett.rounds) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive i₁ i₂ hiorder hspos hsT Tn peSupport newInput
      newSeries hedges q hq htree hkind hp
  obtain ⟨v, u, f, hv, hf, hvin, huout, hends⟩ :=
    peSupport ett.series q (by simpa [hq] using hp)
  obtain ⟨v', u', f', hv', hf', hvin', huout', hends'⟩ :=
    peSupport newSeries q (by simpa [hq] using hkind.trans hp)
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

private theorem helper_closureVertices_400.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := Fin.isLt i₂
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    TreeSequenceInitialSegment base.core Bminus →
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
    TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet Bminus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base i₁ i₂ hiorder hspos Bminus coreToB hp
  obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hp
  intro v hv
  apply TreeSequenceInitialSegmentVertexSetSubset coreToB
  rw [u.vertexSet]
  exact Finset.mem_union_right _ hv

section TerminalStage

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input generating phi : PartialEdgeColoring E k} {tree : TreeSequence G e0}
    {ett : ExtendedTashkinovTree G k e0 input tree generating} {base : HierarchyBase ett phi}

private theorem terminalStageStep (hierarchy : TashkinovHierarchy ett base)
    (terminal : TreeSequence G e0)
    (stages : Fin (hierarchy.dividerCount + 2) → TreeSequence G e0)
    (old : ∀ index, index.val ≤ hierarchy.dividerCount → stages index = hierarchy.stage index)
    (last : stages (Fin.last (hierarchy.dividerCount + 1)) = terminal)
    (terminalPrefix : TreeSequenceInitialSegment
      (hierarchy.stage (Fin.last hierarchy.dividerCount).castSucc) terminal)
    (terminalStrict : (hierarchy.stage (Fin.last hierarchy.dividerCount).castSucc).length <
      terminal.length) (index : Fin (hierarchy.dividerCount + 1)) :
    TreeSequenceInitialSegment (stages index.castSucc) (stages index.succ) ∧
      (stages index.castSucc).length < (stages index.succ).length := by
  rw [old index.castSucc (Nat.le_of_lt_succ index.isLt)]
  by_cases final : index.val = hierarchy.dividerCount
  · have same : index = Fin.last hierarchy.dividerCount := Fin.ext final
    subst index
    rw [show (Fin.last hierarchy.dividerCount).succ =
      Fin.last (hierarchy.dividerCount + 1) from rfl, last]
    exact ⟨terminalPrefix, terminalStrict⟩
  · rw [old index.succ (by simp; have := index.isLt; omega)]
    exact ⟨hierarchy.nested index, hierarchy.strict index⟩

private theorem terminalDividerStage (hierarchy : TashkinovHierarchy ett base)
    (terminal : TreeSequence G e0) (terminalPrefix : TreeSequenceInitialSegment terminal tree)
    (stages : Fin (hierarchy.dividerCount + 2) → TreeSequence G e0)
    (old : ∀ index, index.val ≤ hierarchy.dividerCount → stages index = hierarchy.stage index)
    (bound : ∀ index : Fin hierarchy.dividerCount,
      (hierarchy.dividerPosition index).val ≤ terminal.length)
    (index : Fin hierarchy.dividerCount) :
    stages ⟨index.val + 1, by omega⟩ =
      TreeSequencePrefix terminal (hierarchy.dividerPosition index).val
        (hierarchy.dividerPositive index) (bound index) := by
  rw [old ⟨index.val + 1, by omega⟩
    (by change index.val + 1 ≤ hierarchy.dividerCount; exact Nat.succ_le_of_lt index.isLt),
    hierarchy.dividerStage index]
  exact ((TreeSequenceInitialSegment.prefix_segment terminal _
    (hierarchy.dividerPositive index) (bound index)).trans terminalPrefix).eq_prefix.symm

end TerminalStage

private theorem treeSequenceVertexCast {V E : Type*} {G : LooplessMultigraph V E}
    {e0 : E} {S U : TreeSequence G e0} (h : S = U) (i : Fin (S.length + 1)) :
    U.vertex (Fin.cast (congrArg (fun R : TreeSequence G e0 => R.length + 1) h) i) =
      S.vertex i := by
  cases h
  rfl

private theorem helper_branch_366.{u_1, u_2} :
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi),
   (0 : ℕ) < ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ : GoodHierarchy H)
     (beta : Fin k) (b₂ : V) (gamma : Fin k) (sigma : PartialEdgeColoring E k)
       (i₁ i₂ : Fin (T.length + (1 : ℕ))) (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ))
       (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)) (hsT : (↑i₂ : ℕ) ≤ T.length),
       let Bminus : TreeSequence G e0 :=
        TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
         (Decidable.byContradiction fun (a : ¬(↑i₂ : ℕ) - (1 : ℕ) ≤ T.length) ↦ by omega);
       let C : TreeSequence G e0 :=
        TreeSequencePrefix T (↑i₂ : ℕ)
         (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑i₂ : ℕ)) ↦ by omega) hsT;
       TreeSequenceInitialSegment C T →
        Bminus.length < C.length →
         let mu : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂);
         (∀ (f : E), TreeIncidentEdge Bminus f → mu f = phi f) →
          (∀ v ∈ TreeSequenceVertexSet Bminus, MissingColors G mu v = MissingColors G phi v) →
           (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
            (∀ {S U W : TreeSequence G e0},
              TreeSequenceInitialSegment S U →
               TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
             let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
             TreeSequenceInitialSegment base.core Bminus →
              TreeSequenceInitialSegment Tn Bminus →
               C.length = Bminus.length + (1 : ℕ) →
                TreeSequenceInitialSegment Bminus C →
                 (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                   TreeSequenceInitialSegment (H.stage j.castSucc) Bminus) →
                  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                    TreeSequenceInitialSegment (HierarchyStarredStage H j) Bminus) →
                    (∀ (j : Fin C.length), mu (C.edge j) = phi (C.edge j)) →
                     (∀ (S : TreeSequence G e0),
                       TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus →
                        TreeMissingColors mu S = TreeMissingColors phi S) →
                      (∀ {r : ℕ} {inp : PartialEdgeColoring E k} (s : TashkinovSeries G k r e0 inp)
                        (q : Fin r),
                        s.data.kind q.succ = some TashkinovExtensionKind.PE →
                         ∃ (v : V) (u : V) (f : E),
                          s.data.chosenVertex q.succ = some v ∧
                           s.data.connectingEdges q.succ = { f } ∧
                            v ∈ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
                             u ∉ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
                              G.ends f = s(v, u)) →
                        ∀ (corrC : CorrespondingExtendedTashkinovTree G k e0 ett mu C),
                        MaximumProperty corrC.replacementETT →
                        ∃ (baseC : HierarchyBase corrC.replacementETT mu)
                          (KC : TashkinovHierarchy corrC.replacementETT baseC)
                          (_goodC : GoodHierarchy KC),
                          MaximumProperty corrC.replacementETT ∧
                            KC.dividerCount = H.dividerCount := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H good beta b₂ gamma sigma
      i₁ i₂ hiorder hspos hsT Bminus C hCT hBCstrict mu hfixed hmissingFixed segRefl segTrans Tn
      coreToB TnToB hlenC hBtoC stageToB starredToB fixedC missingEq peSupport corrC hMPC
  rcases corrC with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
    hedges, hkinds, hproper, hone, hstableSeries⟩
  rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
  cases hr
  cases (show series = newSeries from eq_of_heq hs)
  let rep : ExtendedTashkinovTree G k e0 newInput C mu :=
    ⟨ett.rounds, rp, newSeries, above, strict, below, gen⟩
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hq : q.succ = Fin.last ett.rounds := Fin.ext (by simp [q]; omega)
  have htree : newSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
    simpa only [hq, Tn] using htrees q
  have hkind := hkinds (Fin.last ett.rounds)
  have chosenAgree :=
    helper_chosenAgree_381 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive) (@i₁) (@i₂)
        (@hiorder) (@hspos) (@hsT) (@peSupport) (@newInput) (@newSeries) (@hedges) (@hq) (@htree)
        (@hkind)
  have closureVertices :=
    helper_closureVertices_400 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@i₁) (@i₂)
        (@hiorder) (@hspos) (@coreToB)
  -- The closure need not be an ordered prefix of the core.
  have closureMu (hp : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) :=
    TashkinovClosure.transport_of_fixed hfixed hmissingFixed
      (closureVertices hp) (base.parallel hp).2.1
  let pos : Fin ((newSeries.data.tree (Fin.last ett.rounds).castSucc).length + 1) :=
    Fin.cast (congrArg (fun S : TreeSequence G e0 => S.length + 1) htree.symm)
      base.supportPosition
  let baseC : HierarchyBase rep mu :=
    { core := base.core
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
          rw [treeSequenceVertexCast htree.symm base.supportPosition]
          exact hv
        · simpa [pos, htree] using closureMu hpOld
        · simpa [htree] using hu
      nonparallel := by
        dsimp only [rep]
        intro hp
        exact (base.nonparallel (fun h => hp (hkind.trans h))).trans htree.symm }
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
  have step := terminalStageStep H C stageC stageOld stageLast
    ((stageToB (Fin.last H.dividerCount)).trans hBtoC)
    (lt_of_le_of_lt (stageToB (Fin.last H.dividerCount)).1 hBCstrict)
  let KC : TashkinovHierarchy rep baseC :=
    { dividerCount := H.dividerCount
      stage := stageC
      baseStage := by
        rw [stageOld 0 (by simp), H.baseStage]
        exact htree.symm
      terminalStage := stageLast
      nested := fun index => (step index).1
      strict := fun index => (step index).2
      dividerPosition := fun i => ⟨(H.dividerPosition i).val, Nat.lt_succ_of_le (divBound i)⟩
      dividerPositive := H.dividerPositive
      dividerIncreasing := H.dividerIncreasing
      dividerStage := terminalDividerStage H C hCT stageC stageOld divBound
      coreInsideFirst := by
        by_cases hd : H.dividerCount = 0
        · have he : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
              Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
          rw [he, stageLast]
          exact segTrans coreToB hBtoC
        · rw [stageOld ⟨1, by omega⟩ (by change 1 ≤ H.dividerCount; omega)]
          exact H.coreInsideFirst }
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
  exact ⟨KC, goodC, hMPC, rfl⟩

private theorem helper_rebuild_367.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    MaximumProperty ett →
    (0 : ℕ) < ett.rounds →
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
      (_ : GoodHierarchy H) (_ : ℕ) (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (b₂ : V),
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    ∀ (gamma : Fin k) (sigma : PartialEdgeColoring E k) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ))
      (hsT : (↑i₂ : ℕ) ≤ T.length),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (Decidable.byContradiction fun (a : ¬(↑i₂ : ℕ) - (1 : ℕ) ≤ T.length) ↦ by omega);
    let C : TreeSequence G e0 :=
      TreeSequencePrefix T (↑i₂ : ℕ)
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑i₂ : ℕ)) ↦ by omega) hsT;
    TreeSequenceInitialSegment A Bminus →
    TreeSequenceInitialSegment C T →
    Bminus.length < C.length →
    (∃ (g : E), TreeSequenceAdjoinEdge Bminus g C) →
    let mu : PartialEdgeColoring E k :=
      TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂);
    IsProperEdgeColoring G mu →
    IsOneEdgeUncolored mu e0 →
    (∀ (f : E), TreeIncidentEdge Bminus f → mu f = phi f) →
    (∀ v ∈ TreeSequenceVertexSet Bminus, MissingColors G mu v = MissingColors G phi v) →
    ∃ (corrC : CorrespondingExtendedTashkinovTree G k e0 ett mu C) (baseC :
      HierarchyBase corrC.replacementETT mu) (KC :
      TashkinovHierarchy corrC.replacementETT baseC) (_goodC : GoodHierarchy KC),
    MaximumProperty corrC.replacementETT ∧
    KC.dividerCount = H.dividerCount := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hproper hone hlower base H good q alpha
      beta hne b₂ A gamma sigma i₁ i₂ hiorder hspos hsT Bminus C hAB hCT hBCstrict hBCadjoin mu
      hproperMu honeMu hfixed hmissingFixed
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
  obtain ⟨g, hattach⟩ := hBCadjoin
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
  have hstable : StableColoring Tn
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi mu := by
    constructor
    · intro f ⟨v, hv, hvf⟩ _
      exact hfixed f ⟨v, TreeSequenceInitialSegmentVertexSetSubset TnToB hv, hvf⟩
    · intro v hv
      exact hmissingFixed v (TreeSequenceInitialSegmentVertexSetSubset TnToB hv)
  have hmod : ModColoring ett mu :=
    Td G k e0 input T phi ett hMP hpositive hlower mu hproperMu honeMu
      (by simpa [ett.generatingColoring] using hstable)
  have terminalRoute := ett.series.terminalRouteColoringTransport hpositive phi
    ett.generatingColoring C TnToC TnStrictC (segTrans hCT ett.belowFinal)
    mu Bminus hBtoC hlenC (fun t _ => fixedC t) hmissingFixed
  obtain ⟨corrC⟩ := hmod.2.2 C TnToC TnStrictC terminalRoute
  have hMPC := MaximumPropertyTransport G k e0 ett mu hmod C corrC hMP
  refine ⟨corrC, ?_⟩
  have peSupport {r : ℕ} {inp : PartialEdgeColoring E k}
      (s : TashkinovSeries G k r e0 inp) (q : Fin r)
      (hp : s.data.kind q.succ = some TashkinovExtensionKind.PE) :
      ∃ v u f, s.data.chosenVertex q.succ = some v ∧
        s.data.connectingEdges q.succ = {f} ∧
        v ∈ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
        u ∉ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
        G.ends f = s(v, u) := by
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
  exact helper_branch_366 G k e0 input T phi ett hpositive base H good beta b₂ gamma
    sigma i₁ i₂ hiorder hspos hsT hCT hBCstrict hfixed hmissingFixed segRefl segTrans coreToB
    TnToB hlenC hBtoC stageToB starredToB fixedC missingEq peSupport corrC hMPC

private theorem helper_continuation_1138.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    MaximumProperty ett →
    (0 : ℕ) < ett.rounds →
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
      (_ : GoodHierarchy H) (q : ℕ),
    H.dividerCount < q →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (other : ExtendedTashkinovTree G k e0 input' T' generating'),
        other.rounds = ett.rounds →
          MaximumProperty other →
            ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
              (_ : GoodHierarchy K),
              K.dividerCount < q →
                ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (a₂ b₂ : V),
    b₂ ∉ TreeSequenceVertexSet (HierarchyStarredStage H (Fin.last H.dividerCount)) →
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    beta ∈ TreeMissingColors phi A →
    ∀ (gamma : Fin k),
    gamma ≠ beta →
    ∀ (sigma : PartialEdgeColoring E k)
      (Q₂ : (TwoColorIncidenceGraph G sigma gamma beta).Walk (Sum.inl a₂) (Sum.inl b₂)),
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (∀ (f : E), TreeIncidentEdge T f → sigma f = phi f) →
    TreeExitPath T sigma gamma beta a₂ b₂ Q₂ →
    gamma ∈ MissingColors G sigma b₂ →
    ∀ (i₁ i₂ : Fin (T.length + (1 : ℕ))) (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ))
      (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)) (hsT : (↑i₂ : ℕ) ≤ T.length),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    let C : TreeSequence G e0 :=
      TreeSequencePrefix T (↑i₂ : ℕ)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
        hsT;
    TreeSequenceInitialSegment A Bminus →
    TreeSequenceInitialSegment Bminus C →
    TreeSequenceInitialSegment C T →
    TreeSequenceInitialSegment Bminus T →
    Bminus.length < C.length →
    C.vertex (Fin.last C.length) = b₂ →
    b₂ ∉ TreeSequenceVertexSet Bminus →
    (∃ (g : E), TreeSequenceAdjoinEdge Bminus g C) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hproper hone hlower base H good q
      hdivider hfewer alpha beta hne a₂ b₂ houtside A betaA gamma hgb sigma Q₂ hsproper hsone
      sigma_fixed hQ₂ hgSigma i₁ i₂ hiorder hspos hsT Bminus C hAB hBC hCT hBT hBCstrict hbC
      hbNotB hBCadjoin
  let K₂ := TwoColorComponent G sigma gamma beta (Sum.inl b₂)
  have hKtree : ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ K₂ ↔ v = b₂ :=
    TreeExitComponentMeetsTreeOnlyAtExit T sigma gamma beta b₂ hsproper hgSigma
      ⟨a₂, Q₂, hQ₂⟩
  let mu := TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂)
  have hproperMu : IsProperEdgeColoring G mu :=
    TwoColorComponentSwapProper G sigma gamma beta hgb hsproper _
  have honeMu : IsOneEdgeUncolored mu e0 := by
    constructor
    · simp [mu, TwoColorComponentSwap, hsone.1]
    · intro f hfe
      obtain ⟨c, hc⟩ := hsone.2 f hfe
      by_cases hf : Sum.inr f ∈ K₂
      · by_cases ha : sigma f = some gamma
        · exact ⟨beta, by simp [mu, TwoColorComponentSwap, K₂, hf, ha]⟩
        · by_cases hb : sigma f = some beta
          · exact ⟨gamma, by simp [mu, TwoColorComponentSwap, K₂, hf, hb, hgb.symm]⟩
          · refine ⟨c, ?_⟩
            change (if Sum.inr f ∈ K₂ then
              if sigma f = some gamma then some beta
              else if sigma f = some beta then some gamma else sigma f
              else sigma f) = some c
            rw [ite_eq_left hf, ite_eq_right ha, ite_eq_right hb]
            exact hc
      · exact ⟨c, by simp [mu, TwoColorComponentSwap, K₂, hf, hc]⟩
  have hfixed : ∀ f, TreeIncidentEdge Bminus f → mu f = phi f := by
    intro f hf
    obtain ⟨v, hv, hvf⟩ := hf
    have hvT := TreeSequenceInitialSegmentVertexSetSubset hBT hv
    have hvK : Sum.inl v ∉ K₂ := by
      intro h
      exact hbNotB ((hKtree v hvT).mp h ▸ hv)
    have unchanged : mu f = sigma f := by
      by_cases heK : Sum.inr f ∈ K₂
      · have noColor : ¬ (sigma f = some gamma ∨ sigma f = some beta) := by
          intro hc
          have ha : (TwoColorIncidenceGraph G sigma gamma beta).Adj
              (Sum.inl v) (Sum.inr f) := ⟨hvf, hc⟩
          exact hvK ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).trans heK)
        push Not at noColor
        simp [mu, TwoColorComponentSwap, K₂, heK, noColor.1, noColor.2]
      · simp [mu, TwoColorComponentSwap, K₂, heK]
    exact unchanged.trans (sigma_fixed f ⟨v, hvT, hvf⟩)
  have hmissingFixed : ∀ v ∈ TreeSequenceVertexSet Bminus,
      MissingColors G mu v = MissingColors G phi v := by
    intro v hv
    ext c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    have same : (∃ f, Incident G v f ∧ mu f = some c) ↔
        (∃ f, Incident G v f ∧ phi f = some c) := by
      constructor <;> rintro ⟨f, hf, hc⟩
      · exact ⟨f, hf, (hfixed f ⟨v, hv, hf⟩).symm.trans hc⟩
      · exact ⟨f, hf, (hfixed f ⟨v, hv, hf⟩).trans hc⟩
    exact not_congr same
  have hbMissing : beta ∈ MissingColors G mu b₂ :=
    (TwoColorComponentSwapMissingBehavior G sigma gamma beta hgb hsproper
      (Sum.inl b₂)).2.1 b₂ (show Sum.inl b₂ ∈ K₂ from rfl) hgSigma
  have rebuild :=
    @helper_rebuild_367 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett hMP hpositive hproper hone hlower base H good q alpha beta hne b₂ gamma
        sigma i₁ i₂ hiorder hspos hsT hAB hCT hBCstrict hBCadjoin hproperMu honeMu hfixed
        hmissingFixed
  obtain ⟨corrC, baseC, KC, goodC, hMPC, hdiv⟩ := rebuild
  have elementaryC : ColoredVertexSetElementary G mu (TreeSequenceVertexSet C) :=
    hfewer corrC.replacementETT corrC.rungAgreement hMPC baseC KC goodC
      (by rw [hdiv]; exact hdivider)
  obtain ⟨v, hvA, hbv⟩ := Finset.mem_biUnion.mp betaA
  have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hvA
  have hvC := TreeSequenceInitialSegmentVertexSetSubset hBC hvB
  have hbCmem : b₂ ∈ TreeSequenceVertexSet C := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last C.length, hbC⟩
  have hvb : v ≠ b₂ := by intro h; exact houtside (h ▸ hvA)
  have hbvMu : beta ∈ MissingColors G mu v := by
    rw [hmissingFixed v hvB]
    exact hbv
  exact (Finset.disjoint_left.mp (elementaryC hvC hbCmem hvb)) hbvMu hbMissing

lemma Step1CaseOneOutsideStar {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (q : ℕ) (hdivider : H.dividerCount < q)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < q →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (_ : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hterminal : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (hbeta : beta ∈ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (_ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (_ : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (_ : a₁ ≠ a₂) (_ : b₁ ≠ b₂)
    (horder : TreeVertexOrder T b₁ b₂)
    (f₁ f₂ : E)
    (_ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (_ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (_ : Sum.inr f₁ ∈ P₁.support)
    (_ : Sum.inr f₂ ∈ P₂.support)
    (houtside : b₂ ∉ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))) : False := by
  classical
  have segment_trans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) : TreeSequenceInitialSegment S W := by
    exact hSU.trans hUW
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have hAT : TreeSequenceInitialSegment A T := by
    exact H.lastStarredInitialSegment
  have hbT : b₂ ∈ TreeSequenceVertexSet T := hP₂.2.2.2.1
  have betaReserved : beta ∈ (HierarchyTerminalStoredColors H).biUnion
      (good.gamma (Fin.last H.dividerCount)) := by
    by_contra hn
    have hempty := hterminal beta (Finset.mem_sdiff.mpr ⟨hbeta, hn⟩)
    rw [hempty] at hf₂
    exact Finset.notMem_empty _ hf₂
  have betaA : beta ∈ TreeMissingColors phi A := by
    obtain ⟨eta, he, hbe⟩ := Finset.mem_biUnion.mp betaReserved
    exact (GoodHierarchyReservedDisjoint good (Fin.last H.dividerCount)).1 eta
      ((HierarchyTerminalStoredColorsSubsetLast H).1 he) hbe
  have hdegree : MaximumDegree G + 1 ≤ k := by
    have hinit := ett.series.certified 0
    cases hinit with
    | initial triple => exact triple.2.2.1
  obtain ⟨gamma, hgamma⟩ := MissingColorsNonemptyOfMaximumDegree G phi hdegree b₂
  have hgb : gamma ≠ beta := by
    intro h
    have hn : gamma ∉ PresentColors G phi b₂ := by simpa [MissingColors] using hgamma
    apply hn
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f₂, hif₂, h.symm ▸ (Finset.mem_filter.mp hf₂).2⟩
  have hgReserved : gamma ∉ (HierarchyStoredColorsAt H
      (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last H.dividerCount)) := by
    intro hg
    obtain ⟨eta, heta, hge⟩ := Finset.mem_biUnion.mp hg
    have hgm := (GoodHierarchyReservedDisjoint good (Fin.last H.dividerCount)).1
      eta heta hge
    obtain ⟨v, hvA, hgv⟩ := Finset.mem_biUnion.mp hgm
    have hvT := TreeSequenceInitialSegmentVertexSetSubset hAT hvA
    have hvb : v ≠ b₂ := by intro h; exact houtside (h ▸ hvA)
    exact (Finset.disjoint_left.mp (hElementary hvT hbT hvb)) hgv hgamma
  have hgTerminal : gamma ∉ (HierarchyTerminalStoredColors H).biUnion
      (good.gamma (Fin.last H.dividerCount)) := by
    intro hg
    obtain ⟨eta, heta, hge⟩ := Finset.mem_biUnion.mp hg
    exact hgReserved (Finset.mem_biUnion.mpr ⟨eta,
      (HierarchyTerminalStoredColorsSubsetLast H).1 heta, hge⟩)
  have hgClosed : TreeColorSetClosed G phi T {gamma} := by
    intro c hc
    have he : c = gamma := Finset.mem_singleton.mp hc
    subst c
    apply hterminal gamma
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨b₂, hbT, hgamma⟩, hgTerminal⟩
  have first : ∃ (sigma : PartialEdgeColoring E k)
      (Q₂ : (TwoColorIncidenceGraph G sigma gamma beta).Walk (Sum.inl a₂) (Sum.inl b₂)),
      IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
      (∀ f, TreeIncidentEdge T f → sigma f = phi f) ∧
      (∀ v ∈ TreeSequenceVertexSet T, MissingColors G sigma v = MissingColors G phi v) ∧
      TreeExitPath T sigma gamma beta a₂ b₂ Q₂ := by
    by_cases hag : alpha = gamma
    · subst gamma
      exact ⟨phi, P₂, hproper, hone, fun _ _ => rfl, fun _ _ => rfl, hP₂⟩
    · obtain ⟨sigma, hrec, hsproper, hsone, hsub, hout, hcopy⟩ :=
        P2716_T1_OutsideExitTransport G T phi alpha gamma beta hag hne hgb
          hproper hone hclosed hgClosed
      obtain ⟨Q₂, hQ₂, _, _⟩ := hcopy T (fun _ h => h) a₂ b₂ P₂ hP₂ hbT
      obtain ⟨_, _, hs, _, fixed⟩ := OutsideKempeRecoloringStable G e0 T ∅
        phi sigma alpha gamma hproper hone hrec
      exact ⟨sigma, Q₂, hsproper, hsone, fixed, hs.2, hQ₂⟩
  obtain ⟨sigma, Q₂, hsproper, hsone, sigma_fixed, sigma_missing, hQ₂⟩ := first
  have hgSigma : gamma ∈ MissingColors G sigma b₂ := by
    rw [sigma_missing b₂ hbT]
    exact hgamma
  obtain ⟨i₁, i₂, hi₁, hi₂, hiorder⟩ := horder
  have hAs : A.length < i₂.val := by
    by_contra h
    have hiA : i₂.val ≤ A.length := by omega
    let r : Fin (A.length + 1) := ⟨i₂.val, by omega⟩
    have hr : Fin.castLE (Nat.succ_le_succ hAT.1) r = i₂ := Fin.ext rfl
    have hv : A.vertex r = b₂ :=
      (hAT.2.1 r).symm.trans (by simpa only [hr] using hi₂)
    apply houtside
    change b₂ ∈ TreeSequenceVertexSet A
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨r, hv⟩
  have hspos : 1 ≤ i₂.val - 1 := by have := A.positive; omega
  have hsT : i₂.val ≤ T.length := Nat.le_of_lt_succ i₂.isLt
  let Bminus := TreeSequencePrefix T (i₂.val - 1) hspos (by omega)
  let C := TreeSequencePrefix T i₂.val (by omega) hsT
  have hAB : TreeSequenceInitialSegment A Bminus :=
    hAT.prefix_of_segment _ (by omega) (by omega)
  have hBC : TreeSequenceInitialSegment Bminus C :=
    TreeSequenceInitialSegment.prefix_prefix T _ _ hspos (by omega)
      (by omega) hsT (by omega)
  have hCT : TreeSequenceInitialSegment C T := ⟨hsT, fun _ => rfl, fun _ => rfl⟩
  have hBT := segment_trans hBC hCT
  have hBCstrict : Bminus.length < C.length := by
    simp only [Bminus, C, TreeSequencePrefix]
    omega
  have hbC : C.vertex (Fin.last C.length) = b₂ := by
    change T.vertex ⟨i₂.val, _⟩ = b₂
    exact hi₂
  have hbNotB : b₂ ∉ TreeSequenceVertexSet Bminus := by
    rw [← hi₂]
    exact hBT.vertex_not_mem_after (by change i₂.val - 1 < i₂.val; omega)
  have hBCadjoin : ∃ g, TreeSequenceAdjoinEdge Bminus g C := by
    have hlen : C.length = Bminus.length + 1 := by
      simp only [Bminus, C, TreeSequencePrefix]
      omega
    exact ⟨C.edge (Fin.cast hlen.symm (Fin.last Bminus.length)), hlen, hBC, rfl⟩
  exact helper_continuation_1138 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hMP) (@hpositive)
      (@hproper) (@hone) (@hlower) (@base) (@H) (@good) (@q) (@hdivider) (@hfewer) (@alpha)
      (@beta) (@hne) (@a₂) (@b₂) (@houtside) (@betaA) (@gamma) (@hgb) (@sigma) (@Q₂) (@hsproper)
      (@hsone) (@sigma_fixed) (@hQ₂) (@hgSigma) (@i₁) (@i₂) (@hiorder) (@hspos) (@hsT) (@hAB)
      (@hBC) (@hCT) (@hBT) (@hBCstrict) (@hbC) (@hbNotB) (@hBCadjoin)
end GoldbergSeymour

end
