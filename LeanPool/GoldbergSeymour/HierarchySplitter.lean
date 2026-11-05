/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved
public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.MaximumPropertyTransport
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.SameHierarchyStages
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.Td

public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Hierarchy Splitter

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch57Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (_ : (0 : ℕ) < ett.rounds)
  (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
  (_ : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE)
  (_ :
   (let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
   have seed : TreeSequence G e0 :=
    TreeSequencePrefix Tn (↑base.supportPosition : ℕ) base.supportPositive
     (Nat.le_of_lt_succ base.supportPosition.isLt);
   (∀ (j : Fin Tn.length), sigma (Tn.edge j) = phi (Tn.edge j)) ∧
    (∀ (j : Fin base.closure.length), sigma (base.closure.edge j) = phi (base.closure.edge j)) ∧
     TashkinovClosure sigma seed base.closure))
  (replacementInput : PartialEdgeColoring E k)
  (replacementSeries : TashkinovSeries G k ett.rounds e0 replacementInput)
  (finalGeneratingColoring : sigma = replacementSeries.data.coloring (Fin.last ett.rounds))
  (ladderTreesAgree :
   ∀ (i : Fin ett.rounds),
    replacementSeries.data.tree i.succ.castSucc = ett.series.data.tree i.succ.castSucc)
  (storedColorsAgree :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeries.data.stored i = ett.series.data.stored i)
  (connectingEdgesAgree :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))),
    replacementSeries.data.connectingEdges i = ett.series.data.connectingEdges i)
  (extensionKindsAgree :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), replacementSeries.data.kind i = ett.series.data.kind i)
  (replacementProper :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsProperEdgeColoring G (replacementSeries.data.coloring i))
  (replacementOneUncolored :
   ∀ (i : Fin (ett.rounds + (1 : ℕ))), IsOneEdgeUncolored (replacementSeries.data.coloring i) e0)
  (replacementStable :
   ∀ (i : Fin ett.rounds),
    StableColoring (ett.series.data.tree i.succ.castSucc)
     (TashkinovStoredColors ett.series.data i.succ) (ett.series.data.coloring i.succ)
     (replacementSeries.data.coloring i.succ))
  (rounds : ℕ) (roundsPositive : (1 : ℕ) ≤ rounds)
  (replacementData : TashkinovSeries G k rounds e0 replacementInput)
  (above :
   TreeSequenceInitialSegment
    (replacementData.data.tree (⟨rounds, (by omega)⟩ : Fin (rounds + (2 : ℕ)))) T)
  (strict :
   (replacementData.data.tree (⟨rounds, (by omega)⟩ : Fin (rounds + (2 : ℕ)))).length < T.length)
  (below : TreeSequenceInitialSegment T (replacementData.data.tree (Fin.last (rounds + (1 : ℕ)))))
  (generating : sigma = replacementData.data.coloring (Fin.last rounds))
  (rungAgreement :
   { rounds := rounds, roundsPositive := roundsPositive, series := replacementData,
      abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
      generatingColoring := generating :
      ExtendedTashkinovTree G k e0 replacementInput T sigma }.rounds =
    ett.rounds)
  (seriesPresentation :
   { rounds := rounds, roundsPositive := roundsPositive, series := replacementData,
      abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
      generatingColoring := generating :
      ExtendedTashkinovTree G k e0 replacementInput T sigma }.series ≍
    replacementSeries)
  (_ :
   MaximumProperty
    { replacementInput := replacementInput, replacementSeries := replacementSeries,
      replacementETT :=
       {
        rounds := rounds, roundsPositive := roundsPositive, series := replacementData,
        abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
        generatingColoring := generating : ExtendedTashkinovTree G k e0 replacementInput T sigma },
      rungAgreement := rungAgreement, seriesPresentation := seriesPresentation,
      finalGeneratingColoring := finalGeneratingColoring, ladderTreesAgree := ladderTreesAgree,
      storedColorsAgree := storedColorsAgree, connectingEdgesAgree := connectingEdgesAgree,
      extensionKindsAgree := extensionKindsAgree, replacementProper := replacementProper,
      replacementOneUncolored := replacementOneUncolored, replacementStable := replacementStable :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma T }.replacementETT),
  ∃ (baseSigma :
   HierarchyBase
    { replacementInput := replacementInput, replacementSeries := replacementSeries,
      replacementETT :=
       {
        rounds := rounds, roundsPositive := roundsPositive, series := replacementData,
        abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
        generatingColoring := generating : ExtendedTashkinovTree G k e0 replacementInput T sigma },
      rungAgreement := rungAgreement, seriesPresentation := seriesPresentation,
      finalGeneratingColoring := finalGeneratingColoring, ladderTreesAgree := ladderTreesAgree,
      storedColorsAgree := storedColorsAgree, connectingEdgesAgree := connectingEdgesAgree,
      extensionKindsAgree := extensionKindsAgree, replacementProper := replacementProper,
      replacementOneUncolored := replacementOneUncolored, replacementStable := replacementStable :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma T }.replacementETT
    sigma)
   (K :
   TashkinovHierarchy
    { replacementInput := replacementInput, replacementSeries := replacementSeries,
      replacementETT :=
       {
        rounds := rounds, roundsPositive := roundsPositive, series := replacementData,
        abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
        generatingColoring := generating : ExtendedTashkinovTree G k e0 replacementInput T sigma },
      rungAgreement := rungAgreement, seriesPresentation := seriesPresentation,
      finalGeneratingColoring := finalGeneratingColoring, ladderTreesAgree := ladderTreesAgree,
      storedColorsAgree := storedColorsAgree, connectingEdgesAgree := connectingEdgesAgree,
      extensionKindsAgree := extensionKindsAgree, replacementProper := replacementProper,
      replacementOneUncolored := replacementOneUncolored, replacementStable := replacementStable :
      CorrespondingExtendedTashkinovTree G k e0 ett sigma T }.replacementETT
    baseSigma),
   SameHierarchyStages H K

private theorem helper_chosenAgree_167.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (hpositive : (0 : ℕ) < ett.rounds)
      (_ : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE)
      (replacementInput : PartialEdgeColoring E k)
      (replacementSeries : TashkinovSeries G k ett.rounds e0 replacementInput)
      (_ :
        (∀ (i : Fin (ett.rounds + (1 : ℕ))),
          replacementSeries.data.connectingEdges i = ett.series.data.connectingEdges i)),
      let q : Fin ett.rounds :=
        (⟨ett.rounds - (1 : ℕ),
            Nat.sub_lt (Nat.zero_lt_of_lt hpositive)
              (Decidable.byContradiction fun (a : ¬(0 : ℕ) < (1 : ℕ)) => by omega)⟩ :
          Fin ett.rounds);
      ∀ (_ : q.succ = Fin.last ett.rounds)
        (_ :
          replacementSeries.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE)
        (_ :
          (∀ (u v x y : V) (e : E)
            (_ :
              u ∈
                TreeSequenceVertexSet
                  (replacementSeries.data.tree (Fin.last ett.rounds).castSucc))
            (_ :
              v ∈
                TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc))
            (_ :
              x ∉
                TreeSequenceVertexSet
                  (replacementSeries.data.tree (Fin.last ett.rounds).castSucc))
            (_ :
              y ∉
                TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc))
            (_ : G.ends e = s(u, x)) (_ : G.ends e = s(v, y)), u = v)),
        replacementSeries.data.chosenVertex (Fin.last ett.rounds) =
          ett.series.data.chosenVertex (Fin.last ett.rounds) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive hPE replacementInput replacementSeries
      connectingEdgesAgree q hq hkind insideUnique
  have oldStep := ett.series.certified (Fin.last ett.rounds)
  have newStep := replacementSeries.certified (Fin.last ett.rounds)
  generalize oldIndex : Fin.last ett.rounds = oldTarget at oldStep
  generalize newIndex : Fin.last ett.rounds = newTarget at newStep
  cases oldStep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    rw [oldIndex] at hPE
    rw [initialKind] at hPE
    cases hPE
  | SE oi previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    rw [oldIndex] at hPE
    rw [currentKind] at hPE
    cases hPE
  | RE oi previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    rw [oldIndex] at hPE
    rw [currentKind] at hPE
    cases hPE
  | PE oi previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting oldChoice seriesAlternativeFails
      oldGamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness oldColoring oldProper oldOneUncolored
      oldStored oldEdges oldKind oldVertex oldOutside oldDelta oldGamma2
      closedExtension orderedExtension strictExtension =>
    have hio : oi = q := by
      apply Fin.ext
      have hv := congrArg Fin.val oldIndex
      simp [q] at hv ⊢
      omega
    subst oi
    cases newStep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      rw [newIndex] at hkind
      rw [initialKind] at hkind
      cases hkind
    | SE ni previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      rw [newIndex] at hkind
      rw [currentKind] at hkind
      cases hkind
    | RE ni previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      rw [newIndex] at hkind
      rw [currentKind] at hkind
      cases hkind
    | PE ni previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting newChoice seriesAlternativeFails
        newGamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness newColoring newProper newOneUncolored
        newStored newEdges newKind newVertex newOutside newDelta newGamma2
        closedExtension orderedExtension strictExtension =>
      have hin : ni = q := by
        apply Fin.ext
        have hv := congrArg Fin.val newIndex
        simp [q] at hv ⊢
        omega
      subst ni
      have hedge : newChoice.edge = oldChoice.edge := by
        have he := connectingEdgesAgree (Fin.last ett.rounds)
        rw [← hq] at he
        rw [newEdges, oldEdges] at he
        simpa using he
      have hnew : newChoice.vertex ∈ TreeSequenceVertexSet
          (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) := by
        simpa [hq] using newChoice.vertexDefective.1
      have hold : oldChoice.vertex ∈ TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
        simpa [hq] using oldChoice.vertexDefective.1
      have hnewOutside : newChoice.otherEndpoint ∉ TreeSequenceVertexSet
          (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) := by
        simpa [hq] using newChoice.otherOutside
      have holdOutside : oldChoice.otherEndpoint ∉ TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
        simpa [hq] using oldChoice.otherOutside
      have hv := insideUnique newChoice.vertex oldChoice.vertex
        newChoice.otherEndpoint oldChoice.otherEndpoint newChoice.edge
        hnew hold hnewOutside holdOutside
        newChoice.edgeEnds (hedge ▸ oldChoice.edgeEnds)
      have hvertices := newVertex.trans ((congrArg some hv).trans oldVertex.symm)
      simpa [hq] using hvertices

private theorem helper_branch_57.{u_1, u_2} :
    helperBranch57Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett hpositive base H hPE hbase replacementInput
      replacementSeries finalGeneratingColoring ladderTreesAgree storedColorsAgree
      connectingEdgesAgree extensionKindsAgree replacementProper replacementOneUncolored
      replacementStable rounds roundsPositive replacementData above strict below generating
      rungAgreement seriesPresentation hc
  cases rungAgreement
  have seriesSame : replacementData = replacementSeries :=
    eq_of_heq seriesPresentation
  cases seriesSame
  let q : Fin ett.rounds :=
    ⟨ett.rounds - 1, Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩
  have hq : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have hfinal : replacementSeries.data.tree (Fin.last ett.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    rw [← hq]
    exact ladderTreesAgree q
  have hkindEq : replacementSeries.data.kind (Fin.last ett.rounds) =
      ett.series.data.kind (Fin.last ett.rounds) := by
    have hk := extensionKindsAgree q.succ
    rw [hq] at hk
    exact hk
  have hkind : replacementSeries.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE := hkindEq.trans hPE
  have insideUnique : ∀ (u v x y : V) (e : E),
      u ∈ TreeSequenceVertexSet
          (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) →
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) →
      x ∉ TreeSequenceVertexSet
          (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) →
      y ∉ TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) →
      G.ends e = s(u, x) → G.ends e = s(v, y) → u = v := by
    intro u v x y e hu hv hx hy he₁ he₂
    rcases (Sym2.eq_iff.mp (he₁.symm.trans he₂)) with h | h
    · exact h.1
    · have hv' := hv
      rw [← hfinal] at hv'
      exact False.elim (hx (h.2 ▸ hv'))
  have chosenAgree := @helper_chosenAgree_167 V E inferInstance inferInstance inferInstance G k e0
      input T phi ett hpositive hPE replacementInput replacementSeries connectingEdgesAgree hq hkind
      insideUnique
  have transportVertex : ∀ (A B : TreeSequence G e0), ∀ (h : A = B),
      ∀ i : Fin (B.length + 1),
      A.vertex (Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1)
        h.symm) i) = B.vertex i := by
    intro A B h i
    cases h
    rfl
  let pos : Fin ((replacementSeries.data.tree
      (Fin.last ett.rounds).castSucc).length + 1) :=
    Fin.cast (congrArg (fun W : TreeSequence G e0 => W.length + 1)
      hfinal.symm) base.supportPosition
  let baseSigma : HierarchyBase
      { rounds := ett.rounds
        roundsPositive := by omega
        series := replacementSeries
        abovePenultimate := above
        strictAbovePenultimate := strict
        belowFinal := below
        generatingColoring := generating } sigma :=
    { core := base.core
      closure := base.closure
      supportPosition := pos
      supportPositive := by simpa [pos] using base.supportPositive
      terminalMissingColors := by rfl
      parallel := by
        dsimp
        intro hp
        have hp' : ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE := by
          exact hkindEq ▸ hp
        have hb := base.parallel hp'
        refine ⟨?_, ?_, ?_⟩
        · have hvertex :
              (replacementSeries.data.tree (Fin.last ett.rounds).castSucc).vertex pos =
          (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex
                  base.supportPosition := by
            exact transportVertex _ _ hfinal base.supportPosition
          rw [chosenAgree]
          rw [hvertex]
          simpa [hfinal] using hb.1
        · simpa [pos, hfinal] using hbase.2.2
        · simpa [hfinal] using hb.2.2
      nonparallel := by
        dsimp
        intro hp
        exact False.elim (hp hkind) }
  refine ⟨baseSigma, ?_⟩
  let K : TashkinovHierarchy _ baseSigma :=
    { dividerCount := H.dividerCount
      stage := H.stage
      baseStage := by simpa [hfinal] using H.baseStage
      terminalStage := H.terminalStage
      nested := H.nested
      strict := H.strict
      dividerPosition := H.dividerPosition
      dividerPositive := H.dividerPositive
      dividerIncreasing := H.dividerIncreasing
      dividerStage := H.dividerStage
      coreInsideFirst := H.coreInsideFirst }
  refine ⟨K, ?_⟩
  simp [SameHierarchyStages, baseSigma, K, hPE, hkind]

private theorem HierarchySplitter_finish_92.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi sigma : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (_ : 0 < ett.rounds)
      (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
      (_ : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE)
      (_ :
        (let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc;
        have seed :=
          TreeSequencePrefix Tn (↑base.supportPosition : ℕ) base.supportPositive
            (Nat.le_of_lt_succ base.supportPosition.isLt);
        (∀ (j : Fin Tn.length), sigma (Tn.edge j) = phi (Tn.edge j)) ∧
          (∀ (j : Fin base.closure.length),
              sigma (base.closure.edge j) = phi (base.closure.edge j)) ∧
            TashkinovClosure sigma seed base.closure))
      (c : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
      (_ : MaximumProperty c.replacementETT),
      ∃ (baseSigma : HierarchyBase c.replacementETT sigma) (K :
        TashkinovHierarchy c.replacementETT baseSigma), SameHierarchyStages H K := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett hpositive base H hPE hbase c hc
  rcases c with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive replacementData above strict below generating =>
      exact @helper_branch_57 V E inferInstance inferInstance inferInstance inferInstance G k e0
          input T phi sigma ett hpositive base H hPE hbase replacementInput replacementSeries
          finalGeneratingColoring ladderTreesAgree storedColorsAgree connectingEdgesAgree
          extensionKindsAgree replacementProper replacementOneUncolored replacementStable rounds
          roundsPositive replacementData above strict below generating rungAgreement
          seriesPresentation hc
theorem HierarchySplitter {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hproperSigma : IsProperEdgeColoring G sigma)
    (honeSigma : IsOneEdgeUncolored sigma e0)
    (hcombined : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (hbuilt : TashkinovAugmentationSequence sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) T) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
      MaximumProperty corr.replacementETT ∧
      ∃ baseSigma : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT baseSigma,
          SameHierarchyStages H K := by
  classical
  have hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma := by
    simpa [ett.generatingColoring] using hcombined.1
  have hmod : ModColoring ett sigma := by
    exact Td G k e0 input T phi ett hMP hpositive hlower sigma
      hproperSigma honeSigma hstable
  rcases hmod with ⟨hsProper, hsOne, hmodProp⟩
  have hbase := CombinedStableClosurePreserved G k e0 input T phi phi sigma ett
    hpositive base ett.generatingColoring hPE hproperPhi honePhi hproperSigma honeSigma hcombined
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  have hinitial : TreeSequenceInitialSegment Tn T := by
    have hi : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        (Fin.last ett.rounds).castSucc := Fin.ext (by rfl)
    change TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) T
    rw [← hi]
    exact ett.abovePenultimate
  have hstrict : Tn.length < T.length := by
    have hi : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
        (Fin.last ett.rounds).castSucc := Fin.ext (by rfl)
    change (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < T.length
    rw [← hi]
    exact ett.strictAbovePenultimate
  have hcorr : Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma T) := by
    exact hmodProp T hinitial hstrict (Or.inl ⟨hPE, hbuilt⟩)
  let corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T :=
    Classical.choice hcorr
  have hcorrMP : MaximumProperty corr.replacementETT := by
    exact MaximumPropertyTransport G k e0 ett sigma
      ⟨hsProper, hsOne, hmodProp⟩ T corr hMP
  refine ⟨corr, hcorrMP, ?_⟩
  have finish : ∀ (c : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
      MaximumProperty c.replacementETT →
      ∃ baseSigma : HierarchyBase c.replacementETT sigma,
        ∃ K : TashkinovHierarchy c.replacementETT baseSigma,
          SameHierarchyStages H K := by
    exact @HierarchySplitter_finish_92 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi sigma ett hpositive base H hPE hbase
  exact finish corr hcorrMP

end GoldbergSeymour

end
