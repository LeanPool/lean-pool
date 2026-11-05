/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HkuParallelBoundaryStructure
public import LeanPool.GoldbergSeymour.OrderedTreeUnionAugmentationSequence

/-!
# Parallel Core Augmentation Strict

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch144Conditions.{u_1, u_2} : Prop :=
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k
        e0 input T phi) (base : HierarchyBase ett phi),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let supportPrefix : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : ett.series.data.chosenVertex (Fin.last ett.rounds) = some ((ett.series.data.tree
        (Fin.last ett.rounds).castSucc).vertex base.supportPosition)) (_ : TashkinovClosure phi
        (TreeSequencePrefix (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (↑base.supportPosition : ℕ) base.supportPositive (Nat.le_of_lt_succ
        base.supportPosition.isLt)) base.closure) (_ : OrderedTreeUnion (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) base.closure base.core) (_ : TashkinovAugmentationSequence
        phi Tn base.core) (hrounds : (0 : ℕ) < ett.rounds),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : q.succ = n) (_ : Tn = ett.series.data.tree q.succ.castSucc) (_ : phi =
        ett.series.data.coloring q.succ) (_ : TreeSequenceVertexSet supportPrefix ⊆
        TreeSequenceVertexSet base.closure) (_ : Tn.vertex base.supportPosition ∈
        TreeSequenceVertexSet base.closure) (ci : Fin ett.rounds) (_ : IsProperEdgeColoring G
        (ett.series.data.coloring ci.castSucc)) (_ : IsOneEdgeUncolored (ett.series.data.coloring
        ci.castSucc) e0) (_ : ColoredVertexSetClosed G (ett.series.data.coloring ci.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree ci.succ.castSucc))) (_ :
        ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring ci.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree ci.succ.castSucc))) (_ : ¬Nonempty
        (RevisitingExtensionCertificate ett.series.data ci.castSucc)) (choice :
        MaximumDefectiveChoice G e0 (ett.series.data.tree ci.succ.castSucc) (TashkinovStoredColors
        ett.series.data ci.castSucc) (ett.series.data.coloring ci.castSucc)) (_ : (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data ci.castSucc)) choice.selected rho ∧ ¬Disjoint
        (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (ett.series.data.tree
        ci.succ.castSucc)))) (gamma : Fin k) (_ : ParallelExtensionColor ett.series.data
        ci.castSucc choice.selected choice.vertex gamma) (secondStable : PartialEdgeColoring E k)
        (_ : StableColoring (ett.series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data ci.castSucc)) choice.selected secondStable) (_ :
        TreeExit (ett.series.data.tree ci.succ.castSucc) secondStable gamma choice.color
        choice.vertex) (_ : ett.series.data.coloring ci.succ = TwoColorComponentSwap G
        secondStable gamma choice.color (Sum.inl choice.vertex)) (_ : IsProperEdgeColoring G
        (ett.series.data.coloring ci.succ)) (_ : IsOneEdgeUncolored (ett.series.data.coloring
        ci.succ) e0) (_ : ett.series.data.stored ci.succ = { choice.color, gamma }) (_ :
        ett.series.data.connectingEdges ci.succ = { choice.edge }) (_ : ett.series.data.kind
        ci.succ = some TashkinovExtensionKind.PE) (_ : ett.series.data.chosenVertex ci.succ = some
        choice.vertex) (_ : ett.series.data.outsideVertex ci.succ = some choice.otherEndpoint) (_
        : ett.series.data.delta ci.succ = some choice.color) (_ : ett.series.data.gamma ci.succ =
        some gamma) (_ : TashkinovClosure (ett.series.data.coloring ci.succ) (ett.series.data.tree
        ci.succ.castSucc) (ett.series.data.tree ci.succ.succ)) (_ : TreeSequenceInitialSegment
        (ett.series.data.tree ci.succ.castSucc) (ett.series.data.tree ci.succ.succ)) (_ :
        (ett.series.data.tree ci.succ.castSucc).length < (ett.series.data.tree
        ci.succ.succ).length) (_ : q.succ = ci.succ), TashkinovAugmentationSequence phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) base.core ∧ (ett.series.data.tree
        (Fin.last ett.rounds).castSucc).length < base.core.length

private theorem helper_hdeltaMissing_244.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [instE : DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k
        e0 input T phi) (hrounds : (0 : ℕ) < ett.rounds),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)) (_ : ett.series.data.coloring q.succ =
        TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)) (_ :
        gamma ∈ MissingColors G secondStable choice.vertex) (_ : gamma ≠ choice.color),
        choice.color ∈ MissingColors G (ett.series.data.coloring q.succ) choice.vertex := by
  classical
  intro V E _ _ instE G k e0 input T phi ett hrounds q gamma secondStable choice currentColoring
      hgammaMissing hgammaNe
  rw [currentColoring]
  simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro hpresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpresent
  obtain ⟨e, heIncident, heColor⟩ := hpresent
  by_cases heComponent : Sum.inr e ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex)
  · by_cases heGamma : secondStable e = some gamma
    · have hpGamma : gamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, heIncident, heGamma⟩
      have hnGamma : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hgammaMissing
      exact hnGamma hpGamma
    · by_cases heDelta : secondStable e = some choice.color
      · simp [TwoColorComponentSwap, heComponent, heDelta,
          hgammaNe, hgammaNe.symm] at heColor
      · simp [TwoColorComponentSwap, heComponent, heGamma, heDelta] at heColor
  · have heSecond : secondStable e = some choice.color := by
      simpa [TwoColorComponentSwap, heComponent] using heColor
    apply heComponent
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, heIncident, heSecond]

private theorem helper_hlengthNe_341.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k
        e0 input T phi) (base : HierarchyBase ett phi),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ v ∈ TreeSequenceVertexSet base.core, v ∉ TreeSequenceVertexSet Tn →
        TreeSequenceInitialSegment Tn base.core → Tn.length ≠ base.core.length := by
  classical
  intro V E _ _ instV instE G k e0 input T phi ett base n Tn v hvCore hvNotTn hsegment hlength
  rw [TreeSequenceVertexSet] at hvCore
  obtain ⟨j, -, hj⟩ :=
    (@Finset.mem_image _ _ (Classical.decEq V)).mp hvCore
  let i : Fin (Tn.length + 1) :=
    Fin.cast (congrArg (fun m => m + 1) hlength.symm) j
  have hcast : Fin.castLE (Nat.succ_le_succ hsegment.1) i = j := by
    apply Fin.ext
    simp [i]
  have hvertex := hsegment.2.1 i
  rw [hcast] at hvertex
  apply hvNotTn
  rw [TreeSequenceVertexSet]
  exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    ⟨i, Finset.mem_univ _, hvertex.symm.trans hj⟩

private theorem helper_continuation_309.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k
        e0 input T phi) (base : HierarchyBase ett phi),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let supportPrefix : TreeSequence G e0 := TreeSequencePrefix Tn (↑base.supportPosition : ℕ)
        base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt);
    ∀ (_ : TashkinovClosure phi (TreeSequencePrefix (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (↑base.supportPosition : ℕ) base.supportPositive (Nat.le_of_lt_succ
        base.supportPosition.isLt)) base.closure) (_ : OrderedTreeUnion (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) base.closure base.core) (_ : TashkinovAugmentationSequence
        phi Tn base.core) (hrounds : (0 : ℕ) < ett.rounds),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : Tn = ett.series.data.tree q.succ.castSucc) (_ : phi = ett.series.data.coloring q.succ)
        (_ : TreeSequenceVertexSet supportPrefix ⊆ TreeSequenceVertexSet base.closure) (_ :
        Tn.vertex base.supportPosition ∈ TreeSequenceVertexSet base.closure) (gamma : Fin k)
        (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (_ : ett.series.data.coloring q.succ =
        TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)) (_ :
        choice.vertex = Tn.vertex base.supportPosition) (_ : BoundaryColorEdges G
        (ett.series.data.coloring q.succ) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) gamma = { choice.edge } ∧ (
    ∀ g ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color,
    ∃ (w : V), TreeVertexOrder (ett.series.data.tree q.succ.castSucc) w choice.vertex ∧ Incident G
        w g) ∧ (ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
    ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree
        q.succ.castSucc), alpha ≠ choice.color → BoundaryColorEdges G (ett.series.data.coloring
        q.succ) (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) alpha = ∅)),
    let vertices : Finset V := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc);
    ∀ g ∈ BoundaryEdges G vertices, gamma ∈ MissingColors G secondStable choice.vertex → gamma ≠
        choice.color → ett.series.data.coloring q.succ g = some choice.color →
        TashkinovAugmentationSequence phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        base.core ∧ (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
        base.core.length := by
  classical
  intro V E _ _ instV instE G k e0 input T phi ett base n Tn supportPrefix hclosure hunion
      hsequence hrounds q hTnq hphiCurrent hprefixClosure hsupportClosure gamma secondStable
      choice currentColoring hsupport hboundaryInfo vertices g hgRawBoundary hgammaMissing
      hgammaNe hgCurrentDelta
  have hgCurrentBoundary : g ∈ BoundaryColorEdges G
      (ett.series.data.coloring q.succ) vertices choice.color :=
    Finset.mem_filter.mpr ⟨hgRawBoundary, hgCurrentDelta⟩
  obtain ⟨w, hworder, hwIncident⟩ := hboundaryInfo.2.1 g hgCurrentBoundary
  have hdeltaMissing := @helper_hdeltaMissing_244 V E inferInstance inferInstance instE G k e0 input
      T phi ett hrounds gamma secondStable choice currentColoring hgammaMissing hgammaNe
  have horderTn : TreeVertexOrder Tn w (Tn.vertex base.supportPosition) := by
    simpa [hTnq, hsupport] using hworder
  have hwPrefix : w ∈ TreeSequenceVertexSet supportPrefix := by
    obtain ⟨i, j, hi, hj, hij⟩ := horderTn
    have hjpos : j = base.supportPosition := Tn.vertex_injective hj
    subst j
    rw [TreeSequenceVertexSet]
    apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    let i' : Fin (base.supportPosition.val + 1) := ⟨i.val, by omega⟩
    refine ⟨i', Finset.mem_univ _, ?_⟩
    simpa [supportPrefix, TreeSequencePrefix, i'] using hi
  have hwClosure : w ∈ TreeSequenceVertexSet base.closure :=
    hprefixClosure hwPrefix
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hgRawBoundary
  obtain ⟨u, huTn, v, hvTn, huv⟩ := hgRawBoundary
  have hwEnds : w = u ∨ w = v := by
    change w ∈ G.ends g at hwIncident
    rw [huv] at hwIncident
    simpa using hwIncident
  have hwTn : w ∈ TreeSequenceVertexSet Tn := by
    obtain ⟨i, j, hi, hj, hij⟩ := horderTn
    rw [TreeSequenceVertexSet]
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨i, Finset.mem_univ _, hi⟩
  have hwVertices : w ∈ vertices := by
    simpa [vertices, hTnq] using hwTn
  have hwu : w = u := hwEnds.resolve_right
    (fun hwv => hvTn (hwv ▸ hwVertices))
  subst u
  have hphiG : phi g = some choice.color := by
    exact (congrFun hphiCurrent g).trans hgCurrentDelta
  have hdeltaSupport : choice.color ∈ MissingColors G phi
      (Tn.vertex base.supportPosition) := by
    have hmissingEq := congrArg
      (fun coloring => MissingColors G coloring (Tn.vertex base.supportPosition))
      hphiCurrent
    rw [hmissingEq, ← hsupport]
    exact hdeltaMissing
  have hvClosure : v ∈ TreeSequenceVertexSet base.closure := by
    by_contra hvNot
    have hgClosure : g ∈ BoundaryEdges G
        (TreeSequenceVertexSet base.closure) := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hwClosure, v, hvNot, huv⟩
    exact (hclosure.2 hgClosure hsupportClosure hphiG) hdeltaSupport
  have hvCore : v ∈ TreeSequenceVertexSet base.core := by
    rw [hunion.vertexSet]
    exact Finset.mem_union_right _ hvClosure
  have hvNotTn : v ∉ TreeSequenceVertexSet Tn := by
    simpa [vertices, hTnq] using hvTn
  have hsegment :=
    TashkinovAugmentationSequenceInitialSegment phi Tn base.core hsequence
  have hlengthNe := @helper_hlengthNe_341 V E inferInstance inferInstance instV instE G k e0 input T
      phi ett base v hvCore hvNotTn hsegment
  have hstrict : Tn.length < base.core.length :=
    lt_of_le_of_ne hsegment.1 hlengthNe
  simpa [Tn, n] using And.intro hsequence hstrict

private theorem helper_branch_144.{u_1, u_2} :
    helperBranch144Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ instV instE G k e0 input T phi ett base n Tn supportPrefix hchosen hclosure
      hunion hsequence hrounds q hsucc hTnq hphiCurrent hprefixClosure hsupportClosure ci
      previousProper previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting
      choice seriesAlternativeFails gamma gammaRule secondStable secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension target_eq
  have hv := congrArg Fin.val target_eq
  simp only [Fin.val_succ, Nat.add_right_cancel_iff] at hv
  have hci : ci = q := by ext; omega
  subst ci
  have hsupport : choice.vertex = Tn.vertex base.supportPosition := by
    change ett.series.data.chosenVertex n =
      some (Tn.vertex base.supportPosition) at hchosen
    rw [← hsucc, currentVertex] at hchosen
    exact Option.some.inj hchosen
  have hboundaryInfo := HkuParallelBoundaryStructure G k ett.rounds e0 input
    ett.series q choice.edge choice.color gamma choice.vertex
    (by simpa using currentKind) (by simpa using currentEdges)
    (by simpa using currentDelta) (by simpa using currentGamma)
    (by simpa using currentVertex)
  let vertices := TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
  have hchoiceBoundary : choice.edge ∈
      BoundaryColorEdges G choice.selected vertices choice.color := by
    rcases choice.edgeDefective with ⟨c, hcDefective, hcBoundary⟩
    have hcColor : choice.selected choice.edge = some c :=
      (Finset.mem_filter.mp hcBoundary).2
    have hc : c = choice.color :=
      Option.some.inj (hcColor.symm.trans choice.edgeColor)
    simpa [vertices, hc] using hcBoundary
  have hdefective : DefectiveColor G choice.selected vertices choice.color := by
    rcases choice.edgeDefective with ⟨c, hcDefective, hcBoundary⟩
    have hcColor : choice.selected choice.edge = some c :=
      (Finset.mem_filter.mp hcBoundary).2
    have hc : c = choice.color :=
      Option.some.inj (hcColor.symm.trans choice.edgeColor)
    simpa [vertices, hc] using hcDefective
  obtain ⟨g, hgBoundary, hgne⟩ : ∃ g,
      g ∈ BoundaryColorEdges G choice.selected vertices choice.color ∧
        g ≠ choice.edge := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Finset.one_lt_card.mp (show 1 <
        (BoundaryColorEdges G choice.selected vertices choice.color).card by
          exact lt_of_lt_of_le Nat.one_lt_two hdefective)
    by_cases haChoice : a = choice.edge
    · exact ⟨b, hb, by intro hbChoice; exact hab (haChoice.trans hbChoice.symm)⟩
    · exact ⟨a, ha, haChoice⟩
  have boundaryIncident : ∀ {e : E}, e ∈ BoundaryEdges G vertices →
      TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e := by
    intro e he
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨u, hu, v, hv, huv⟩ := he
    exact ⟨u, hu, by simp [Incident, huv]⟩
  have hgRawBoundary : g ∈ BoundaryEdges G vertices :=
    (Finset.mem_filter.mp hgBoundary).1
  have hchoiceRawBoundary : choice.edge ∈ BoundaryEdges G vertices :=
    (Finset.mem_filter.mp hchoiceBoundary).1
  have hgSecond : secondStable g = some choice.color := by
    have hstable := secondStableRelation.1 g (boundaryIncident hgRawBoundary)
      ⟨choice.color,
        Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
        (Finset.mem_filter.mp hgBoundary).2⟩
    exact hstable.trans (Finset.mem_filter.mp hgBoundary).2
  have hchoiceSecond : secondStable choice.edge = some choice.color := by
    have hstable := secondStableRelation.1 choice.edge
      (boundaryIncident hchoiceRawBoundary)
      ⟨choice.color,
        Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
        choice.edgeColor⟩
    exact hstable.trans choice.edgeColor
  have hgammaMissing : gamma ∈ MissingColors G secondStable choice.vertex := by
    rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
    exact gammaRule.1
  have hgammaNe : gamma ≠ choice.color := by
    intro h
    have hpresent : gamma ∈ PresentColors G secondStable choice.vertex := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨choice.edge, choice.edgeIncident, h ▸ hchoiceSecond⟩
    have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
      simpa [MissingColors] using hgammaMissing
    exact hnot hpresent
  have hchoiceComponent : Sum.inr choice.edge ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
  have hchoiceCurrent : ett.series.data.coloring q.succ choice.edge = some gamma := by
    rw [congrFun currentColoring choice.edge]
    simp [TwoColorComponentSwap, hchoiceComponent, hchoiceSecond]
  have hgOutside : Sum.inr g ∉
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    intro hgComponent
    have hgCurrent : ett.series.data.coloring q.succ g = some gamma := by
      rw [congrFun currentColoring g]
      simp [TwoColorComponentSwap, hgComponent, hgSecond]
    have hgGamma : g ∈ BoundaryColorEdges G
        (ett.series.data.coloring q.succ) vertices gamma :=
      Finset.mem_filter.mpr ⟨hgRawBoundary, hgCurrent⟩
    rw [hboundaryInfo.1] at hgGamma
    have hgeq : g = choice.edge := by simpa using hgGamma
    exact hgne hgeq
  have hgCurrentDelta : ett.series.data.coloring q.succ g =
      some choice.color := by
    rw [congrFun currentColoring g]
    simp [TwoColorComponentSwap, hgOutside, hgSecond]
  exact @helper_continuation_309 V E inferInstance inferInstance instV instE G k e0 input T phi
      ett base hclosure hunion hsequence hrounds hTnq hphiCurrent hprefixClosure hsupportClosure
      gamma secondStable choice currentColoring hsupport hboundaryInfo g hgRawBoundary
      hgammaMissing hgammaNe hgCurrentDelta
theorem ParallelCoreAugmentationStrict
    {V E : Type*} [Fintype V] [Fintype E]
    [instV : DecidableEq V] [instE : DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    TashkinovAugmentationSequence phi Tn base.core ∧
      Tn.length < base.core.length := by
  dsimp
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let supportPrefix := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  obtain ⟨hchosen, hclosure, ⟨hunion⟩⟩ := base.parallel hPE
  have hprefixSegment : TreeSequenceInitialSegment supportPrefix Tn := by
    refine ⟨Nat.le_of_lt_succ base.supportPosition.isLt, ?_, ?_⟩
    · intro i
      simp [supportPrefix, TreeSequencePrefix]
    · intro i
      simp [supportPrefix, TreeSequencePrefix]
  have hsequence : TashkinovAugmentationSequence phi Tn base.core :=
    OrderedTreeUnionAugmentationSequence phi supportPrefix Tn base.closure base.core
      hclosure.1 hprefixSegment hunion
  have hrounds : 0 < ett.rounds := lt_of_lt_of_le Nat.zero_lt_one ett.roundsPositive
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hsucc : q.succ = n := by
    apply Fin.ext
    simp [q, n]
    omega
  have hTnq : Tn = ett.series.data.tree q.succ.castSucc := by
    simpa [Tn] using congrArg
      (fun z : Fin (ett.rounds + 1) => ett.series.data.tree z.castSucc) hsucc.symm
  have hphiCurrent : phi = ett.series.data.coloring q.succ := by
    calc
      phi = ett.series.data.coloring n := by simpa [n] using ett.generatingColoring
      _ = ett.series.data.coloring q.succ := congrArg ett.series.data.coloring hsucc.symm
  have initialVertices {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro z hz
    rw [TreeSequenceVertexSet] at hz ⊢
    obtain ⟨i, -, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hz
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨Fin.castLE (Nat.succ_le_succ hAB.1) i, Finset.mem_univ _, hAB.2.1 i⟩
  have hprefixClosure : TreeSequenceVertexSet supportPrefix ⊆
      TreeSequenceVertexSet base.closure := by
    exact initialVertices
      (TashkinovAugmentationSequenceInitialSegment phi supportPrefix base.closure hclosure.1)
  have hsupportPrefix : Tn.vertex base.supportPosition ∈
      TreeSequenceVertexSet supportPrefix := by
    rw [TreeSequenceVertexSet]
    apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
    let i : Fin (base.supportPosition.val + 1) :=
      ⟨base.supportPosition.val, Nat.lt_succ_self _⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp [supportPrefix, TreeSequencePrefix, i]
  have hsupportClosure : Tn.vertex base.supportPosition ∈
      TreeSequenceVertexSet base.closure := hprefixClosure hsupportPrefix
  have hPEq : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE := by
    rw [hsucc]
    simpa [n] using hPE
  generalize target_eq : q.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hv := congrArg Fin.val target_eq
    simp at hv
    have hci : ci = q := by ext; omega
    subst ci
    rw [currentKind] at hPEq
    simp at hPEq
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hv := congrArg Fin.val target_eq
    simp at hv
    have hci : ci = q := by ext; omega
    subst ci
    rw [currentKind] at hPEq
    simp at hPEq
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_144 V E inferInstance inferInstance instV instE G k e0 input T phi
              ett base hchosen hclosure hunion hsequence hrounds hsucc hTnq hphiCurrent
              hprefixClosure hsupportClosure ci previousProper previousOneUncolored
              previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
              gamma gammaRule secondStable secondStableRelation exitWitness currentColoring
              currentProper currentOneUncolored currentStored currentEdges currentKind
              currentVertex currentOutside currentDelta currentGamma closedExtension
              orderedExtension strictExtension target_eq
end GoldbergSeymour

end
