/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.InterchangePEClosedCore
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Interchange PETree Constituent

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_sharedCore_164.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0
        : ℕ) < ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored
        sigma e0) (_ : CombinedStableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) base.closure (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)) generating sigma),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) =>
    by
                omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : q.succ = n) (_ : q.succ = Fin.last ett.rounds) (gamma : Fin k) (secondStable :
        PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (_ : ParallelExtensionColor ett.series.data
        q.castSucc choice.selected choice.vertex gamma) (_ : StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
        choice.selected secondStable) (_ : ett.series.data.coloring q.succ = TwoColorComponentSwap
        G secondStable gamma choice.color (Sum.inl choice.vertex)) (_ :
        ett.series.data.chosenVertex q.succ = some choice.vertex) (_ : ett.series.data.kind n =
        some TashkinovExtensionKind.PE), choice.color ∈ TreeMissingColors sigma base.core ∧
        TreeColorSetClosed G sigma base.core { choice.color } := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper
      hone hstable n q hqn hlast gamma secondStable choice gammaRule secondStableRelation
      currentColoring currentVertex hPE'
  have hgm : gamma ∈ MissingColors G secondStable choice.vertex := by
    exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
  have hse : secondStable choice.edge = some choice.color := by
    have hs := secondStableRelation.1 choice.edge
      ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
      ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
        choice.edgeColor⟩
    exact hs.trans choice.edgeColor
  have hswap : choice.color ∈ MissingColors G
      (TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex)) choice.vertex := by
    unfold MissingColors
    simp only [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_univ _
    · intro hp
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨e, he, hec⟩
      have heold : secondStable e = some gamma ∨
          secondStable e = some choice.color := by
        by_cases hc : Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex)
        · simp [TwoColorComponentSwap, hc] at hec
          by_cases hg : secondStable e = some gamma
          · exact Or.inl hg
          · by_cases hd : secondStable e = some choice.color
            · exact Or.inr hd
            · simp [hg, hd] at hec
        · right
          simpa [TwoColorComponentSwap, hc] using hec
      have heK : Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex) := by
        change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
          (Sum.inr e) = (TwoColorIncidenceGraph G secondStable gamma
              choice.color).connectedComponentMk
          (Sum.inl choice.vertex)
        rcases heold with hg | hd
        · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            (by simp [TwoColorIncidenceGraph, he, hg])
        · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            (by simp [TwoColorIncidenceGraph, he, hd])
      have hneq : gamma ≠ choice.color := by
        intro heq
        have hgp : gamma ∈ PresentColors G secondStable choice.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨choice.edge, choice.edgeIncident, heq ▸ hse⟩
        have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
          simpa [MissingColors] using hgm
        exact hnot hgp
      have hgp : gamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases heold with heold | heold
        · exact ⟨e, he, heold⟩
        · exfalso
          have hs : TwoColorComponentSwap G secondStable gamma choice.color
              (Sum.inl choice.vertex) e = some gamma := by
            simp [TwoColorComponentSwap, heK, heold]
          exact hneq (Option.some.inj (hs.symm.trans hec))
      have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hgm
      exact hnot hgp
  have hgen : choice.color ∈ MissingColors G generating choice.vertex := by
    have hcur : ett.series.data.coloring n =
        TwoColorComponentSwap G secondStable gamma choice.color
          (Sum.inl choice.vertex) := by
      rw [← hqn]
      exact currentColoring
    have hcur' : ett.series.data.coloring (Fin.last ett.rounds) =
        TwoColorComponentSwap G secondStable gamma choice.color
          (Sum.inl choice.vertex) := by
      rw [← hlast]
      exact currentColoring
    apply (congrArg (fun c => choice.color ∈ MissingColors G c choice.vertex)
      ett.generatingColoring).mpr
    apply (congrArg (fun c => choice.color ∈ MissingColors G c choice.vertex)
      hcur').mpr
    exact hswap
  have hvt : choice.vertex ∈ TreeSequenceVertexSet
      (ett.series.data.tree n.castSucc) := by
    simpa [hqn] using choice.vertexDefective.1
  have hdt : choice.color ∈ TreeMissingColors sigma
      (ett.series.data.tree n.castSucc) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨choice.vertex, hvt, (hstable.1.2 choice.vertex hvt).symm ▸ hgen⟩
  have hdtcore : choice.color ∈ TreeMissingColors sigma base.core := by
    obtain ⟨unionData⟩ := (base.parallel hPE).2.2
    simp only [TreeMissingColors, Finset.mem_biUnion]
    refine ⟨choice.vertex, ?_, ?_⟩
    · rw [unionData.vertexSet]
      apply Finset.mem_union_left
      simpa [n] using hvt
    · exact (hstable.1.2 choice.vertex hvt).symm ▸ hgen
  have hcore : TreeColorSetClosed G sigma base.core {choice.color} := by
    apply InterchangePECommonMissingClosed G k e0 input T generating sigma ett
      hMP hpositive hlower hPE' base hproper hone hstable choice.color
    · exact hdt
    · have augmentSubset : ∀ {A B : TreeSequence G e0},
          TashkinovAugmentationSequence generating A B →
          TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
        intro A B hab
        have initialSubset : ∀ {C D : TreeSequence G e0},
            TreeSequenceInitialSegment C D →
            TreeSequenceVertexSet C ⊆ TreeSequenceVertexSet D := by
          intro C D hCD x hx
          unfold TreeSequenceVertexSet at hx ⊢
          simp only [Finset.mem_image] at hx ⊢
          obtain ⟨i, hi, rfl⟩ := hx
          obtain ⟨hlen, hvertices, hedges⟩ := hCD
          exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i,
            Finset.mem_univ _, hvertices i⟩
        unfold TashkinovAugmentationSequence at hab
        induction hab using Relation.ReflTransGen.head_induction_on with
        | refl => exact fun x hx => hx
        | head hstep htail ih =>
          intro x hx
          exact ih (initialSubset hstep.2.1 hx)
      obtain ⟨unionData⟩ := (base.parallel hPE).2.2
      have prefixSubset : TreeSequenceVertexSet
          (TreeSequencePrefix
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)
            base.supportPosition.val base.supportPositive
            (Nat.le_of_lt_succ base.supportPosition.isLt)) ⊆
          TreeSequenceVertexSet base.closure := by
        exact augmentSubset (base.parallel hPE).2.1.1
      have hprefix : choice.vertex ∈ TreeSequenceVertexSet
          (TreeSequencePrefix
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)
            base.supportPosition.val base.supportPositive
            (Nat.le_of_lt_succ base.supportPosition.isLt)) := by
        simp only [TreeSequenceVertexSet, Finset.mem_image]
        refine ⟨⟨base.supportPosition.val, Nat.lt_succ_self _⟩, Finset.mem_univ _, ?_⟩
        change (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex base.supportPosition = _
        have cv : ett.series.data.chosenVertex (Fin.last ett.rounds) =
            some choice.vertex := by
          rw [← hlast]
          exact currentVertex
        exact Option.some.inj ((base.parallel hPE).1.symm.trans cv)
      have hclosureVertex : choice.vertex ∈ TreeSequenceVertexSet base.closure :=
        prefixSubset hprefix
      have hdc : choice.color ∈ TreeMissingColors sigma base.closure := by
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨choice.vertex, hclosureVertex,
          (hstable.2.2 choice.vertex hclosureVertex).symm ▸ hgen⟩
      exact hdc
  exact ⟨hdtcore, hcore⟩

private theorem helper_branch_126.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating sigma : PartialEdgeColoring E k) (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0
        : ℕ) < ett.rounds) (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (_ :
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE) (base :
        HierarchyBase ett generating) (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored
        sigma e0) (_ : CombinedStableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) base.closure (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)) generating sigma) (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) =>
    by
                omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : q.succ = n) (_ : q.succ = Fin.last ett.rounds) (ci : Fin ett.rounds) (_ :
        IsProperEdgeColoring G (ett.series.data.coloring ci.castSucc)) (_ : IsOneEdgeUncolored
        (ett.series.data.coloring ci.castSucc) e0) (_ : ColoredVertexSetClosed G
        (ett.series.data.coloring ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        ci.succ.castSucc))) (_ : ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring
        ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree ci.succ.castSucc))) (_ :
        ¬Nonempty (RevisitingExtensionCertificate ett.series.data ci.castSucc)) (choice :
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
        ci.succ.succ).length) (_ : q.succ = ci.succ), TreeInterchangeable G (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) sigma alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper
      hone hstable alpha beta halpha n q hqn hlast ci previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma
      gammaRule secondStable secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma closedExtension orderedExtension strictExtension target_eq
  have hci : ci = q := by
    apply Fin.ext
    have hv := congrArg Fin.val target_eq
    simp at hv
    omega
  subst ci
  have hsupport : ett.series.data.chosenVertex n = some choice.vertex := by
    rw [← hqn]
    exact currentVertex
  have hgamma : ett.series.data.gamma n = some gamma := by
    rw [← hqn]
    exact currentGamma
  have hdel : ett.series.data.delta n = some choice.color := by
    rw [← hqn]
    exact currentDelta
  have hPE' : ett.series.data.kind n =
      some TashkinovExtensionKind.PE := by
    change ett.series.data.kind (Fin.last ett.rounds) = _
    exact hPE
  have sharedCore := @helper_sharedCore_164 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper hone
      hstable hqn hlast gamma secondStable choice gammaRule secondStableRelation currentColoring
      currentVertex hPE'
  have coreSubset : TreeSequenceVertexSet
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆
      TreeSequenceVertexSet base.core := by
    obtain ⟨unionData⟩ := (base.parallel hPE).2.2
    intro vertex member
    rw [unionData.vertexSet]
    exact Finset.mem_union_left _ member
  have interchangeCore (color : Fin k) : TreeInterchangeable G
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) sigma choice.color color :=
    (InterchangePEClosedCore G k e0 input T generating sigma ett hMP hpositive hlower hPE'
      base hproper hone hstable choice.color color sharedCore.1 sharedCore.2).mono coreSubset
  by_cases ha : alpha = choice.color
  · subst alpha
    exact interchangeCore beta
  by_cases hb : beta = choice.color
  · subst beta
    exact (interchangeCore alpha).symm
  exact InterchangePETreeAwayFromDelta G k e0 input T generating sigma ett
    hMP hpositive hlower hPE' base hproper hone hstable choice.vertex gamma
    choice.color alpha beta (by simpa [n] using hsupport)
    (by simpa [n] using hgamma) (by simpa [n] using hdel) halpha ha hb

theorem InterchangePETreeConstituent {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (alpha beta : Fin k) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    alpha ∈ TreeMissingColors sigma Tn →
      TreeInterchangeable G Tn sigma alpha beta := by
  dsimp
  intro halpha
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hqn : q.succ = n := by
    apply Fin.ext
    simp [q, n]
    omega
  have hlast : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
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
    have hci : ci = q := by
      apply Fin.ext
      have hv := congrArg Fin.val target_eq
      simp at hv
      omega
    subst ci
    have hp : ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE := by rw [hlast]; exact hPE
    rw [currentKind] at hp
    simp at hp
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hci : ci = q := by
      apply Fin.ext
      have hv := congrArg Fin.val target_eq
      simp at hv
      omega
    subst ci
    have hp : ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE := by rw [hlast]; exact hPE
    rw [currentKind] at hp
    simp at hp
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_126 V E inferInstance inferInstance inferInstance inferInstance G
              k e0 input T generating sigma ett hMP hpositive hlower hPE base hproper hone
              hstable alpha beta halpha hqn hlast ci previousProper previousOneUncolored
              previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
              gamma gammaRule secondStable secondStableRelation exitWitness currentColoring
              currentProper currentOneUncolored currentStored currentEdges currentKind
              currentVertex currentOutside currentDelta currentGamma closedExtension
              orderedExtension strictExtension target_eq
end GoldbergSeymour

end
