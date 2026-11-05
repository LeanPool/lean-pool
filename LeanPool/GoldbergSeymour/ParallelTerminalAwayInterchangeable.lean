/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.ParallelExtensionUndoStable
public import LeanPool.GoldbergSeymour.TechnicalInductionContext
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase

/-!
# Parallel Terminal Away Interchangeable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hTauOne_234.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (_ :
        IsOneEdgeUncolored sigma e0),
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) =>
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (chosenGamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)) (_ : chosenGamma ≠ choice.color),
    let tau : PartialEdgeColoring E k := TwoColorComponentSwap G sigma chosenGamma choice.color
        (Sum.inl choice.vertex); IsOneEdgeUncolored tau e0 := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive sigma hone previous chosenGamma choice
      hGammaDelta tau
  unfold IsOneEdgeUncolored
  constructor
  · by_cases he : Sum.inr e0 ∈
        TwoColorComponent G sigma chosenGamma choice.color
          (Sum.inl choice.vertex)
    · simp [tau, TwoColorComponentSwap, he, hone.1]
    · simp [tau, TwoColorComponentSwap, he, hone.1]
  · intro e he0
    obtain ⟨c, hc⟩ := hone.2 e he0
    by_cases he : Sum.inr e ∈
        TwoColorComponent G sigma chosenGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases hcg : c = chosenGamma
      · exact ⟨choice.color, by
          simp [tau, TwoColorComponentSwap, he, hc, hcg]⟩
      · by_cases hcd : c = choice.color
        · exact ⟨chosenGamma, by
            simp [tau, TwoColorComponentSwap, he, hc, hcd,
              hGammaDelta.symm]⟩
        · exact ⟨c, by
            simp [tau, TwoColorComponentSwap, he, hc, hcg, hcd]⟩
    · exact ⟨c, by simp [tau, TwoColorComponentSwap, he, hc]⟩

private theorem helper_hTauInterchangeable_319.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : TechnicalInductionContext G k e0 ett.rounds) (_ : MaximumProperty ett)
        (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (alpha beta : Fin k),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) =>
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (chosenGamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)),
    let tau : PartialEdgeColoring E k := TwoColorComponentSwap G sigma chosenGamma choice.color
        (Sum.inl choice.vertex);
    ∀ (_ : IsProperEdgeColoring G tau) (_ : IsOneEdgeUncolored tau e0) (_ : StableColoring
        (ett.series.data.tree terminal.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc) tau) (_ : alpha ∈
        TreeMissingColors tau (ett.series.data.tree terminal.castSucc)), TreeInterchangeable G
        (ett.series.data.tree terminal.castSucc) tau alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive sigma alpha beta terminal previous
      chosenGamma choice tau hTauProper hTauOne hTauStable hAlphaTau
  by_cases hOne : ett.rounds = 1
  · have hbase := (TechnicalTheoremBase G k ett.rounds e0 input
        ett.series).2
    dsimp only at hbase
    have hTerminalOne : terminal.castSucc =
        (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [terminal, hOne]
    have hPreviousZero : previous.castSucc =
        (0 : Fin (ett.rounds + 1)) := by
      apply Fin.ext
      simp [previous, hOne]
    have hstableBase : StableColoring
        (ett.series.data.tree ⟨1, by omega⟩)
        (TashkinovStoredColors ett.series.data 0)
        (ett.series.data.coloring 0) tau := by
      simpa only [hTerminalOne, hPreviousZero] using hTauStable
    have hinter := hbase tau hTauProper hTauOne hstableBase alpha beta
      (Or.inl (by simpa only [hTerminalOne] using hAlphaTau))
    simpa only [hTerminalOne] using hinter
  · have hrPositive : 1 ≤ ett.rounds - 1 := by omega
    have hrBefore : ett.rounds - 1 < ett.rounds := by omega
    obtain ⟨restricted, hRounds, hRestrictedMP, hTreeEq, hDataEq⟩ :=
      CertifiedETTRestriction G k e0 input T phi ett hMP
        (ett.rounds - 1) hrPositive hrBefore
    let lowerTerminal : Fin (restricted.rounds + 1) :=
      Fin.last restricted.rounds
    have hCastLower : Fin.castLE (by omega) lowerTerminal =
        previous.castSucc := by
      apply Fin.ext
      simp [lowerTerminal, previous, hRounds]
    have hLowerTree : restricted.series.data.tree
          (Fin.last (restricted.rounds + 1)) =
        ett.series.data.tree terminal.castSucc := by
      rw [hTreeEq]
      congr 1
      apply Fin.ext
      simp [terminal, hRounds]
      omega
    obtain ⟨hLowerColor, hLowerStoredRaw, hLowerEdges, hLowerKind,
        hLowerVertex, hLowerOutside, hLowerDelta, hLowerGamma,
        hLowerStored, hLowerCert⟩ := hDataEq lowerTerminal
    have hLowerColor' : restricted.series.data.coloring lowerTerminal =
        ett.series.data.coloring previous.castSucc := by
      simpa only [hCastLower] using hLowerColor
    have hLowerStored' :
        TashkinovStoredColors restricted.series.data lowerTerminal =
          TashkinovStoredColors ett.series.data previous.castSucc := by
      simpa only [hCastLower] using hLowerStored
    have hLowerStable : StableColoring
        (restricted.series.data.tree
          (Fin.last (restricted.rounds + 1)))
        (TashkinovStoredColors restricted.series.data lowerTerminal)
        (restricted.series.data.coloring lowerTerminal) tau := by
      rw [hLowerTree, hLowerStored', hLowerColor']
      exact hTauStable
    have hlower := ctx.lowerTwo restricted
      (by omega) (by omega) hRestrictedMP
    dsimp only at hlower
    have hinter := hlower tau hTauProper hTauOne hLowerStable alpha beta
      (Or.inl (by simpa only [hLowerTree] using hAlphaTau))
    simpa only [hLowerTree] using hinter

private theorem helper_continuation_387.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : TechnicalInductionContext G k e0 ett.rounds) (_ : MaximumProperty ett)
        (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (alpha beta : Fin k)
        (_ : alpha ∈ TreeMissingColors sigma (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) (_ : beta ∈ TreeMissingColors sigma (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) => (
    by first  | omega
    )⟩ : Fin ett.rounds);
    ∀ (chosenGamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)) (_ : alpha ≠ chosenGamma) (_ : beta ≠
        chosenGamma) (_ : alpha ≠ choice.color) (_ : beta ≠ choice.color),
    let tau : PartialEdgeColoring E k := TwoColorComponentSwap G sigma chosenGamma choice.color
        (Sum.inl choice.vertex);
    ∀ (_ : IsProperEdgeColoring G tau) (_ : IsOneEdgeUncolored tau e0) (_ : StableColoring
        (ett.series.data.tree terminal.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc) tau) (_ : (
    ∀ (c : Fin k) (_ : c ≠ chosenGamma) (_ : c ≠ choice.color) (f : E), tau f = some c ↔ sigma f =
        some c)), TreeInterchangeable G (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        sigma alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive sigma alpha beta hAlphaMissing
      hBetaMissing terminal previous chosenGamma choice hAlphaGamma hBetaGamma hAlphaDelta
      hBetaDelta tau hTauProper hTauOne hTauStable hOffPair
  have hAlphaEdge : ∀ f, tau f = some alpha ↔ sigma f = some alpha :=
    hOffPair alpha hAlphaGamma hAlphaDelta
  have hBetaEdge : ∀ f, tau f = some beta ↔ sigma f = some beta :=
    hOffPair beta hBetaGamma hBetaDelta
  have hGraph : TwoColorIncidenceGraph G tau alpha beta =
      TwoColorIncidenceGraph G sigma alpha beta := by
    ext x y
    cases x <;> cases y <;>
      simp [TwoColorIncidenceGraph, hAlphaEdge, hBetaEdge]
  have hComponents (z : Sum V E) :
      TwoColorComponent G tau alpha beta z =
        TwoColorComponent G sigma alpha beta z := by
    unfold TwoColorComponent
    rw [hGraph]
  have hPaths (z : Sum V E) :
      TwoColorPathComponent G tau alpha beta z ↔
        TwoColorPathComponent G sigma alpha beta z := by
    simp only [TwoColorPathComponent]
    rw [hComponents z, hGraph]
  have hMissingVertex (c : Fin k) (hcGamma : c ≠ chosenGamma)
      (hcDelta : c ≠ choice.color) (v : V) :
      c ∈ MissingColors G tau v ↔ c ∈ MissingColors G sigma v := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    simp_rw [hOffPair c hcGamma hcDelta]
  have hTreeMissing (c : Fin k) (hcGamma : c ≠ chosenGamma)
      (hcDelta : c ≠ choice.color) :
      c ∈ TreeMissingColors tau
          (ett.series.data.tree terminal.castSucc) ↔
        c ∈ TreeMissingColors sigma
          (ett.series.data.tree terminal.castSucc) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor
    · rintro ⟨v, hv, hc⟩
      exact ⟨v, hv, (hMissingVertex c hcGamma hcDelta v).mp hc⟩
    · rintro ⟨v, hv, hc⟩
      exact ⟨v, hv, (hMissingVertex c hcGamma hcDelta v).mpr hc⟩
  have hAlphaTau : alpha ∈ TreeMissingColors tau
      (ett.series.data.tree terminal.castSucc) :=
    (hTreeMissing alpha hAlphaGamma hAlphaDelta).mpr hAlphaMissing
  have hBetaTau : beta ∈ TreeMissingColors tau
      (ett.series.data.tree terminal.castSucc) :=
    (hTreeMissing beta hBetaGamma hBetaDelta).mpr hBetaMissing
  have hTauInterchangeable := @helper_hTauInterchangeable_319 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T phi ett ctx hMP hpositive sigma alpha beta
      chosenGamma choice hTauProper hTauOne hTauStable hAlphaTau
  intro z w hz hw hzTree hwTree
  have hzTau : TwoColorPathComponent G tau alpha beta z :=
    (hPaths z).mpr hz
  have hwTau : TwoColorPathComponent G tau alpha beta w :=
    (hPaths w).mpr hw
  have hzTreeTau : ∃ v ∈ TreeSequenceVertexSet
      (ett.series.data.tree terminal.castSucc),
      Sum.inl v ∈ TwoColorComponent G tau alpha beta z := by
    rcases hzTree with ⟨v, hv, hvz⟩
    exact ⟨v, hv, by simpa only [hComponents z] using hvz⟩
  have hwTreeTau : ∃ v ∈ TreeSequenceVertexSet
      (ett.series.data.tree terminal.castSucc),
      Sum.inl v ∈ TwoColorComponent G tau alpha beta w := by
    rcases hwTree with ⟨v, hv, hvw⟩
    exact ⟨v, hv, by simpa only [hComponents w] using hvw⟩
  have hinter := hTauInterchangeable z w hzTau hwTau hzTreeTau hwTreeTau
  rw [hComponents z, hComponents w] at hinter
  exact hinter

private theorem helper_branch_113.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (_ : TechnicalInductionContext G k e0 ett.rounds) (_ : MaximumProperty ett)
        (hpositive : (0 : ℕ) < ett.rounds) (_ : ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE) (sigma : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G
        sigma) (_ : IsOneEdgeUncolored sigma e0) (support : V) (gamma delta : Fin k) (_ :
        ett.series.data.chosenVertex (Fin.last ett.rounds) = some support) (_ :
        ett.series.data.gamma (Fin.last ett.rounds) = some gamma) (_ : ett.series.data.delta
        (Fin.last ett.rounds) = some delta) (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors
        sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : beta ∈ TreeMissingColors
        sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : alpha ≠ gamma) (_ :
        alpha ≠ delta) (_ : beta ≠ gamma) (_ : beta ≠ delta),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬ett.rounds - (1 : ℕ) < ett.rounds) =>
    by
            omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : previous.succ = terminal) (_ : StableColoring (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data terminal) (ett.series.data.coloring terminal)
        sigma) (ci : Fin ett.rounds) (_ : IsProperEdgeColoring G (ett.series.data.coloring
        ci.castSucc)) (_ : IsOneEdgeUncolored (ett.series.data.coloring ci.castSucc) e0) (_ :
        ColoredVertexSetClosed G (ett.series.data.coloring ci.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree ci.succ.castSucc))) (_ : ¬ColoredVertexSetStronglyClosed G
        (ett.series.data.coloring ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        ci.succ.castSucc))) (_ : ¬Nonempty (RevisitingExtensionCertificate ett.series.data
        ci.castSucc)) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        ci.succ.castSucc) (TashkinovStoredColors ett.series.data ci.castSucc)
        (ett.series.data.coloring ci.castSucc)) (_ : (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data ci.castSucc)) choice.selected rho ∧ ¬Disjoint
        (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (ett.series.data.tree
        ci.succ.castSucc)))) (chosenGamma : Fin k) (_ : ParallelExtensionColor ett.series.data
        ci.castSucc choice.selected choice.vertex chosenGamma) (secondStable : PartialEdgeColoring
        E k) (_ : StableColoring (ett.series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data ci.castSucc)) choice.selected secondStable) (_ :
        TreeExit (ett.series.data.tree ci.succ.castSucc) secondStable chosenGamma choice.color
        choice.vertex) (_ : ett.series.data.coloring ci.succ = TwoColorComponentSwap G
        secondStable chosenGamma choice.color (Sum.inl choice.vertex)) (_ : IsProperEdgeColoring G
        (ett.series.data.coloring ci.succ)) (_ : IsOneEdgeUncolored (ett.series.data.coloring
        ci.succ) e0) (_ : ett.series.data.stored ci.succ = { choice.color, chosenGamma }) (_ :
        ett.series.data.connectingEdges ci.succ = { choice.edge }) (_ : ett.series.data.kind
        ci.succ = some TashkinovExtensionKind.PE) (_ : ett.series.data.chosenVertex ci.succ = some
        choice.vertex) (_ : ett.series.data.outsideVertex ci.succ = some choice.otherEndpoint) (_
        : ett.series.data.delta ci.succ = some choice.color) (_ : ett.series.data.gamma ci.succ =
        some chosenGamma) (_ : TashkinovClosure (ett.series.data.coloring ci.succ)
        (ett.series.data.tree ci.succ.castSucc) (ett.series.data.tree ci.succ.succ)) (_ :
        TreeSequenceInitialSegment (ett.series.data.tree ci.succ.castSucc) (ett.series.data.tree
        ci.succ.succ)) (_ : (ett.series.data.tree ci.succ.castSucc).length < (ett.series.data.tree
        ci.succ.succ).length) (_ : terminal = ci.succ), TreeInterchangeable G
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) sigma alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive hPE sigma hproper hone support gamma
      delta hsupport hgamma hdelta alpha beta hAlphaMissing hBetaMissing hAlphaGamma hAlphaDelta
      hBetaGamma hBetaDelta terminal previous hPreviousSucc hStableTerminal ci previousProper
      previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
      seriesAlternativeFails chosenGamma gammaRule secondStable secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension hslot
  have hci : ci = previous := by
    apply Fin.ext
    have hs := congrArg Fin.val hslot
    simp [terminal, previous] at hs ⊢
    omega
  subst ci
  have hTerminalEq : terminal = previous.succ := hslot
  have hLastEq : Fin.last ett.rounds = previous.succ := by
    simpa only [terminal] using hTerminalEq
  have hSupportEq : support = choice.vertex := by
    apply Option.some.inj
    exact hsupport.symm.trans (by
      rw [hLastEq]
      exact currentVertex)
  have hGammaEq : gamma = chosenGamma := by
    apply Option.some.inj
    exact hgamma.symm.trans (by
      rw [hLastEq]
      exact currentGamma)
  have hDeltaEq : delta = choice.color := by
    apply Option.some.inj
    exact hdelta.symm.trans (by
      rw [hLastEq]
      exact currentDelta)
  subst support
  subst gamma
  subst delta
  have hSupportTree : choice.vertex ∈ TreeSequenceVertexSet
      (ett.series.data.tree terminal.castSucc) := by
    simpa [hTerminalEq] using choice.vertexDefective.1
  have hGammaSecond : chosenGamma ∈ MissingColors G secondStable
      choice.vertex := by
    rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
    exact gammaRule.1
  have hChoiceSecond : secondStable choice.edge = some choice.color := by
    have hfix := secondStableRelation.1 choice.edge
      ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), choice.edgeColor⟩
    exact hfix.trans choice.edgeColor
  have hGammaDelta : chosenGamma ≠ choice.color := by
    intro heq
    have hpresent : chosenGamma ∈ PresentColors G secondStable
        choice.vertex := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨choice.edge, choice.edgeIncident, heq ▸ hChoiceSecond⟩
    have hnot : chosenGamma ∉ PresentColors G secondStable
        choice.vertex := by
      simpa [MissingColors] using hGammaSecond
    exact hnot hpresent
  have hComponent :
    ∀ w, w ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) → (Sum.inl w ∈
        TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex) ↔ w =
        choice.vertex) := by
    exact ctx.currentFour ett rfl hMP choice.vertex chosenGamma choice.color
      hPE hsupport hgamma hdelta sigma hproper hone hStableTerminal
  obtain ⟨selected, recoveredSecond, hselectedProper, hselectedOne,
      hselectedStable, hrecoveredSecondProper, hrecoveredSecondOne,
      hrecoveredSecondStable, hcurrentSwap, hundoneSecond,
      hundoneSelected, hundonePrevious⟩ :=
    ParallelExtensionUndoStable G k ett.rounds e0 input ett.series previous
      choice.vertex chosenGamma choice.color
      (by simpa only [hPreviousSucc] using hPE)
      (by simpa only [hPreviousSucc] using hsupport)
      (by simpa only [hPreviousSucc] using hgamma)
      (by simpa only [hPreviousSucc] using hdelta)
      sigma hproper hone
      (by simpa only [hPreviousSucc] using hStableTerminal)
      (by simpa only [hPreviousSucc] using hSupportTree)
      (by simpa only [hPreviousSucc] using hComponent)
  let tau := TwoColorComponentSwap G sigma chosenGamma choice.color
    (Sum.inl choice.vertex)
  have hTauProper : IsProperEdgeColoring G tau := by
    exact TwoColorComponentSwapProper G sigma chosenGamma choice.color
      hGammaDelta hproper (Sum.inl choice.vertex)
  have hTauOne := @helper_hTauOne_234 V E inferInstance inferInstance inferInstance G k e0 input T
      phi ett hpositive sigma hone chosenGamma choice hGammaDelta
  have hTauStable : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data previous.castSucc)
      (ett.series.data.coloring previous.castSucc) tau := by
    simpa [tau, hTerminalEq] using hundonePrevious
  have hOffPair (c : Fin k) (hcGamma : c ≠ chosenGamma)
      (hcDelta : c ≠ choice.color) (f : E) :
      tau f = some c ↔ sigma f = some c := by
    by_cases hf : Sum.inr f ∈
        TwoColorComponent G sigma chosenGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases hfg : sigma f = some chosenGamma
      · simp [tau, TwoColorComponentSwap, hf, hfg, hcGamma.symm,
          hcDelta.symm]
      · by_cases hfd : sigma f = some choice.color
        · simp [tau, TwoColorComponentSwap, hf, hfd, hcGamma.symm,
            hcDelta.symm, hGammaDelta.symm]
        · simp [tau, TwoColorComponentSwap, hf, hfg, hfd]
    · simp [tau, TwoColorComponentSwap, hf]
  exact @helper_continuation_387 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett ctx hMP hpositive sigma alpha beta hAlphaMissing hBetaMissing
      chosenGamma choice hAlphaGamma hBetaGamma hAlphaDelta hBetaDelta hTauProper hTauOne
      hTauStable hOffPair
theorem ParallelTerminalAwayInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (support : V) (gamma delta : Fin k)
    (hsupport : ett.series.data.chosenVertex (Fin.last ett.rounds) =
      some support)
    (hgamma : ett.series.data.gamma (Fin.last ett.rounds) = some gamma)
    (hdelta : ett.series.data.delta (Fin.last ett.rounds) = some delta) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    ∀ alpha beta : Fin k,
    alpha ∈ TreeMissingColors sigma Tn →
    beta ∈ TreeMissingColors sigma Tn →
    alpha ≠ gamma →
    alpha ≠ delta →
    beta ≠ gamma →
    beta ≠ delta →
    TreeInterchangeable G Tn sigma alpha beta := by
  classical
  dsimp only
  intro alpha beta hAlphaMissing hBetaMissing hAlphaGamma hAlphaDelta
    hBetaGamma hBetaDelta
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let previous : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hPreviousSucc : previous.succ = terminal := by
    apply Fin.ext
    simp [previous, terminal]
    omega
  have hStableTerminal : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data terminal)
      (ett.series.data.coloring terminal) sigma := by
    rw [← ett.generatingColoring]
    exact hstable
  have cert := ett.series.certified terminal
  generalize hslot : terminal = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hz := congrArg Fin.val hslot
    simp [terminal] at hz
    omega
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hterm := hPE
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hterm := hPE
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      chosenGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_113 V E inferInstance inferInstance inferInstance inferInstance G
              k e0 input T phi ett ctx hMP hpositive hPE sigma hproper hone support gamma delta
              hsupport hgamma hdelta alpha beta hAlphaMissing hBetaMissing hAlphaGamma
              hAlphaDelta hBetaGamma hBetaDelta hPreviousSucc hStableTerminal ci previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
              seriesAlternativeFails chosenGamma gammaRule secondStable secondStableRelation
              exitWitness currentColoring currentProper currentOneUncolored currentStored
              currentEdges currentKind currentVertex currentOutside currentDelta currentGamma
              closedExtension orderedExtension strictExtension hslot
end GoldbergSeymour

end
