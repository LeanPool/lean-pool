/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTreeFacts

public import LeanPool.GoldbergSeymour.SharedFacts.Basic2TerminalPE

public import LeanPool.GoldbergSeymour.ExtensionBase

public import LeanPool.GoldbergSeymour.ParallelExtensionUndoStable

/-!
# Basic2Terminal PE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hdeltaCurrentMissing_266.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G
        secondStable) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)) (_ : ett.series.data.coloring previous.succ
        = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)) (_ :
        terminal = previous.succ) (_ : gamma ∈ MissingColors G secondStable choice.vertex) (_ :
        secondStable choice.edge = some choice.color) (_ : gamma ≠ choice.color) (_ : Sum.inr
        choice.edge ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex)), choice.color ∈ MissingColors G (ett.series.data.coloring terminal)
        choice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive terminal previous gamma secondStable
      secondStableProper choice currentColoring hterminalEq hgammaSecond hchoiceSecond
      hgammaDeltaNe hchoiceSecondComponent
  rw [hterminalEq, MissingColors]
  simp only [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hpresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hpresent
  rcases hpresent with ⟨f, hfIncident, hfCurrent⟩
  rw [currentColoring] at hfCurrent
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex)
  · by_cases hfg : secondStable f = some gamma
    · have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨f, hfIncident, hfg⟩
      have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hgammaSecond
      exact hnot hp
    · by_cases hfd : secondStable f = some choice.color
      · have heq : choice.color = gamma := by
          simpa [TwoColorComponentSwap, hfComponent, hfg, hfd,
            hgammaDeltaNe] using hfCurrent
        exact hgammaDeltaNe heq.symm
      · simp [TwoColorComponentSwap, hfComponent, hfg, hfd] at hfCurrent
  · have hfd : secondStable f = some choice.color := by
      simpa [TwoColorComponentSwap, hfComponent] using hfCurrent
    by_cases hfeq : f = choice.edge
    · subst f
      exact hfComponent hchoiceSecondComponent
    · exact (secondStableProper hfeq
        ⟨choice.vertex, hfIncident, choice.edgeIncident⟩
        hfd hchoiceSecond).elim

private theorem helper_hrecoveredOne_399.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : IsOneEdgeUncolored sigma e0),
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)) (_ : gamma ≠ choice.color),
    let recovered : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex); IsOneEdgeUncolored recovered e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hone previous gamma choice
      hgammaDeltaNe recovered
  unfold IsOneEdgeUncolored
  constructor
  · by_cases he : Sum.inr e0 ∈
        TwoColorComponent G sigma gamma choice.color
          (Sum.inl choice.vertex)
    · simp [recovered, TwoColorComponentSwap, he, hone.1]
    · simp [recovered, TwoColorComponentSwap, he, hone.1]
  · intro e he0
    obtain ⟨c, hc⟩ := hone.2 e he0
    by_cases he : Sum.inr e ∈
        TwoColorComponent G sigma gamma choice.color
          (Sum.inl choice.vertex)
    · by_cases hcg : c = gamma
      · exact ⟨choice.color, by
          simp [recovered, TwoColorComponentSwap, he, hc, hcg]⟩
      · by_cases hcd : c = choice.color
        · exact ⟨gamma, by
            simp [recovered, TwoColorComponentSwap, he, hc, hcd,
              hgammaDeltaNe.symm]⟩
        · exact ⟨c, by
            simp [recovered, TwoColorComponentSwap, he, hc, hcg, hcd]⟩
    · exact ⟨c, by
        simp [recovered, TwoColorComponentSwap, he, hc]⟩

private theorem helper_targetEdgeOutside_444.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (delta : Fin k),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)) (_ : choice.color ∈ MissingColors G sigma
        choice.vertex) (_ : delta ≠ gamma) (_ : (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), Sum.inl x ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔ x = choice.vertex))
        (_ : (
    ∀ (f : E) (_ : Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl
        choice.vertex)), sigma f = some gamma ∨ sigma f = some choice.color)) (f : E),
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), Incident G x f → sigma f
        = some delta → Sum.inr f ∉ TwoColorComponent G sigma gamma choice.color (Sum.inl
        choice.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma delta terminal previous gamma
      choice hdeltaSigmaMissing hdeltaGammaNe hcomponent hcomponentEdgeColor f x hx hxf hfd
      hfComponent
  rcases hcomponentEdgeColor f hfComponent with hfg | hfc
  · apply hdeltaGammaNe
    exact Option.some.inj (hfd.symm.trans hfg)
  · have hxComponent : Sum.inl x ∈
        TwoColorComponent G sigma gamma choice.color
          (Sum.inl choice.vertex) := by
      change (TwoColorIncidenceGraph G sigma gamma choice.color).connectedComponentMk
          (Sum.inl x) =
        (TwoColorIncidenceGraph G sigma gamma choice.color).connectedComponentMk
          (Sum.inl choice.vertex)
      calc
        _ = (TwoColorIncidenceGraph G sigma gamma choice.color).connectedComponentMk
            (Sum.inr f) := by
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          simp [TwoColorIncidenceGraph, hxf, hfc]
        _ = _ := hfComponent
    have hxEq : x = choice.vertex := (hcomponent x hx).mp hxComponent
    have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
      simpa [MissingColors] using hdeltaSigmaMissing
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨f, by simpa [hxEq] using hxf, hfc⟩

private theorem helper_hstableR_473.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (sigma : PartialEdgeColoring E k) (v : V) (_ : v ∈ TreeSequenceVertexSet T) (_ : Fin
        ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)),
    let recovered : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex);
    ∀ (_ : StableColoring (ett.series.data.tree terminal.castSucc) (TashkinovStoredColors
        ett.series.data previous.castSucc) (ett.series.data.coloring previous.castSucc)
        recovered),
    let r : ℕ := ett.rounds - (1 : ℕ);
    ∀ (hrBefore : r < ett.rounds) (_ : TreeSequenceInitialSegment (ett.series.data.tree (⟨r,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree terminal.castSucc)) (lower :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨r + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨r,
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : lower.rounds = r), StableColoring
        (ett.series.data.tree (⟨r,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc) recovered := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive this sigma v hvFinal q terminal
      previous gamma choice recovered hrecoveredStable r hrBefore hRTerminal lower hr
  constructor
  · intro f hf hcontrol
    apply hrecoveredStable.1 f
    · rcases hf with ⟨x, hx, hxf⟩
      exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset
        hRTerminal hx, hxf⟩
    · rcases hcontrol with ⟨c, hc, hcf⟩
      refine ⟨c, ?_, hcf⟩
      rcases Finset.mem_union.mp hc with hc | hc
      · apply Finset.mem_union.mpr
        left
        simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
        rcases hc with ⟨x, hx, hxc⟩
        exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset
          hRTerminal hx, hxc⟩
      · exact Finset.mem_union.mpr (Or.inr hc)
  · intro x hx
    exact hrecoveredStable.2 x
      (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hx)

private theorem helper_continuation_618.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G
        k e0 ett.rounds → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ (u w : V), TreeVertexOrder A u w → TreeVertexOrder B u w) →
    ∀ (sigma : PartialEdgeColoring E k) (delta : Fin k) (v : V) (_ : v ∈ TreeSequenceVertexSet T)
        (q : Fin ett.rounds) (vi : V), ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE ∨ ett.series.data.kind q.succ = some TashkinovExtensionKind.SE →
        ett.series.data.chosenVertex q.succ = some vi → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    ∀ (w : V), ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc =
        ett.series.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree ((⟨ett.rounds -
        (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ.castSucc) (TashkinovStoredColors ett.series.data
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (ett.series.data.coloring ((⟨ett.rounds - (1 :
        ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc)), IsProperEdgeColoring G
        (TwoColorComponentSwap G sigma gamma choice.color (Sum.inl choice.vertex) :
        PartialEdgeColoring E k) → IsOneEdgeUncolored (TwoColorComponentSwap G sigma gamma
        choice.color (Sum.inl choice.vertex) : PartialEdgeColoring E k) e0 → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc)
        (TashkinovStoredColors ett.series.data ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (ett.series.data.coloring ((⟨ett.rounds - (1 :
        ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (TwoColorComponentSwap G sigma gamma
        choice.color (Sum.inl choice.vertex) : PartialEdgeColoring E k) →
    ∀ (hqBefore : (↑q : ℕ) + (1 : ℕ) < ett.rounds), (1 : ℕ) ≤ (ett.rounds - (1 : ℕ) : ℕ) →
    ∀ (hrBefore : (ett.rounds - (1 : ℕ) : ℕ) < ett.rounds), v ∈ TreeSequenceVertexSet
        (ett.series.data.tree (⟨(↑q : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) → TreeSequenceInitialSegment (ett.series.data.tree
        (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds
        + (1 : ℕ))).castSucc) → TreeVertexOrder (ett.series.data.tree (⟨(ett.rounds - (1 : ℕ) :
        ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) w v → DefectiveColor G (TwoColorComponentSwap G sigma gamma
        choice.color (Sum.inl choice.vertex) : PartialEdgeColoring E k) (TreeSequenceVertexSet
        (ett.series.data.tree (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) delta → BoundaryColorVertex G (TwoColorComponentSwap G sigma
        gamma choice.color (Sum.inl choice.vertex) : PartialEdgeColoring E k)
        (TreeSequenceVertexSet (ett.series.data.tree (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) delta v → BoundaryColorVertex G (TwoColorComponentSwap G
        sigma gamma choice.color (Sum.inl choice.vertex) : PartialEdgeColoring E k)
        (TreeSequenceVertexSet (ett.series.data.tree (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) delta w →
    ∀ (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨(ett.rounds - (1 : ℕ) :
        ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(ett.rounds - (1 : ℕ) : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : lower.rounds = (ett.rounds - (1 : ℕ) : ℕ)),
        MaximumProperty lower → (
    ∀ (i : Fin (lower.rounds + (2 : ℕ))), lower.series.data.tree i = ett.series.data.tree
        (Fin.castLE (
    by omega
    ) i)) → (
    ∀ (i : Fin (lower.rounds + (1 : ℕ))), lower.series.data.coloring i = ett.series.data.coloring
        (Fin.castLE (
    by omega
    ) i) ∧ lower.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by omega
    ) i) ∧ lower.series.data.connectingEdges i = ett.series.data.connectingEdges (Fin.castLE (
    by omega
    ) i) ∧ lower.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by omega
    ) i) ∧ lower.series.data.chosenVertex i = ett.series.data.chosenVertex (Fin.castLE (
    by omega
    ) i) ∧ lower.series.data.outsideVertex i = ett.series.data.outsideVertex (Fin.castLE (
    by omega
    ) i) ∧ lower.series.data.delta i = ett.series.data.delta (Fin.castLE (
    by omega
    ) i) ∧ lower.series.data.gamma i = ett.series.data.gamma (Fin.castLE (
    by omega
    ) i) ∧ TashkinovStoredColors lower.series.data i = TashkinovStoredColors ett.series.data
        (Fin.castLE (
    by omega
    ) i) ∧ lower.series.certified i ≍ ett.series.certified (Fin.castLE (
    by omega
    ) i)) → Fin.castLE (Decidable.byContradiction fun (a : ¬lower.rounds + (1 : ℕ) ≤ ett.rounds +
        (1 : ℕ)) ↦
    by omega
    ) (Fin.last lower.rounds : Fin (lower.rounds + (1 : ℕ))) = ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc → Fin.castLE (Decidable.byContradiction fun (a
        : ¬lower.rounds + (1 : ℕ) + (1 : ℕ) ≤ ett.rounds + (1 : ℕ) + (1 : ℕ)) ↦
    by omega
    ) (Fin.last lower.rounds : Fin (lower.rounds + (1 : ℕ))).castSucc = ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc.castSucc → v = vi ∨ TreeVertexOrder T v vi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hlower orderTransfer sigma delta v hvFinal
      q vi hkind hchosen hvN w
  set terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds
  set previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ :
                        Fin ett.rounds)
  intro htreeTerminal gamma choice
  set recovered : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
      (Sum.inl choice.vertex)
  intro hrecoveredProper hrecoveredOne hrecoveredStable hqBefore
  set r : ℕ := ett.rounds - (1 : ℕ)
  intro hrPositive hrBefore hvAtQ hRTerminal hwvR hdefectiveR hvBoundaryR hwBoundaryR lower hr
      hmaxLower htree hdata
  set nLower : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds
  intro hnCast hnTreeCast
  have hrTree : ett.series.data.tree ⟨r, by omega⟩ =
      ett.series.data.tree previous.castSucc.castSucc := by
    apply congrArg ett.series.data.tree
    apply Fin.ext
    simp [previous, r]
  have hdisplay : ett.series.data.tree ⟨r + 1, by omega⟩ =
      ett.series.data.tree terminal.castSucc := by
    congr 1
    apply Fin.ext
    simp [r, terminal]
    omega
  have hvLower : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r + 1, by omega⟩) := by
    rw [hdisplay]
    exact hvN
  rcases hdata nLower with
    ⟨hnColor, hnRawStored, hnEdges, hnKind, hnVertex, hnOutside,
      hnDelta, hnGamma, hnStored, hnCert⟩
  have hnColor' : lower.series.data.coloring nLower =
      ett.series.data.coloring previous.castSucc := by
    rw [hnColor, hnCast]
  have hnStored' : TashkinovStoredColors lower.series.data nLower =
      TashkinovStoredColors ett.series.data previous.castSucc := by
    rw [hnStored, hnCast]
  have hnTree' : lower.series.data.tree nLower.castSucc =
      ett.series.data.tree ⟨r, by omega⟩ := by
    rw [htree nLower.castSucc, hnTreeCast, ← hrTree]
  have hstableR :=
    @helper_hstableR_473 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett hpositive sigma v hvFinal q gamma choice hrecoveredStable hrBefore
        hRTerminal lower hr
  have hstableLower : StableColoring
      (lower.series.data.tree nLower.castSucc)
      (TashkinovStoredColors lower.series.data nLower)
      (lower.series.data.coloring nLower) recovered := by
    rw [hnTree', hnStored', hnColor']
    exact hstableR
  let qLower : Fin lower.rounds := ⟨q.val, by omega⟩
  have hqCast : Fin.castLE (by omega) qLower.succ = q.succ := by
    apply Fin.ext
    rfl
  rcases hdata qLower.succ with
    ⟨_, _, _, hqKind, hqVertex, _, _, _, _, _⟩
  have hkindLower : lower.series.data.kind qLower.succ =
        some TashkinovExtensionKind.PE ∨
      lower.series.data.kind qLower.succ =
        some TashkinovExtensionKind.SE := by
    rw [hqKind, hqCast]
    exact hkind
  have hchosenLower : lower.series.data.chosenVertex qLower.succ =
      some vi := by
    rw [hqVertex, hqCast]
    exact hchosen
  have hfirstLower : ETTFirstAppearanceIndex lower v hvLower ≤ qLower.val + 1 := by
    apply ETTFirstAppearanceIndex.le_of_series_mem lower v hvLower qLower
    have castEqual : Fin.castLE (by omega) qLower.succ.castSucc =
        (⟨q.val + 1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      rfl
    rw [htree qLower.succ.castSucc, castEqual]
    exact hvAtQ
  have hdefectiveLower : DefectiveColor G recovered
      (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
      delta := by
    rw [hnTree']
    exact hdefectiveR
  have hvBoundaryLower : BoundaryColorVertex G recovered
      (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
      delta v := by
    rw [hnTree']
    exact hvBoundaryR
  have hwBoundaryLower : BoundaryColorVertex G recovered
      (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
      delta w := by
    rw [hnTree']
    exact hwBoundaryR
  have hwvLower : TreeVertexOrder
      (lower.series.data.tree nLower.castSucc) w v := by
    rw [hnTree']
    exact hwvR
  have hlowerFive :=
    (hlower lower (by omega) (by omega) hmaxLower).2.2.2.2.1
  have hresult := hlowerFive recovered hrecoveredProper hrecoveredOne
    hstableLower delta hdefectiveLower v hvBoundaryLower
    ⟨w, hwBoundaryLower, hwvLower⟩ hvLower qLower vi hkindLower
    hchosenLower hfirstLower
  rcases hresult with heq | horder
  · exact Or.inl heq
  · apply Or.inr
    have hdisplayToT : TreeSequenceInitialSegment
        (ett.series.data.tree ⟨r + 1, by omega⟩) T := by
      rw [hdisplay]
      rw [htreeTerminal]
      exact ett.abovePenultimate
    exact orderTransfer hdisplayToT v vi horder

private theorem helper_branch_567.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (_ : (
    ∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))))) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (u w : V) (_ :
        TreeVertexOrder A u w), TreeVertexOrder B u w)) (sigma : PartialEdgeColoring E k) (delta :
        Fin k) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (vi : V) (_ :
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨ ett.series.data.kind q.succ
        = some TashkinovExtensionKind.SE) (_ : ett.series.data.chosenVertex q.succ = some vi) (_ :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (_ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (a : E) (_ : Incident G v a) (w :
        V) (_ : TreeVertexOrder (ett.series.data.tree (Fin.last ett.rounds).castSucc) w v) (b : E)
        (_ : Incident G w b),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : ett.series.data.tree terminal.castSucc = ett.series.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (gamma : Fin k) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)),
    let recovered : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex);
    ∀ (_ : IsProperEdgeColoring G recovered) (_ : IsOneEdgeUncolored recovered e0) (_ :
        StableColoring (ett.series.data.tree terminal.castSucc) (TashkinovStoredColors
        ett.series.data previous.castSucc) (ett.series.data.coloring previous.castSucc) recovered)
        (_ : recovered a = some delta) (_ : recovered b = some delta),
    ∀ za ∉ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), G.ends a = s(v, za) →
    ∀ zb ∉ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), G.ends b = s(w, zb) → a
        ≠ b → ¬q.succ = terminal → v = vi ∨ TreeVertexOrder T v vi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower this stageToStage orderTransfer
      sigma delta v hvFinal q vi hkind hchosen hfirstBound hvN a hva w hwv b hwb terminal previous
      htreeTerminal gamma choice recovered hrecoveredProper hrecoveredOne hrecoveredStable
      haRecoveredValue hbRecoveredValue za hzaOutside haEnds zb hzbOutside hbEnds hab hqTerminal
  have hqBefore : q.val + 1 < ett.rounds := by
    have hle : q.val + 1 ≤ ett.rounds := by omega
    have hne : q.val + 1 ≠ ett.rounds := by
      intro heq
      apply hqTerminal
      apply Fin.ext
      simpa [terminal] using heq
    omega
  have appearanceInStage :=
    @SharedFacts.Basic2TerminalPE.appearanceInStage V E inferInstance inferInstance
        inferInstance G k e0
        input T generating ett stageToStage v hvFinal q
  let r := ett.rounds - 1
  have hrPositive : 1 ≤ r := by
    dsimp [r]
    omega
  have hrBefore : r < ett.rounds := by
    dsimp [r]
    omega
  have hfirstToR : ETTFirstAppearanceIndex ett v hvFinal ≤ r := by
    dsimp [r]
    omega
  have hvR : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r, by omega⟩) :=
    appearanceInStage v hvFinal r hrPositive (by dsimp [r]; omega)
      hfirstToR
  have hvAtQ : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨q.val + 1, by omega⟩) :=
    appearanceInStage v hvFinal (q.val + 1) (by omega) (by omega)
      hfirstBound
  have hRTerminal : TreeSequenceInitialSegment
      (ett.series.data.tree ⟨r, by omega⟩)
      (ett.series.data.tree terminal.castSucc) := by
    rw [htreeTerminal]
    exact stageToStage r ett.rounds hrPositive (by dsimp [r]; omega)
      le_rfl
  have earlierInPrefix :=
    @SharedFacts.Basic2TerminalPE.earlierInPrefix V E inferInstance inferInstance
        inferInstance G k e0 input
        T generating ett v hvFinal q
  obtain ⟨hwR, hwvR⟩ := earlierInPrefix w v hRTerminal hvR hwv
  have hzaR : za ∉ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r, by omega⟩) := by
    intro hza
    exact hzaOutside
      (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hza)
  have hzbR : zb ∉ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r, by omega⟩) := by
    intro hzb
    exact hzbOutside
      (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hzb)
  have haR : a ∈ BoundaryColorEdges G recovered
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    refine ⟨?_, haRecoveredValue⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨v, hvR, za, hzaR, haEnds⟩
  have hbR : b ∈ BoundaryColorEdges G recovered
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    refine ⟨?_, hbRecoveredValue⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨w, hwR, zb, hzbR, hbEnds⟩
  have hdefectiveR : DefectiveColor G recovered
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta := by
    unfold DefectiveColor
    have hc : 1 < (BoundaryColorEdges G recovered
        (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
        delta).card := Finset.one_lt_card.mpr
          ⟨a, haR, b, hbR, hab⟩
    omega
  have hvBoundaryR : BoundaryColorVertex G recovered
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta v := ⟨hvR, a, haR, hva⟩
  have hwBoundaryR : BoundaryColorVertex G recovered
      (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
      delta w := ⟨hwR, b, hbR, hwb⟩
  obtain ⟨lower, hr, hmaxLower, htree, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP r
      hrPositive hrBefore
  let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
  have hnCast : Fin.castLE (by omega) nLower = previous.castSucc := by
    apply Fin.ext
    simp [nLower, hr, previous, r]
  have hnTreeCast : Fin.castLE (by omega) nLower.castSucc =
      previous.castSucc.castSucc := by
    apply Fin.ext
    simp [nLower, hr, previous, r]
  exact @helper_continuation_618 V E inferInstance inferInstance  inferInstance G k
      e0 input T generating ett hpositive hlower orderTransfer sigma delta v hvFinal q vi hkind
      hchosen hvN w htreeTerminal gamma choice hrecoveredProper hrecoveredOne hrecoveredStable
      hqBefore hrPositive hrBefore hvAtQ hRTerminal hwvR hdefectiveR hvBoundaryR hwBoundaryR
      lower hr hmaxLower htree hdata hnCast hnTreeCast
private theorem helper_hgammaControl_803.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds),
    ∀ v ∈ TreeSequenceVertexSet T,
    ∀ (_ : Fin ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)), ett.series.data.stored previous.succ =
        { choice.color, gamma } → terminal = previous.succ → gamma ∈ TreeMissingColors
        (ett.series.data.coloring terminal) (ett.series.data.tree terminal.castSucc) ∪
        TashkinovStoredColors ett.series.data terminal := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v hvFinal q terminal previous gamma
      choice currentStored hterminalEq
  by_cases hm : gamma ∈
      TreeMissingColors (ett.series.data.coloring terminal)
        (ett.series.data.tree terminal.castSucc)
  · exact Finset.mem_union_left _ hm
  · apply Finset.mem_union_right
    rw [TashkinovStoredColors]
    simp only [show terminal.val ≠ 0 by simp [terminal]; omega,
      ite_false, Finset.mem_sdiff]
    refine ⟨?_, hm⟩
    simp only [Finset.mem_biUnion]
    refine ⟨terminal, Finset.mem_univ _, ?_⟩
    rw [hterminalEq, currentStored]
    simp

private theorem helper_hgammaBoundarySigma_844.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)) (_ : gamma ∈ TreeMissingColors
        (ett.series.data.coloring terminal) (ett.series.data.tree terminal.castSucc) ∪
        TashkinovStoredColors ett.series.data terminal) (_ : (
    ∀ (f : E) (_ : TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f) (_ : ((
    ∃ c ∈ TreeMissingColors (ett.series.data.coloring terminal) (ett.series.data.tree
        terminal.castSucc) ∪ TashkinovStoredColors ett.series.data terminal,
        ett.series.data.coloring terminal f = some c) ∨
    ∃ c ∈ TreeMissingColors (ett.series.data.coloring terminal) (ett.series.data.tree
        terminal.castSucc) ∪ TashkinovStoredColors ett.series.data terminal, sigma f = some c)),
        sigma f = ett.series.data.coloring terminal f)) (_ : (
    ∀ {f : E} (_ : f ∈ BoundaryEdges G (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc))), TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f)) (_ :
        BoundaryColorEdges G (ett.series.data.coloring terminal) (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) gamma = { choice.edge }), BoundaryColorEdges G
        sigma (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) gamma =
        { choice.edge } := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma terminal previous gamma choice
      hgammaControl hfixBoth boundaryIncident hgammaBoundaryCurrent
  rw [← hgammaBoundaryCurrent]
  apply Finset.ext
  intro f
  simp only [BoundaryColorEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hfBoundary, hfSigma⟩
    refine ⟨hfBoundary, ?_⟩
    have hfix := hfixBoth f (boundaryIncident hfBoundary)
      (Or.inr ⟨gamma, hgammaControl, hfSigma⟩)
    exact hfix.symm.trans hfSigma
  · rintro ⟨hfBoundary, hfCurrent⟩
    refine ⟨hfBoundary, ?_⟩
    have hfix := hfixBoth f (boundaryIncident hfBoundary)
      (Or.inl ⟨gamma, hgammaControl, hfCurrent⟩)
    exact hfix.trans hfCurrent

private theorem helper_branch_1001.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (u w : V) (_ :
        TreeVertexOrder A u w), TreeVertexOrder B u w)) (sigma : PartialEdgeColoring E k) (delta :
        Fin k) (v : V) (q : Fin ett.rounds) (vi : V) (_ : ett.series.data.chosenVertex q.succ =
        some vi) (_ : v ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) (a : E) (_ : Incident G v a),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : previous.succ = terminal) (_ : ett.series.data.tree terminal.castSucc =
        ett.series.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (gamma : Fin k) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)) (_ :
        ett.series.data.chosenVertex previous.succ = some choice.vertex),
    let recovered : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex);
    ∀ (_ : IsProperEdgeColoring G recovered) (_ : IsOneEdgeUncolored recovered e0) (_ :
        StableColoring (ett.series.data.tree terminal.castSucc) (TashkinovStoredColors
        ett.series.data previous.castSucc) (ett.series.data.coloring previous.castSucc) recovered)
        (_ : a ∈ BoundaryColorEdges G recovered (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc)) delta) (_ : DefectiveColor G recovered (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) delta) (_ : q.succ = terminal), v = vi ∨
        TreeVertexOrder T v vi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive orderTransfer sigma delta v q vi
      hchosen hvN a hva terminal previous hpreviousSucc htreeTerminal gamma choice currentVertex
      recovered hrecoveredProper hrecoveredOne hrecoveredStable haRecovered hdefectiveRecovered
      hqTerminal
  have hchoice : choice.vertex = vi := by
    apply Option.some.inj
    exact currentVertex.symm.trans
      (by simpa [hqTerminal, hpreviousSucc] using hchosen)
  have hvDefective : DefectiveVertex G recovered
      (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) v :=
    ⟨hvN, a, ⟨delta, hdefectiveRecovered, haRecovered⟩, hva⟩
  have hmaximal := choice.maximal recovered v hrecoveredProper
    hrecoveredOne (by simpa [hpreviousSucc] using hrecoveredStable)
    (by simpa [hpreviousSucc] using hvDefective)
  rcases hmaximal with heq | horder
  · exact Or.inl (heq.trans hchoice)
  · apply Or.inr
    have hsegment : TreeSequenceInitialSegment
        (ett.series.data.tree terminal.castSucc) T := by
      rw [htreeTerminal]
      exact ett.abovePenultimate
    exact orderTransfer hsegment v vi
      (by simpa [hpreviousSucc, hchoice] using horder)

private theorem helper_continuation_1207.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (_ : (
    ∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))))) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (u w : V) (_ :
        TreeVertexOrder A u w), TreeVertexOrder B u w)) (sigma : PartialEdgeColoring E k) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (delta : Fin k) (v : V)
        (hvFinal : v ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (vi : V) (_ :
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨ ett.series.data.kind q.succ
        = some TashkinovExtensionKind.SE) (_ : ett.series.data.chosenVertex q.succ = some vi) (_ :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (_ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    ∀ a ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta, Incident G v a →
    ∀ (w : V), TreeVertexOrder (ett.series.data.tree (Fin.last ett.rounds).castSucc) w v → w ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    ∀ b ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta, Incident G w b →
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); previous.succ = terminal → ett.series.data.tree terminal.castSucc =
        ett.series.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)), ett.series.data.chosenVertex previous.succ
        = some choice.vertex → terminal = previous.succ → gamma ≠ choice.color → choice.color ∈
        MissingColors G sigma choice.vertex → delta ≠ gamma → (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), Sum.inl x ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔ x = choice.vertex)
        → StableColoring (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors
        ett.series.data previous.castSucc) (ett.series.data.coloring previous.castSucc)
        (TwoColorComponentSwap G sigma gamma choice.color (Sum.inl choice.vertex)) → v = vi ∨
        TreeVertexOrder T v vi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower
  let this : DecidableEq V :=
    Classical.decEq V
  intro stageToStage orderTransfer sigma hproper hone delta v hvFinal q vi hkind hchosen
      hfirstBound hvN a haColor hva w hwv hwN b hbColor hwb terminal previous hpreviousSucc
      htreeTerminal gamma choice currentVertex hterminalEq hgammaDeltaNe hdeltaSigmaMissing
      hdeltaGammaNe hcomponent hundonePrevious
  let recovered := TwoColorComponentSwap G sigma gamma choice.color
    (Sum.inl choice.vertex)
  have hrecoveredProper : IsProperEdgeColoring G recovered := by
    exact TwoColorComponentSwapProper G sigma gamma choice.color
      hgammaDeltaNe hproper (Sum.inl choice.vertex)
  have hrecoveredOne :=
    @helper_hrecoveredOne_399 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett hpositive sigma hone gamma choice hgammaDeltaNe
  have hrecoveredStable : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data previous.castSucc)
      (ett.series.data.coloring previous.castSucc) recovered := by
    simpa [recovered, hterminalEq] using hundonePrevious
  have hcomponentEdgeColor :=
    (fun (edge : E) member => TwoColorComponent.edge_colors
      (G := G) (phi := sigma) (alpha := gamma) (beta := choice.color)
      (vertex := choice.vertex) (edge := edge) member)
  have targetEdgeOutside :=
    @helper_targetEdgeOutside_444 V E inferInstance inferInstance inferInstance G k e0
        input T generating ett hpositive sigma delta gamma choice hdeltaSigmaMissing
        hdeltaGammaNe hcomponent hcomponentEdgeColor
  have haSigma : sigma a = some delta := (Finset.mem_filter.mp haColor).2
  have hbSigma : sigma b = some delta := (Finset.mem_filter.mp hbColor).2
  have haOutside := targetEdgeOutside a v hvN hva haSigma
  have hbOutside := targetEdgeOutside b w hwN hwb hbSigma
  have haRecoveredValue : recovered a = some delta := by
    simp [recovered, TwoColorComponentSwap, haOutside, haSigma]
  have hbRecoveredValue : recovered b = some delta := by
    simp [recovered, TwoColorComponentSwap, hbOutside, hbSigma]
  have haRecovered : a ∈ BoundaryColorEdges G recovered
      (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
      delta := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp haColor).1, haRecoveredValue⟩
  have hbRecovered : b ∈ BoundaryColorEdges G recovered
      (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
      delta := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hbColor).1, hbRecoveredValue⟩
  have boundaryEndpoint :=
    @SharedFacts.Basic2TerminalPE.boundaryEndpoint V E inferInstance inferInstance
        inferInstance G k e0 input
        T generating ett sigma delta
  obtain ⟨za, hzaOutside, haEnds⟩ :=
    boundaryEndpoint v hvN a haColor hva
  obtain ⟨zb, hzbOutside, hbEnds⟩ :=
    boundaryEndpoint w hwN b hbColor hwb
  have hwne : w ≠ v := by
    intro hwvEq
    rcases hwv with ⟨iw, iv, hiw, hiv, hlt⟩
    have hieq : iw = iv := by
      apply (ett.series.data.tree terminal.castSucc).vertex_injective
      exact hiw.trans (hiv.trans hwvEq.symm).symm
    omega
  have hab : a ≠ b := by
    intro habEq
    subst b
    have hwEnds : w = v ∨ w = za := by
      change w ∈ G.ends a at hwb
      rw [haEnds] at hwb
      simpa using hwb
    rcases hwEnds with hwvEq | hwza
    · exact hwne hwvEq
    · exact hzaOutside (hwza ▸ hwN)
  have hdefectiveRecovered : DefectiveColor G recovered
      (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
      delta := by
    unfold DefectiveColor
    have hc : 1 < (BoundaryColorEdges G recovered
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
        delta).card := Finset.one_lt_card.mpr
          ⟨a, haRecovered, b, hbRecovered, hab⟩
    omega
  have hvBoundaryRecovered : BoundaryColorVertex G recovered
      (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
      delta v := ⟨hvN, a, haRecovered, hva⟩
  have hwBoundaryRecovered : BoundaryColorVertex G recovered
      (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
      delta w := ⟨hwN, b, hbRecovered, hwb⟩
  by_cases hqTerminal : q.succ = terminal
  · exact @helper_branch_1001 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett hpositive orderTransfer sigma delta v q vi hchosen hvN a hva hpreviousSucc
      htreeTerminal gamma choice currentVertex hrecoveredProper hrecoveredOne hrecoveredStable
      haRecovered hdefectiveRecovered hqTerminal
  · exact @helper_branch_567 V E inferInstance inferInstance  inferInstance G k e0
      input T generating ett hMP hpositive hlower stageToStage orderTransfer sigma delta v
      hvFinal q vi hkind hchosen hfirstBound hvN a hva w hwv b hwb htreeTerminal gamma choice
      hrecoveredProper hrecoveredOne hrecoveredStable haRecoveredValue hbRecoveredValue za
      hzaOutside haEnds zb hzbOutside hbEnds hab hqTerminal

private theorem helper_hchoiceSecond_1447.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (_ : v ∈
        TreeSequenceVertexSet T) (_ : Fin ett.rounds),
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)), StableColoring
        (ett.series.data.tree previous.succ.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data previous.castSucc) : Finset (Fin k)) choice.selected secondStable →
        secondStable choice.edge = some choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v hvFinal q previous secondStable
      choice secondStableRelation
  have hfix := secondStableRelation.1 choice.edge
    ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
    ⟨choice.color, Finset.mem_union_right _
      (Finset.mem_insert_self _ _), choice.edgeColor⟩
  exact hfix.trans choice.edgeColor

private theorem helper_hgammaDeltaNe_1453.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (_ : v ∈
        TreeSequenceVertexSet T) (_ : Fin ett.rounds),
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)), gamma ∈ MissingColors G
        secondStable choice.vertex → secondStable choice.edge = some choice.color → gamma ≠
        choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v hvFinal q previous gamma secondStable
      choice hgammaSecond hchoiceSecond heq
  have hpresent : gamma ∈ PresentColors G secondStable choice.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨choice.edge, choice.edgeIncident, heq ▸ hchoiceSecond⟩
  have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
    simpa [MissingColors] using hgammaSecond
  exact hnot hpresent

private theorem helper_boundaryIncident_1485.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    ∀ {f : E},
    f ∈ BoundaryEdges G (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) →
    TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminal f hf
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at hf
  rcases hf with ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, by simp [Incident, hxy]⟩

private theorem helper_hdeltaGammaNe_1506.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (delta : Fin k), DefectiveColor G sigma (TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) delta →
    ∀ (v : V) (_ : v ∈ TreeSequenceVertexSet T) (_ : Fin ett.rounds),
    ∀ a ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta,
    ∀ b ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta,
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)), BoundaryColorEdges G sigma
        (TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc)) gamma =
        ({ choice.edge } : Finset E) → delta ≠ gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma delta hdefective v hvFinal q a
      haColor b hbColor previous gamma choice hgammaBoundarySigma heq
  subst delta
  unfold DefectiveColor at hdefective
  rw [hgammaBoundarySigma] at hdefective
  simp at hdefective

private theorem helper_hcomponent_1512.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma →
    ∀ (v : V) (_ : v ∈ TreeSequenceVertexSet T) (_ : Fin ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); previous.succ = terminal →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)), ett.series.data.kind previous.succ = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex previous.succ = some
        choice.vertex → ett.series.data.delta previous.succ = some choice.color →
        ett.series.data.gamma previous.succ = some gamma →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), Sum.inl x ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔ x = choice.vertex
  := by
  classical
  intro V E _ _ edgeDecidable G k e0 input T generating ett hMP hpositive hlower this sigma hproper
      hone hstable v hvFinal q terminal previous hpreviousSucc gamma choice currentKind
      currentVertex currentDelta currentGamma
  have hbase := @ExtensionBase V E _ _  edgeDecidable
    G k e0 input T generating ett hMP hpositive
    hlower choice.vertex gamma choice.color
    (by simpa only [← hpreviousSucc, terminal] using currentKind)
    (by simpa only [← hpreviousSucc, terminal] using currentVertex)
    (by simpa only [← hpreviousSucc, terminal] using currentGamma)
    (by simpa only [← hpreviousSucc, terminal] using currentDelta)
    sigma hproper hone hstable
  simpa [terminal] using hbase

private theorem helper_branch_195.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (_ : (
    ∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))))) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (u w : V) (_ :
        TreeVertexOrder A u w), TreeVertexOrder B u w)) (sigma : PartialEdgeColoring E k) (_ :
        IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0) (_ : StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring (Fin.last ett.rounds))
        sigma) (delta : Fin k) (_ : DefectiveColor G sigma (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) delta) (v : V) (hvFinal : v ∈
        TreeSequenceVertexSet T) (q : Fin ett.rounds) (vi : V) (_ : ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE ∨ ett.series.data.kind q.succ = some
        TashkinovExtensionKind.SE) (_ : ett.series.data.chosenVertex q.succ = some vi) (_ :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (_ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    ∀ a ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta, Incident G v a →
    ∀ (w : V), TreeVertexOrder (ett.series.data.tree (Fin.last ett.rounds).castSucc) w v → w ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) →
    ∀ b ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) delta, Incident G w b →
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); previous.succ = terminal → ett.series.data.tree terminal.castSucc =
        ett.series.data.tree (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) →
    ∀ (ci : Fin ett.rounds), IsProperEdgeColoring G (ett.series.data.coloring ci.castSucc) →
        IsOneEdgeUncolored (ett.series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G
        (ett.series.data.coloring ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring
        ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree ci.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate ett.series.data ci.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree ci.succ.castSucc)
        (TashkinovStoredColors ett.series.data ci.castSucc) (ett.series.data.coloring
        ci.castSucc)), (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data ci.castSucc)) choice.selected rho ∧ ¬Disjoint
        (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (ett.series.data.tree
        ci.succ.castSucc))) →
    ∀ (gamma : Fin k), ParallelExtensionColor ett.series.data ci.castSucc choice.selected
        choice.vertex gamma →
    ∀ (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
        StableColoring (ett.series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data ci.castSucc)) choice.selected secondStable →
        TreeExit (ett.series.data.tree ci.succ.castSucc) secondStable gamma choice.color
        choice.vertex → ett.series.data.coloring ci.succ = TwoColorComponentSwap G secondStable
        gamma choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G
        (ett.series.data.coloring ci.succ) → IsOneEdgeUncolored (ett.series.data.coloring ci.succ)
        e0 → ett.series.data.stored ci.succ = { choice.color, gamma } →
        ett.series.data.connectingEdges ci.succ = { choice.edge } → ett.series.data.kind ci.succ =
        some TashkinovExtensionKind.PE → ett.series.data.chosenVertex ci.succ = some choice.vertex
        → ett.series.data.outsideVertex ci.succ = some choice.otherEndpoint →
        ett.series.data.delta ci.succ = some choice.color → ett.series.data.gamma ci.succ = some
        gamma → TashkinovClosure (ett.series.data.coloring ci.succ) (ett.series.data.tree
        ci.succ.castSucc) (ett.series.data.tree ci.succ.succ) → TreeSequenceInitialSegment
        (ett.series.data.tree ci.succ.castSucc) (ett.series.data.tree ci.succ.succ) →
        (ett.series.data.tree ci.succ.castSucc).length < (ett.series.data.tree
        ci.succ.succ).length → terminal = ci.succ → v = vi ∨ TreeVertexOrder T v vi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower
  let this : DecidableEq V :=
    Classical.decEq V
  intro stageToStage orderTransfer sigma hproper hone hstable delta hdefective v hvFinal q vi
      hkind hchosen hfirstBound hvN a haColor hva w hwv hwN b hbColor hwb terminal previous
      hpreviousSucc htreeTerminal ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma gammaRule
      secondStable secondStableProper secondStableRelation exitWitness currentColoring
      currentProper currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension
      hslot
  have hci : ci = previous := by
    apply Fin.ext
    have hs := congrArg Fin.val hslot
    simp [terminal, previous] at hs ⊢
    omega
  subst ci
  have hterminalEq : terminal = previous.succ := hslot
  have htreeEq : ett.series.data.tree terminal.castSucc =
      ett.series.data.tree previous.succ.castSucc := by
    rw [hterminalEq]
  have hchoiceVertex : choice.vertex ∈
      TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) := by
    simpa [htreeEq] using choice.vertexDefective.1
  have hgammaSecond : gamma ∈ MissingColors G secondStable
      choice.vertex := by
    rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
    exact gammaRule.1
  have hchoiceSecond :=
    @helper_hchoiceSecond_1447 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hvFinal) (@q)
        (@secondStable) (@choice) (@secondStableRelation)
  have hgammaDeltaNe :=
    @helper_hgammaDeltaNe_1453 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hvFinal) (@q) (@gamma)
        (@secondStable) (@choice) (@hgammaSecond) (@hchoiceSecond)
  have hchoiceSecondComponent : Sum.inr choice.edge ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
  have hdeltaCurrentMissing :=
    @helper_hdeltaCurrentMissing_266 V E inferInstance inferInstance inferInstance G k e0
        input T generating ett hpositive gamma secondStable secondStableProper choice
        currentColoring hterminalEq hgammaSecond hchoiceSecond hgammaDeltaNe hchoiceSecondComponent
  have hdeltaSigmaMissing : choice.color ∈ MissingColors G sigma
      choice.vertex := by
    rw [hstable.2 choice.vertex hchoiceVertex]
    exact hdeltaCurrentMissing
  have hgammaControl :=
    @helper_hgammaControl_803 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett hpositive v hvFinal q gamma choice currentStored hterminalEq
  have hfixBoth := (sc1 G e0
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data terminal)
      (ett.series.data.coloring terminal) sigma
      (by simpa [hterminalEq] using currentProper)
      (by simpa [hterminalEq] using currentOneUncolored)
      hproper hone).mp hstable
  have boundaryIncident :=
    @helper_boundaryIncident_1485 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett)
  have hgammaBoundaryCurrent :
      BoundaryColorEdges G (ett.series.data.coloring terminal)
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
        gamma = {choice.edge} := by
    have hbound := HkuParallelBoundaryStructure G k ett.rounds e0 input
      ett.series previous choice.edge choice.color gamma choice.vertex
      currentKind currentEdges currentDelta currentGamma currentVertex
    simpa [hterminalEq] using hbound.1
  have hgammaBoundarySigma :=
    @helper_hgammaBoundarySigma_844 V E inferInstance inferInstance inferInstance G k e0
        input T generating ett hpositive sigma gamma choice hgammaControl hfixBoth
        boundaryIncident hgammaBoundaryCurrent
  have hdeltaGammaNe :=
    @helper_hdeltaGammaNe_1506 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@delta) (@hdefective)
        (@v) (@hvFinal) (@q) (@a) (@haColor) (@b) (@hbColor) (@gamma) (@choice)
        (@hgammaBoundarySigma)
  have hcomponent :=
    @helper_hcomponent_1512 (@V) (@E) inferInstance inferInstance  inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@hlower) (@sigma)
        (@hproper) (@hone) (@hstable) (@v) (@hvFinal) (@q) (@hpreviousSucc) (@gamma) (@choice)
        (@currentKind) (@currentVertex) (@currentDelta) (@currentGamma)
  obtain ⟨selected, recoveredSecond, hselectedProper, hselectedOne,
      hselectedStable, hrecoveredSecondProper, hrecoveredSecondOne,
      hrecoveredSecondStable, hcurrentSwap, hundoneSecond,
      hundoneSelected, hundonePrevious⟩ :=
    ParallelExtensionUndoStable G k ett.rounds e0 input ett.series previous
      choice.vertex gamma choice.color currentKind currentVertex currentGamma
      currentDelta sigma hproper hone
      (by simpa only [hpreviousSucc, terminal] using hstable)
      choice.vertexDefective.1
      (by simpa only [hpreviousSucc, terminal] using hcomponent)
  exact @helper_continuation_1207 V E inferInstance inferInstance  inferInstance G k
      e0 input T generating ett hMP hpositive hlower stageToStage orderTransfer sigma hproper
      hone delta v hvFinal q vi hkind hchosen hfirstBound hvN a haColor hva w hwv hwN b hbColor
      hwb hpreviousSucc htreeTerminal gamma choice currentVertex hterminalEq hgammaDeltaNe
      hdeltaSigmaMissing hdeltaGammaNe hcomponent hundonePrevious
theorem Basic2TerminalPE {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hterminalKind :
      ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    StableColoring Tn (TashkinovStoredColors ett.series.data n) (ett.series.data.coloring n)
        sigma →
    ∀ (delta : Fin k),
    DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
    ∀ (v : V),
    BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v →
    (∃ w,
        BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧
          TreeVertexOrder Tn w v) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (q : Fin ett.rounds) (vi : V),
    (ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
        ett.series.data.kind q.succ = some TashkinovExtensionKind.SE) →
    ett.series.data.chosenVertex q.succ = some vi →
    ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 →
    v = vi ∨ TreeVertexOrder T v vi := by
  classical
  let : DecidableEq V := Classical.decEq V
  have stageToStage (first last : ℕ) (positive : 1 ≤ first)
      (ordered : first ≤ last) (bounded : last ≤ ett.rounds) :
      TreeSequenceInitialSegment
        (ett.series.data.tree
          ⟨first, lt_of_le_of_lt ordered (Nat.lt_succ_of_le (Nat.le_succ_of_le bounded))⟩)
        (ett.series.data.tree ⟨last, Nat.lt_succ_of_le (Nat.le_succ_of_le bounded)⟩) :=
    ett.series.stageInitialSegmentOfLE _ _
      (Nat.lt_of_lt_of_le Nat.zero_lt_one positive) ordered
  have orderTransfer : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B → ∀ u w,
        TreeVertexOrder A u w → TreeVertexOrder B u w := by
    intro A B hAB u w huw
    rcases hAB with ⟨hlen, hvertices, _⟩
    rcases huw with ⟨iu, iw, hu, hw, hi⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) iu,
      Fin.castLE (Nat.succ_le_succ hlen) iw,
      (hvertices iu).trans hu, (hvertices iw).trans hw, hi⟩
  dsimp only
  intro sigma hproper hone hstable delta hdefective v hvBoundary
    hvNonminimum hvFinal q vi hkind hchosen hfirstBound
  rcases hvBoundary with ⟨hvN, a, haColor, hva⟩
  rcases hvNonminimum with
    ⟨w, ⟨hwN, b, hbColor, hwb⟩, hwv⟩
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let previous : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hpreviousSucc : previous.succ = terminal := by
    apply Fin.ext
    simp [previous, terminal]
    omega
  have htreeTerminal :
      ett.series.data.tree terminal.castSucc =
        ett.series.data.tree ⟨ett.rounds, by omega⟩ := by
    congr 1
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
    have hterm := hterminalKind
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hterm := hterminalKind
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_195 V E inferInstance inferInstance  inferInstance G
              k e0 input T generating ett hMP hpositive hlower stageToStage orderTransfer sigma
              hproper hone hstable delta hdefective v hvFinal q vi hkind hchosen hfirstBound hvN
              a haColor hva w hwv hwN b hbColor hwb hpreviousSucc htreeTerminal ci previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
              seriesAlternativeFails gamma gammaRule secondStable secondStableProper
              secondStableRelation exitWitness currentColoring currentProper currentOneUncolored
              currentStored currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma closedExtension orderedExtension strictExtension hslot
end GoldbergSeymour

end
