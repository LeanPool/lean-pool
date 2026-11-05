/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumPropertyTransport

public import LeanPool.GoldbergSeymour.OrderedExitCounterexample
public import LeanPool.GoldbergSeymour.TerminalStableRoute

public import LeanPool.GoldbergSeymour.RutgersCounterexampleMeasure

/-!
# Rutgers Counterexample Minimum Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem RutgersCounterexampleMinimumExists
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty original)
    (hcurrentOne : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T'))
    (hcurrentSix : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      let n : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tn : TreeSequence G e0 := current.series.data.tree n.castSucc
      forall sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
        StableColoring Tn
          (TashkinovStoredColors current.series.data n)
          (current.series.data.coloring n) sigma ->
        ModColoring current sigma)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (original.series.data.tree (Fin.last (original.rounds + 1)))
      (TashkinovStoredColors original.series.data
        (Fin.last original.rounds))
      (original.series.data.coloring (Fin.last original.rounds)) sigma)
    (alpha beta : Fin k) (hcolors : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors sigma
      (original.series.data.tree (Fin.last (original.rounds + 1))))
    (hnot : ¬ TreeInterchangeable G
      (original.series.data.tree (Fin.last (original.rounds + 1)))
      sigma alpha beta) :
    exists (presentation : RutgersClosedPresentation G k e0 original)
      (counterexample :
        RutgersCounterexample G k e0 original presentation),
      forall (otherPresentation :
          RutgersClosedPresentation G k e0 original)
        (otherCounterexample :
          RutgersCounterexample G k e0 original otherPresentation),
        RutgersCounterexampleMeasure counterexample <=
          RutgersCounterexampleMeasure otherCounterexample := by
  classical
  let F := original.series.data.tree (Fin.last (original.rounds + 1))
  obtain ⟨_, _, hsegment, hstrict, hterminalStable, hroute⟩ :=
    P2647_T1_TerminalStableRoute G k e0 original sigma hproper hone hstable
  have hmod : ModColoring original sigma :=
    hcurrentSix original rfl hMP sigma hproper hone hterminalStable
  have eligible :
      (original.series.data.kind (Fin.last original.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma
          (original.series.data.tree (Fin.last original.rounds).castSucc) F) ∨
      ((original.series.data.kind (Fin.last original.rounds) =
            some TashkinovExtensionKind.SE ∨
          original.series.data.kind (Fin.last original.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          original.series.data.connectingEdges (Fin.last original.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (original.series.data.tree (Fin.last original.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence sigma seed F) := by
    rcases hroute with ⟨hkind, hclosure⟩ | ⟨hkind, f, seed, hedge, hadjoin, hclosure⟩
    · exact Or.inl ⟨hkind, hclosure.1⟩
    · exact Or.inr ⟨hkind, f, seed, hedge, hadjoin, hclosure.1⟩
  obtain ⟨corr⟩ := hmod.2.2 F hsegment hstrict eligible
  have hmaximum := MaximumPropertyTransport G k e0 original sigma hmod F corr hMP
  have replacementRoute :
      let replacement := corr.replacementETT
      let n := Fin.last replacement.rounds
      let Tn := replacement.series.data.tree n.castSucc
      (replacement.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovClosure sigma Tn F) ∨
        ((replacement.series.data.kind n = some TashkinovExtensionKind.SE ∨
            replacement.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            replacement.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovClosure sigma seed F) := by
    rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive replacementData above strict below generating =>
      cases rungAgreement
      have seriesSame : replacementData = replacementSeries := eq_of_heq seriesPresentation
      cases seriesSame
      let q : Fin original.rounds := ⟨original.rounds - 1, by
        have := original.roundsPositive
        omega⟩
      have hq : q.succ = Fin.last original.rounds := by
        apply Fin.ext
        dsimp [q]
        have := original.roundsPositive
        omega
      have ladderEq : replacementSeries.data.tree
          (Fin.last original.rounds).castSucc =
          original.series.data.tree (Fin.last original.rounds).castSucc := by
        rw [← hq]
        exact ladderTreesAgree q
      dsimp
      simpa only [ladderEq, extensionKindsAgree, connectingEdgesAgree] using hroute
  let presentation : RutgersClosedPresentation G k e0 original :=
    ⟨sigma, F, corr, hmaximum, replacementRoute⟩
  have hsigma : presentation.sigma = sigma := rfl
  have hU : presentation.U = F := rfl
  have helementary : ColoredVertexSetElementary G presentation.sigma
      (TreeSequenceVertexSet presentation.U) :=
    hcurrentOne presentation.corresponding.replacementETT
      presentation.corresponding.rungAgreement presentation.maximum
  have hclosed : ColoredVertexSetClosed G presentation.sigma
      (TreeSequenceVertexSet presentation.U) := by
    rcases presentation.terminalRoute with ⟨_, hclosure⟩ |
      ⟨_, f, seed, _, _, hclosure⟩
    · exact hclosure.2
    · exact hclosure.2
  have hproperPresentation : IsProperEdgeColoring G presentation.sigma := by
    rw [hsigma]
    exact hproper
  have halphaPresentation :
      alpha ∈ TreeMissingColors presentation.sigma presentation.U := by
    rw [hsigma, hU]
    exact halpha
  have hnotPresentation :
      ¬ TreeInterchangeable G presentation.U presentation.sigma alpha beta := by
    rw [hsigma, hU]
    exact hnot
  obtain ⟨counterexample, _, _⟩ :=
    P2647_T1_OrderedExitCounterexample G k e0 original presentation
      hproperPresentation helementary hclosed alpha beta hcolors
      halphaPresentation hnotPresentation
  let attainable : Nat → Prop := fun m =>
    ∃ (P : RutgersClosedPresentation G k e0 original)
      (C : RutgersCounterexample G k e0 original P),
      RutgersCounterexampleMeasure C = m
  have inhabited : ∃ m, attainable m :=
    ⟨RutgersCounterexampleMeasure counterexample, presentation, counterexample, rfl⟩
  obtain ⟨minimumPresentation, minimumCounterexample, hmeasure⟩ :=
    Nat.find_spec inhabited
  refine ⟨minimumPresentation, minimumCounterexample, ?_⟩
  intro otherPresentation otherCounterexample
  rw [hmeasure]
  exact Nat.find_min' inhabited ⟨otherPresentation, otherCounterexample, rfl⟩

end GoldbergSeymour

end
