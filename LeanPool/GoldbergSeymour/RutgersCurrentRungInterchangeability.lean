/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.RutgersCounterexampleMinimumExists
public import LeanPool.GoldbergSeymour.RutgersMiddleExitOutsideTerminalLadder
public import LeanPool.GoldbergSeymour.RutgersStrictShortening

/-!
# Rutgers Current Rung Interchangeability

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem RutgersCurrentRungInterchangeability
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty original)
    (hdegree : MaximumDegree G + 1 <= k)
    (hcurrentOne : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      ColoredVertexSetElementary G generating'
        (TreeSequenceVertexSet T'))
    (hcurrentFour : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      let terminal : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tterminal : TreeSequence G e0 :=
        current.series.data.tree terminal.castSucc
      forall (v : V) (gamma delta : Fin k),
        current.series.data.kind terminal =
          some TashkinovExtensionKind.PE ->
        current.series.data.chosenVertex terminal = some v ->
        current.series.data.gamma terminal = some gamma ->
        current.series.data.delta terminal = some delta ->
        forall sigma : PartialEdgeColoring E k,
          IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
          StableColoring Tterminal
            (TashkinovStoredColors current.series.data terminal)
            (current.series.data.coloring terminal) sigma ->
          forall w, w ∈ TreeSequenceVertexSet Tterminal ->
            (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                (Sum.inl v) <-> w = v))
    (hcurrentSix : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      let terminal : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tterminal : TreeSequence G e0 :=
        current.series.data.tree terminal.castSucc
      forall sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
        StableColoring Tterminal
          (TashkinovStoredColors current.series.data terminal)
          (current.series.data.coloring terminal) sigma ->
        ModColoring current sigma)
    (hlowerTwo : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds -> lower.rounds < original.rounds ->
      MaximumProperty lower ->
      let terminal : Fin (lower.rounds + 1) := Fin.last lower.rounds
      let Tnext : TreeSequence G e0 :=
        lower.series.data.tree (Fin.last (lower.rounds + 1))
      forall sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
        StableColoring Tnext
          (TashkinovStoredColors lower.series.data terminal)
          (lower.series.data.coloring terminal) sigma ->
        forall alpha beta : Fin k,
          (alpha ∈ TreeMissingColors sigma Tnext ∨
            beta ∈ TreeMissingColors sigma Tnext) ->
          TreeInterchangeable G Tnext sigma alpha beta) :
    let terminal : Fin (original.rounds + 1) := Fin.last original.rounds
    let Tnext : TreeSequence G e0 :=
      original.series.data.tree (Fin.last (original.rounds + 1))
    forall sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
      StableColoring Tnext
        (TashkinovStoredColors original.series.data terminal)
        (original.series.data.coloring terminal) sigma ->
      forall alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigma Tnext ∨
          beta ∈ TreeMissingColors sigma Tnext) ->
        TreeInterchangeable G Tnext sigma alpha beta := by
  classical
  dsimp
  intro sigma hproper hone hstable alpha beta hmissing
  have interchangeSwap :
      TreeInterchangeable G (original.series.data.tree (Fin.last (original.rounds + 1)))
        sigma alpha beta ↔
      TreeInterchangeable G (original.series.data.tree (Fin.last (original.rounds + 1)))
        sigma beta alpha :=
    ⟨TreeInterchangeable.symm, TreeInterchangeable.symm⟩
  by_cases heq : alpha = beta
  · subst alpha
    simp [TreeInterchangeable, TwoColorPathComponent]
  by_cases halpha : alpha ∈ TreeMissingColors sigma
      (original.series.data.tree (Fin.last (original.rounds + 1)))
  · by_contra hnot
    obtain ⟨presentation, counterexample, hminimum⟩ :=
      RutgersCounterexampleMinimumExists G k e0
        (input := _) (T := _) (generating := _) original hMP
        hcurrentOne hcurrentSix sigma hproper hone hstable alpha beta heq
        halpha hnot
    have helementary :
        ColoredVertexSetElementary G presentation.sigma
          (TreeSequenceVertexSet presentation.U) := by
      apply hcurrentOne presentation.corresponding.replacementETT
      · exact presentation.corresponding.rungAgreement
      · exact presentation.maximum
    have houtside := RutgersMiddleExitOutsideTerminalLadder G k e0 original
      hdegree hcurrentFour hlowerTwo presentation counterexample helementary
    obtain ⟨newPresentation, newCounterexample, hshort⟩ :=
      RutgersStrictShortening G k e0 original hdegree hcurrentOne hcurrentSix
        presentation counterexample houtside
    have hweak := hminimum newPresentation newCounterexample
    exact (Nat.not_lt_of_ge hweak) hshort
  · have hbeta : beta ∈ TreeMissingColors sigma
        (original.series.data.tree (Fin.last (original.rounds + 1))) := by
      exact hmissing.resolve_left halpha
    by_contra hnot
    have hnotSwap : ¬ TreeInterchangeable G
        (original.series.data.tree (Fin.last (original.rounds + 1)))
        sigma beta alpha := by
      intro hs
      exact hnot (interchangeSwap.mpr hs)
    obtain ⟨presentation, counterexample, hminimum⟩ :=
      RutgersCounterexampleMinimumExists G k e0
        (input := _) (T := _) (generating := _) original hMP
        hcurrentOne hcurrentSix sigma hproper hone hstable beta alpha
        (by intro h; exact heq h.symm)
        hbeta hnotSwap
    have helementary :
        ColoredVertexSetElementary G presentation.sigma
          (TreeSequenceVertexSet presentation.U) := by
      apply hcurrentOne presentation.corresponding.replacementETT
      · exact presentation.corresponding.rungAgreement
      · exact presentation.maximum
    have houtside := RutgersMiddleExitOutsideTerminalLadder G k e0 original
      hdegree hcurrentFour hlowerTwo presentation counterexample helementary
    obtain ⟨newPresentation, newCounterexample, hshort⟩ :=
      RutgersStrictShortening G k e0 original hdegree hcurrentOne hcurrentSix
        presentation counterexample houtside
    have hweak := hminimum newPresentation newCounterexample
    exfalso
    exact (Nat.not_lt_of_ge hweak) hshort

end GoldbergSeymour

end
