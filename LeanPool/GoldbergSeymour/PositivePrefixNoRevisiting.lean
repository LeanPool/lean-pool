/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Preamble

public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint
public import LeanPool.GoldbergSeymour.TdEarlierPEWitnessIdentification
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorInterchangeableDistinctComponentCycle
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion
public import LeanPool.GoldbergSeymour.RevisitingCertificatePreparation

/-!
# P2971_T1_Positive Prefix No Revisiting

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev positivePrefixContradictionStatement.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds),
  (
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
  (0 : ℕ) < lower.rounds →
  lower.rounds < ett.rounds →
  MaximumProperty lower →
  (
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tnext : TreeSequence G e0 :=
   lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ)));
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tnext (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ (alpha beta : Fin k),
  alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma Tnext →
  TreeInterchangeable G Tnext sigma alpha beta) ∧
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc;
  ∀ (v : V) (gamma delta : Fin k),
  lower.series.data.kind n = some TashkinovExtensionKind.PE →
  lower.series.data.chosenVertex n = some v →
  lower.series.data.gamma n = some gamma →
  lower.series.data.delta n = some delta →
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tn (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ w ∈ TreeSequenceVertexSet Tn,
   Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔ w = v) →
  ∀ (sigmaPrev : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigmaPrev →
  IsOneEdgeUncolored sigmaPrev e0 →
  IsProperEdgeColoring G
    (ett.series.data.coloring
     (⟨ett.rounds - (1 : ℕ),
        positivePrefixPredecessorBound ett.rounds hroundLarge⟩ :
       Fin ett.rounds).castSucc) →
  IsOneEdgeUncolored
    (ett.series.data.coloring
     (⟨ett.rounds - (1 : ℕ),
        positivePrefixPredecessorBound ett.rounds hroundLarge⟩ :
       Fin ett.rounds).castSucc)
    e0 →
  StableColoring
    (ett.series.data.tree
     (⟨ett.rounds - (1 : ℕ),
        positivePrefixPredecessorBound ett.rounds hroundLarge⟩ :
       Fin ett.rounds).succ.castSucc)
    (TashkinovStoredColors ett.series.data
     (⟨ett.rounds - (1 : ℕ),
        positivePrefixPredecessorBound ett.rounds hroundLarge⟩ :
       Fin ett.rounds).castSucc)
    (ett.series.data.coloring
     (⟨ett.rounds - (1 : ℕ),
        positivePrefixPredecessorBound ett.rounds hroundLarge⟩ :
       Fin ett.rounds).castSucc)
    sigmaPrev →
  ∀
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - (1 : ℕ),
         positivePrefixPredecessorBound ett.rounds hroundLarge⟩ :
        Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
  MaximumProperty originalPrefix →
  (
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i =
   ett.series.data.tree
    (Fin.castLE
     (positivePrefixPrefixBound ett.rounds originalPrefix.rounds 2 hr)
     i)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring
     (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds 1 hr)
      i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored
      (Fin.castLE
       (positivePrefixPrefixBound ett.rounds originalPrefix.rounds 1 hr)
       i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges
       (Fin.castLE
        (positivePrefixPrefixBound ett.rounds originalPrefix.rounds 1 hr)
        i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind
        (Fin.castLE
         (positivePrefixPrefixBound ett.rounds originalPrefix.rounds 1 hr)
         i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE
         (positivePrefixPrefixBound ett.rounds originalPrefix.rounds 1 hr)
         i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev →
  MaximumProperty corr.replacementETT →
  ¬Nonempty
     (RevisitingExtensionCertificate ett.series.data
      (⟨ett.rounds - (1 : ℕ),
         positivePrefixPredecessorBound ett.rounds hroundLarge⟩ :
        Fin ett.rounds).castSucc) →
  ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin ett.rounds)
      : Fin ett.rounds).succ =
    Fin.last ett.rounds →
  (0 : ℕ) < originalPrefix.rounds →
  Fin.castLE
     (positivePrefixPrefixBound ett.rounds originalPrefix.rounds 1 hr)
     (Fin.last originalPrefix.rounds : Fin (originalPrefix.rounds + (1 : ℕ))) =
    ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
        ett.rounds) :
      Fin ett.rounds).castSucc →
  corr.replacementSeries.data.tree
     (Fin.last originalPrefix.rounds :
       Fin (originalPrefix.rounds + (1 : ℕ))).succ =
    ett.series.data.tree
     ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
         ett.rounds) :
       Fin ett.rounds).succ.castSucc →
  originalPrefix.series.data.tree
     (Fin.last originalPrefix.rounds :
       Fin (originalPrefix.rounds + (1 : ℕ))).castSucc =
    ett.series.data.tree
     ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
         ett.rounds) :
       Fin ett.rounds).castSucc.castSucc →
  (
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (base : ExtendedTashkinovTree G k e0 input' T' generating'),
  (0 : ℕ) < base.rounds →
  base.rounds < ett.rounds →
  MaximumProperty base →
  ∀ (r : ℕ) (series : TashkinovSeries G k r e0 input'),
  base.rounds = r →
  base.series ≍ series →
  ∀ (a : Fin (r + (1 : ℕ))) (v : V) (gamma delta : Fin k),
  (0 : ℕ) < (↑a : ℕ) →
  series.data.kind a = some TashkinovExtensionKind.PE →
  series.data.chosenVertex a = some v →
  series.data.gamma a = some gamma →
  series.data.delta a = some delta →
  IsProperEdgeColoring G (series.data.coloring a) →
  IsOneEdgeUncolored (series.data.coloring a) e0 →
  ∀ w ∈ TreeSequenceVertexSet (series.data.tree a.castSucc),
   Sum.inl w ∈
     TwoColorComponent G (series.data.coloring a) gamma delta
      (Sum.inl v) ↔
    w = v) →
  ∀
   (available :
    RevisitingExtensionCertificate corr.replacementSeries.data
     (Fin.last originalPrefix.rounds)),
  (0 : ℕ) <
    (↑(available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) : ℕ) →
  originalPrefix.series.data.kind
     (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) =
    some TashkinovExtensionKind.PE →
  ∀ (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0
     (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  ParallelExtensionColor originalPrefix.series.data oldi.castSucc
    oldChoice.selected oldChoice.vertex oldGamma →
  ∀ (oldSecond : PartialEdgeColoring E k),
  IsProperEdgeColoring G oldSecond →
  StableColoring (originalPrefix.series.data.tree oldi.succ.castSucc)
    (insert oldChoice.color
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc))
    oldChoice.selected oldSecond →
  originalPrefix.series.data.coloring oldi.succ =
    TwoColorComponentSwap G oldSecond oldGamma oldChoice.color
     (Sum.inl oldChoice.vertex) →
  IsProperEdgeColoring G
    (originalPrefix.series.data.coloring oldi.succ) →
  IsOneEdgeUncolored (originalPrefix.series.data.coloring oldi.succ)
    e0 →
  originalPrefix.series.data.stored oldi.succ =
    { oldChoice.color, oldGamma } →
  originalPrefix.series.data.connectingEdges oldi.succ =
    { oldChoice.edge } →
  originalPrefix.series.data.kind oldi.succ =
    some TashkinovExtensionKind.PE →
  originalPrefix.series.data.chosenVertex oldi.succ =
    some oldChoice.vertex →
  originalPrefix.series.data.delta oldi.succ =
    some oldChoice.color →
  originalPrefix.series.data.gamma oldi.succ = some oldGamma →
  (available.earlier :
     Fin (originalPrefix.rounds + (1 : ℕ))) =
    oldi.succ →
  oldi.succ =
    (available.earlier :
     Fin (originalPrefix.rounds + (1 : ℕ))) →
  ∀ (newi : Fin originalPrefix.rounds),
  IsProperEdgeColoring G
    (corr.replacementSeries.data.coloring newi.castSucc) →
  IsOneEdgeUncolored
    (corr.replacementSeries.data.coloring newi.castSucc)
    e0 →
  ColoredVertexSetClosed G
    (corr.replacementSeries.data.coloring newi.castSucc)
    (TreeSequenceVertexSet
     (corr.replacementSeries.data.tree
      newi.succ.castSucc)) →
  ¬ColoredVertexSetStronglyClosed G
     (corr.replacementSeries.data.coloring
      newi.castSucc)
     (TreeSequenceVertexSet
      (corr.replacementSeries.data.tree
       newi.succ.castSucc)) →
  ¬Nonempty
     (RevisitingExtensionCertificate
      corr.replacementSeries.data newi.castSucc) →
  ∀
   (newChoicePE :
    MaximumDefectiveChoice G e0
     (corr.replacementSeries.data.tree
      newi.succ.castSucc)
     (TashkinovStoredColors
      corr.replacementSeries.data newi.castSucc)
     (corr.replacementSeries.data.coloring
      newi.castSucc)),
  (∃ (rho : PartialEdgeColoring E k),
    IsProperEdgeColoring G rho ∧
     IsOneEdgeUncolored rho e0 ∧
      StableColoring
        (corr.replacementSeries.data.tree
         newi.succ.castSucc)
        (insert newChoicePE.color
         (TashkinovStoredColors
          corr.replacementSeries.data
          newi.castSucc))
        newChoicePE.selected rho ∧
       ¬Disjoint
         (MissingColors G rho
          newChoicePE.otherEndpoint)
         (TreeMissingColors rho
          (corr.replacementSeries.data.tree
           newi.succ.castSucc))) →
  ∀ (newGamma : Fin k),
  ParallelExtensionColor
    corr.replacementSeries.data newi.castSucc
    newChoicePE.selected newChoicePE.vertex
    newGamma →
  ∀ (newSecond : PartialEdgeColoring E k),
  IsProperEdgeColoring G newSecond →
  StableColoring
    (corr.replacementSeries.data.tree
     newi.succ.castSucc)
    (insert newChoicePE.color
     (TashkinovStoredColors
      corr.replacementSeries.data
      newi.castSucc))
    newChoicePE.selected newSecond →
  TreeExit
    (corr.replacementSeries.data.tree
     newi.succ.castSucc)
    newSecond newGamma newChoicePE.color
    newChoicePE.vertex →
  corr.replacementSeries.data.coloring
     newi.succ =
    TwoColorComponentSwap G newSecond
     newGamma newChoicePE.color
     (Sum.inl newChoicePE.vertex) →
  IsProperEdgeColoring G
    (corr.replacementSeries.data.coloring
     newi.succ) →
  IsOneEdgeUncolored
    (corr.replacementSeries.data.coloring
     newi.succ)
    e0 →
  corr.replacementSeries.data.stored
     newi.succ =
    { newChoicePE.color, newGamma } →
  corr.replacementSeries.data.connectingEdges
     newi.succ =
    { newChoicePE.edge } →
  corr.replacementSeries.data.kind
     newi.succ =
    some TashkinovExtensionKind.PE →
  corr.replacementSeries.data.chosenVertex
     newi.succ =
    some newChoicePE.vertex →
  corr.replacementSeries.data.outsideVertex
     newi.succ =
    some newChoicePE.otherEndpoint →
  corr.replacementSeries.data.delta
     newi.succ =
    some newChoicePE.color →
  corr.replacementSeries.data.gamma
     newi.succ =
    some newGamma →
  TashkinovClosure
    (corr.replacementSeries.data.coloring
     newi.succ)
    (corr.replacementSeries.data.tree
     newi.succ.castSucc)
    (corr.replacementSeries.data.tree
     newi.succ.succ) →
  TreeSequenceInitialSegment
    (corr.replacementSeries.data.tree
     newi.succ.castSucc)
    (corr.replacementSeries.data.tree
     newi.succ.succ) →
  (corr.replacementSeries.data.tree
      newi.succ.castSucc).length <
    (corr.replacementSeries.data.tree
      newi.succ.succ).length →
  (available.earlier :
     Fin
      (originalPrefix.rounds +
       (1 : ℕ))) =
    newi.succ →
  False

private abbrev positivePrefixColorIdentificationStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : 1 < ett.rounds),
  (
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
  0 < lower.rounds →
  lower.rounds < ett.rounds →
  MaximumProperty lower →
  (
  let n : Fin (lower.rounds + 1) := Fin.last lower.rounds;
  let Tnext : TreeSequence G e0 := lower.series.data.tree (Fin.last (lower.rounds + 1));
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tnext (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ (alpha beta : Fin k),
  alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma Tnext →
  TreeInterchangeable G Tnext sigma alpha beta) ∧
  let n : Fin (lower.rounds + 1) := Fin.last lower.rounds;
  let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc;
  ∀ (v : V) (gamma delta : Fin k),
  lower.series.data.kind n = some TashkinovExtensionKind.PE →
  lower.series.data.chosenVertex n = some v →
  lower.series.data.gamma n = some gamma →
  lower.series.data.delta n = some delta →
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tn (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ w ∈ TreeSequenceVertexSet Tn,
   Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔ w = v) →
  let q : Fin ett.rounds :=
   (⟨ett.rounds - 1,
     Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
    Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigmaPrev →
  IsOneEdgeUncolored sigmaPrev e0 →
  IsProperEdgeColoring G
    (ett.series.data.coloring
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).castSucc) →
  IsOneEdgeUncolored
    (ett.series.data.coloring
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).castSucc)
    e0 →
  StableColoring
    (ett.series.data.tree
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).succ.castSucc)
    (TashkinovStoredColors ett.series.data
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).castSucc)
    (ett.series.data.coloring
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).castSucc)
    sigmaPrev →
  ∀
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - 1,
         Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
        Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - 1),
  MaximumProperty originalPrefix →
  (
  ∀ (i : Fin (originalPrefix.rounds + 2)),
  originalPrefix.series.data.tree i =
   ett.series.data.tree
    (Fin.castLE
     (Decidable.byContradiction fun (a : ¬originalPrefix.rounds + 2 ≤ ett.rounds + 2) ↦
      (by omega))
     i)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + 1)),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring
     (Fin.castLE
      (Decidable.byContradiction
       fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
      i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored
      (Fin.castLE
       (Decidable.byContradiction
        fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
       i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges
       (Fin.castLE
        (Decidable.byContradiction
         fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
        i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind
        (Fin.castLE
         (Decidable.byContradiction
          fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
         i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE
         (Decidable.byContradiction
          fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
         i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  MaximumProperty corr.replacementETT →
  ¬Nonempty
     (RevisitingExtensionCertificate ett.series.data
      (⟨ett.rounds - 1,
         Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
          (by omega)⟩ :
        Fin ett.rounds).castSucc) →
  (⟨ett.rounds - 1,
       Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
        (by omega)⟩ :
      Fin ett.rounds).succ =
    Fin.last ett.rounds →
  let replacementLast : Fin (originalPrefix.rounds + 1) :=
   Fin.last originalPrefix.rounds;
  corr.replacementSeries.data.coloring replacementLast = sigmaPrev →
  0 < originalPrefix.rounds →
  Fin.castLE
     (Decidable.byContradiction
      fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
     replacementLast =
    (⟨ett.rounds - 1,
       Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
        (by omega)⟩ :
      Fin ett.rounds).castSucc →
  corr.replacementSeries.data.tree replacementLast.succ =
    ett.series.data.tree
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
         (by omega)⟩ :
       Fin ett.rounds).succ.castSucc →
  originalPrefix.series.data.tree replacementLast.castSucc =
    ett.series.data.tree
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
         (by omega)⟩ :
       Fin ett.rounds).castSucc.castSucc →
  (
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (base : ExtendedTashkinovTree G k e0 input' T' generating'),
  0 < base.rounds →
  base.rounds < ett.rounds →
  MaximumProperty base →
  ∀ (r : ℕ) (series : TashkinovSeries G k r e0 input'),
  base.rounds = r →
  base.series ≍ series →
  ∀ (a : Fin (r + 1)) (v : V) (gamma delta : Fin k),
  0 < (↑a : ℕ) →
  series.data.kind a = some TashkinovExtensionKind.PE →
  series.data.chosenVertex a = some v →
  series.data.gamma a = some gamma →
  series.data.delta a = some delta →
  IsProperEdgeColoring G (series.data.coloring a) →
  IsOneEdgeUncolored (series.data.coloring a) e0 →
  ∀ w ∈ TreeSequenceVertexSet (series.data.tree a.castSucc),
   Sum.inl w ∈
     TwoColorComponent G (series.data.coloring a) gamma delta
      (Sum.inl v) ↔
    w = v) →
  ∀
   (available :
    RevisitingExtensionCertificate corr.replacementSeries.data
     replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + 1) := available.earlier;
  0 < (↑earlierPrefix : ℕ) →
  originalPrefix.series.data.kind earlierPrefix =
    some TashkinovExtensionKind.PE →
  ∀ (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0
     (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  ParallelExtensionColor originalPrefix.series.data oldi.castSucc
    oldChoice.selected oldChoice.vertex oldGamma →
  ∀ (oldSecond : PartialEdgeColoring E k),
  IsProperEdgeColoring G oldSecond →
  StableColoring (originalPrefix.series.data.tree oldi.succ.castSucc)
    (insert oldChoice.color
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc))
    oldChoice.selected oldSecond →
  originalPrefix.series.data.coloring oldi.succ =
    TwoColorComponentSwap G oldSecond oldGamma oldChoice.color
     (Sum.inl oldChoice.vertex) →
  IsProperEdgeColoring G
    (originalPrefix.series.data.coloring oldi.succ) →
  IsOneEdgeUncolored (originalPrefix.series.data.coloring oldi.succ)
    e0 →
  originalPrefix.series.data.stored oldi.succ =
    { oldChoice.color, oldGamma } →
  originalPrefix.series.data.connectingEdges oldi.succ =
    { oldChoice.edge } →
  originalPrefix.series.data.kind oldi.succ =
    some TashkinovExtensionKind.PE →
  originalPrefix.series.data.chosenVertex oldi.succ =
    some oldChoice.vertex →
  originalPrefix.series.data.delta oldi.succ =
    some oldChoice.color →
  originalPrefix.series.data.gamma oldi.succ = some oldGamma →
  earlierPrefix = oldi.succ →
  oldi.succ = earlierPrefix →
  ∀ (newGamma : Fin k)
   (newSecond : PartialEdgeColoring E k),
  IsProperEdgeColoring G newSecond →
  IsProperEdgeColoring G
    (corr.replacementSeries.data.coloring
     oldi.castSucc) →
  IsOneEdgeUncolored
    (corr.replacementSeries.data.coloring oldi.castSucc)
    e0 →
  ColoredVertexSetClosed G
    (corr.replacementSeries.data.coloring
     oldi.castSucc)
    (TreeSequenceVertexSet
     (corr.replacementSeries.data.tree
      oldi.succ.castSucc)) →
  ¬ColoredVertexSetStronglyClosed G
     (corr.replacementSeries.data.coloring
      oldi.castSucc)
     (TreeSequenceVertexSet
      (corr.replacementSeries.data.tree
       oldi.succ.castSucc)) →
  ¬Nonempty
     (RevisitingExtensionCertificate
      corr.replacementSeries.data oldi.castSucc) →
  ∀
   (newChoicePE :
    MaximumDefectiveChoice G e0
     (corr.replacementSeries.data.tree
      oldi.succ.castSucc)
     (TashkinovStoredColors
      corr.replacementSeries.data oldi.castSucc)
     (corr.replacementSeries.data.coloring
      oldi.castSucc)),
  (∃ (rho : PartialEdgeColoring E k),
    IsProperEdgeColoring G rho ∧
     IsOneEdgeUncolored rho e0 ∧
      StableColoring
        (corr.replacementSeries.data.tree
         oldi.succ.castSucc)
        (insert newChoicePE.color
         (TashkinovStoredColors
          corr.replacementSeries.data
          oldi.castSucc))
        newChoicePE.selected rho ∧
       ¬Disjoint
         (MissingColors G rho
          newChoicePE.otherEndpoint)
         (TreeMissingColors rho
          (corr.replacementSeries.data.tree
           oldi.succ.castSucc))) →
  ParallelExtensionColor
    corr.replacementSeries.data oldi.castSucc
    newChoicePE.selected newChoicePE.vertex
    newGamma →
  StableColoring
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    (insert newChoicePE.color
     (TashkinovStoredColors
      corr.replacementSeries.data oldi.castSucc))
    newChoicePE.selected newSecond →
  TreeExit
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    newSecond newGamma newChoicePE.color
    newChoicePE.vertex →
  corr.replacementSeries.data.coloring
     oldi.succ =
    TwoColorComponentSwap G newSecond newGamma
     newChoicePE.color
     (Sum.inl newChoicePE.vertex) →
  IsProperEdgeColoring G
    (corr.replacementSeries.data.coloring
     oldi.succ) →
  IsOneEdgeUncolored
    (corr.replacementSeries.data.coloring
     oldi.succ)
    e0 →
  corr.replacementSeries.data.stored
     oldi.succ =
    { newChoicePE.color, newGamma } →
  corr.replacementSeries.data.connectingEdges
     oldi.succ =
    { newChoicePE.edge } →
  corr.replacementSeries.data.kind
     oldi.succ =
    some TashkinovExtensionKind.PE →
  corr.replacementSeries.data.chosenVertex
     oldi.succ =
    some newChoicePE.vertex →
  corr.replacementSeries.data.outsideVertex
     oldi.succ =
    some newChoicePE.otherEndpoint →
  corr.replacementSeries.data.delta
     oldi.succ =
    some newChoicePE.color →
  corr.replacementSeries.data.gamma
     oldi.succ =
    some newGamma →
  TashkinovClosure
    (corr.replacementSeries.data.coloring
     oldi.succ)
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    (corr.replacementSeries.data.tree
     oldi.succ.succ) →
  TreeSequenceInitialSegment
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    (corr.replacementSeries.data.tree
     oldi.succ.succ) →
  (corr.replacementSeries.data.tree
      oldi.succ.castSucc).length <
    (corr.replacementSeries.data.tree
      oldi.succ.succ).length →
  earlierPrefix = oldi.succ →
  oldi.succ = earlierPrefix →
  ∀
   (hbaseTree :
    corr.replacementSeries.data.tree
      oldi.succ.castSucc =
     originalPrefix.series.data.tree
      oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    (TashkinovStoredColors
     originalPrefix.series.data
     oldi.castSucc)
    (originalPrefix.series.data.coloring
     oldi.castSucc) :=
   Eq.symm hbaseTree ▸
    oldChoice;
  (
  ∀ {A B : TreeSequence G e0}
   (hAB : A = B)
   (C : Finset (Fin k))
   (phi :
    PartialEdgeColoring E k)
   (ch :
    MaximumDefectiveChoice G
     e0 A C phi),
  (hAB ▸ ch).edge = ch.edge ∧
   (hAB ▸ ch).vertex =
     ch.vertex ∧
    (hAB ▸
        ch).otherEndpoint =
      ch.otherEndpoint ∧
     (hAB ▸ ch).color =
      ch.color) →
  (Eq.symm hbaseTree ▸
       oldChoice).edge =
     oldChoice.edge ∧
    (Eq.symm hbaseTree ▸
        oldChoice).vertex =
      oldChoice.vertex ∧
     (Eq.symm hbaseTree ▸
         oldChoice).otherEndpoint =
       oldChoice.otherEndpoint ∧
      (Eq.symm hbaseTree ▸
         oldChoice).color =
       oldChoice.color →
  oldChoiceOnNew.edge =
    oldChoice.edge →
  oldChoiceOnNew.vertex =
    oldChoice.vertex →
  oldChoiceOnNew.otherEndpoint =
    oldChoice.otherEndpoint →
  oldChoiceOnNew.color =
    oldChoice.color →
  ({oldChoiceOnNew.edge} : Finset E) =
    {
     newChoicePE.edge } →
  ({oldChoiceOnNew.color, oldGamma} : Finset (Fin k)) =
    { newChoicePE.color,
     newGamma } →
  newChoicePE.edge =
    oldChoiceOnNew.edge →
  s(oldChoiceOnNew.vertex,
     oldChoiceOnNew.otherEndpoint) =
    s(newChoicePE.vertex,
     newChoicePE.otherEndpoint) →
  newChoicePE.vertex =
    oldChoiceOnNew.vertex →
  newChoicePE.otherEndpoint =
    oldChoiceOnNew.otherEndpoint →
  (
  ∀
   (X :
    TreeSequence G
     e0)
   (C :
    Finset
     (Fin k))
   (phi :
    PartialEdgeColoring
     E k)
   (ch :
    MaximumDefectiveChoice
     G e0 X C phi)
   (g : Fin k)
   (second :
    PartialEdgeColoring
     E k),
  IsProperEdgeColoring
    G second →
  StableColoring
    X
    (insert
     ch.color C)
    ch.selected
    second →
  g ∈
    MissingColors
     G
     ch.selected
     ch.vertex →
  have post :
   PartialEdgeColoring
    E k :=
   TwoColorComponentSwap
    G second g
    ch.color
    (Sum.inl
     ch.vertex);
  ch.color ∈
    MissingColors
     G post
     ch.vertex ∧
   g ∉
     MissingColors
      G post
      ch.vertex ∧
    g ≠
     ch.color) →
  oldChoice.color ∈
    MissingColors
     G
     (originalPrefix.series.data.coloring
      oldi.succ)
     oldChoice.vertex →
  oldGamma ∉
    MissingColors
     G
     (originalPrefix.series.data.coloring
      oldi.succ)
     oldChoice.vertex →
  oldGamma ≠
    oldChoice.color →
  newChoicePE.color ∈
    MissingColors
     G
     (corr.replacementSeries.data.coloring
      oldi.succ)
     newChoicePE.vertex →
  newGamma ∉
    MissingColors
     G
     (corr.replacementSeries.data.coloring
      oldi.succ)
     newChoicePE.vertex →
  newGamma ≠
    newChoicePE.color →
  False

private abbrev positivePrefixReturnTransportStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : 1 < ett.rounds),
  (
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
  0 < lower.rounds →
  lower.rounds < ett.rounds →
  MaximumProperty lower →
  (
  let n : Fin (lower.rounds + 1) := Fin.last lower.rounds;
  let Tnext : TreeSequence G e0 := lower.series.data.tree (Fin.last (lower.rounds + 1));
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tnext (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ (alpha beta : Fin k),
  alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma Tnext →
  TreeInterchangeable G Tnext sigma alpha beta) ∧
  let n : Fin (lower.rounds + 1) := Fin.last lower.rounds;
  let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc;
  ∀ (v : V) (gamma delta : Fin k),
  lower.series.data.kind n = some TashkinovExtensionKind.PE →
  lower.series.data.chosenVertex n = some v →
  lower.series.data.gamma n = some gamma →
  lower.series.data.delta n = some delta →
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tn (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ w ∈ TreeSequenceVertexSet Tn,
   Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔ w = v) →
  let q : Fin ett.rounds :=
   (⟨ett.rounds - 1,
     Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
    Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigmaPrev →
  IsOneEdgeUncolored sigmaPrev e0 →
  IsProperEdgeColoring G
    (ett.series.data.coloring
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).castSucc) →
  IsOneEdgeUncolored
    (ett.series.data.coloring
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).castSucc)
    e0 →
  StableColoring
    (ett.series.data.tree
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).succ.castSucc)
    (TashkinovStoredColors ett.series.data
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).castSucc)
    (ett.series.data.coloring
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
       Fin ett.rounds).castSucc)
    sigmaPrev →
  ∀
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - 1,
         Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦ (by omega)⟩ :
        Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - 1),
  MaximumProperty originalPrefix →
  (
  ∀ (i : Fin (originalPrefix.rounds + 2)),
  originalPrefix.series.data.tree i =
   ett.series.data.tree
    (Fin.castLE
     (Decidable.byContradiction fun (a : ¬originalPrefix.rounds + 2 ≤ ett.rounds + 2) ↦
      (by omega))
     i)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + 1)),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring
     (Fin.castLE
      (Decidable.byContradiction
       fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
      i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored
      (Fin.castLE
       (Decidable.byContradiction
        fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
       i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges
       (Fin.castLE
        (Decidable.byContradiction
         fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
        i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind
        (Fin.castLE
         (Decidable.byContradiction
          fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
         i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE
         (Decidable.byContradiction
          fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
         i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  MaximumProperty corr.replacementETT →
  ¬Nonempty
     (RevisitingExtensionCertificate ett.series.data
      (⟨ett.rounds - 1,
         Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
          (by omega)⟩ :
        Fin ett.rounds).castSucc) →
  (⟨ett.rounds - 1,
       Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
        (by omega)⟩ :
      Fin ett.rounds).succ =
    Fin.last ett.rounds →
  let replacementLast : Fin (originalPrefix.rounds + 1) :=
   Fin.last originalPrefix.rounds;
  corr.replacementSeries.data.coloring replacementLast = sigmaPrev →
  0 < originalPrefix.rounds →
  Fin.castLE
     (Decidable.byContradiction
      fun (a : ¬originalPrefix.rounds + 1 ≤ ett.rounds + 1) ↦ (by omega))
     replacementLast =
    (⟨ett.rounds - 1,
       Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
        (by omega)⟩ :
      Fin ett.rounds).castSucc →
  corr.replacementSeries.data.tree replacementLast.succ =
    ett.series.data.tree
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
         (by omega)⟩ :
       Fin ett.rounds).succ.castSucc →
  originalPrefix.series.data.tree replacementLast.castSucc =
    ett.series.data.tree
     (⟨ett.rounds - 1,
        Decidable.byContradiction fun (a : ¬ett.rounds - 1 < ett.rounds) ↦
         (by omega)⟩ :
       Fin ett.rounds).castSucc.castSucc →
  (
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (base : ExtendedTashkinovTree G k e0 input' T' generating'),
  0 < base.rounds →
  base.rounds < ett.rounds →
  MaximumProperty base →
  ∀ (r : ℕ) (series : TashkinovSeries G k r e0 input'),
  base.rounds = r →
  base.series ≍ series →
  ∀ (a : Fin (r + 1)) (v : V) (gamma delta : Fin k),
  0 < (↑a : ℕ) →
  series.data.kind a = some TashkinovExtensionKind.PE →
  series.data.chosenVertex a = some v →
  series.data.gamma a = some gamma →
  series.data.delta a = some delta →
  IsProperEdgeColoring G (series.data.coloring a) →
  IsOneEdgeUncolored (series.data.coloring a) e0 →
  ∀ w ∈ TreeSequenceVertexSet (series.data.tree a.castSucc),
   Sum.inl w ∈
     TwoColorComponent G (series.data.coloring a) gamma delta
      (Sum.inl v) ↔
    w = v) →
  ∀
   (available :
    RevisitingExtensionCertificate corr.replacementSeries.data
     replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + 1) := available.earlier;
  0 < (↑earlierPrefix : ℕ) →
  originalPrefix.series.data.kind earlierPrefix =
    some TashkinovExtensionKind.PE →
  ∀ (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0
     (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  ParallelExtensionColor originalPrefix.series.data oldi.castSucc
    oldChoice.selected oldChoice.vertex oldGamma →
  ∀ (oldSecond : PartialEdgeColoring E k),
  IsProperEdgeColoring G oldSecond →
  StableColoring (originalPrefix.series.data.tree oldi.succ.castSucc)
    (insert oldChoice.color
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc))
    oldChoice.selected oldSecond →
  originalPrefix.series.data.coloring oldi.succ =
    TwoColorComponentSwap G oldSecond oldGamma oldChoice.color
     (Sum.inl oldChoice.vertex) →
  IsProperEdgeColoring G
    (originalPrefix.series.data.coloring oldi.succ) →
  IsOneEdgeUncolored (originalPrefix.series.data.coloring oldi.succ)
    e0 →
  originalPrefix.series.data.stored oldi.succ =
    { oldChoice.color, oldGamma } →
  originalPrefix.series.data.connectingEdges oldi.succ =
    { oldChoice.edge } →
  originalPrefix.series.data.kind oldi.succ =
    some TashkinovExtensionKind.PE →
  originalPrefix.series.data.chosenVertex oldi.succ =
    some oldChoice.vertex →
  originalPrefix.series.data.delta oldi.succ =
    some oldChoice.color →
  originalPrefix.series.data.gamma oldi.succ = some oldGamma →
  earlierPrefix = oldi.succ →
  oldi.succ = earlierPrefix →
  ∀ (newGamma : Fin k)
   (newSecond : PartialEdgeColoring E k),
  IsProperEdgeColoring G newSecond →
  IsProperEdgeColoring G
    (corr.replacementSeries.data.coloring
     oldi.castSucc) →
  IsOneEdgeUncolored
    (corr.replacementSeries.data.coloring oldi.castSucc)
    e0 →
  ColoredVertexSetClosed G
    (corr.replacementSeries.data.coloring
     oldi.castSucc)
    (TreeSequenceVertexSet
     (corr.replacementSeries.data.tree
      oldi.succ.castSucc)) →
  ¬ColoredVertexSetStronglyClosed G
     (corr.replacementSeries.data.coloring
      oldi.castSucc)
     (TreeSequenceVertexSet
      (corr.replacementSeries.data.tree
       oldi.succ.castSucc)) →
  ¬Nonempty
     (RevisitingExtensionCertificate
      corr.replacementSeries.data oldi.castSucc) →
  ∀
   (newChoicePE :
    MaximumDefectiveChoice G e0
     (corr.replacementSeries.data.tree
      oldi.succ.castSucc)
     (TashkinovStoredColors
      corr.replacementSeries.data oldi.castSucc)
     (corr.replacementSeries.data.coloring
      oldi.castSucc)),
  (∃ (rho : PartialEdgeColoring E k),
    IsProperEdgeColoring G rho ∧
     IsOneEdgeUncolored rho e0 ∧
      StableColoring
        (corr.replacementSeries.data.tree
         oldi.succ.castSucc)
        (insert newChoicePE.color
         (TashkinovStoredColors
          corr.replacementSeries.data
          oldi.castSucc))
        newChoicePE.selected rho ∧
       ¬Disjoint
         (MissingColors G rho
          newChoicePE.otherEndpoint)
         (TreeMissingColors rho
          (corr.replacementSeries.data.tree
           oldi.succ.castSucc))) →
  ParallelExtensionColor
    corr.replacementSeries.data oldi.castSucc
    newChoicePE.selected newChoicePE.vertex
    newGamma →
  StableColoring
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    (insert newChoicePE.color
     (TashkinovStoredColors
      corr.replacementSeries.data oldi.castSucc))
    newChoicePE.selected newSecond →
  TreeExit
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    newSecond newGamma newChoicePE.color
    newChoicePE.vertex →
  corr.replacementSeries.data.coloring
     oldi.succ =
    TwoColorComponentSwap G newSecond newGamma
     newChoicePE.color
     (Sum.inl newChoicePE.vertex) →
  IsProperEdgeColoring G
    (corr.replacementSeries.data.coloring
     oldi.succ) →
  IsOneEdgeUncolored
    (corr.replacementSeries.data.coloring
     oldi.succ)
    e0 →
  corr.replacementSeries.data.stored
     oldi.succ =
    { newChoicePE.color, newGamma } →
  corr.replacementSeries.data.connectingEdges
     oldi.succ =
    { newChoicePE.edge } →
  corr.replacementSeries.data.kind
     oldi.succ =
    some TashkinovExtensionKind.PE →
  corr.replacementSeries.data.chosenVertex
     oldi.succ =
    some newChoicePE.vertex →
  corr.replacementSeries.data.outsideVertex
     oldi.succ =
    some newChoicePE.otherEndpoint →
  corr.replacementSeries.data.delta
     oldi.succ =
    some newChoicePE.color →
  corr.replacementSeries.data.gamma
     oldi.succ =
    some newGamma →
  TashkinovClosure
    (corr.replacementSeries.data.coloring
     oldi.succ)
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    (corr.replacementSeries.data.tree
     oldi.succ.succ) →
  TreeSequenceInitialSegment
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    (corr.replacementSeries.data.tree
     oldi.succ.succ) →
  (corr.replacementSeries.data.tree
      oldi.succ.castSucc).length <
    (corr.replacementSeries.data.tree
      oldi.succ.succ).length →
  earlierPrefix = oldi.succ →
  oldi.succ = earlierPrefix →
  ∀
   (hbaseTree :
    corr.replacementSeries.data.tree
      oldi.succ.castSucc =
     originalPrefix.series.data.tree
      oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree
     oldi.succ.castSucc)
    (TashkinovStoredColors
     originalPrefix.series.data
     oldi.castSucc)
    (originalPrefix.series.data.coloring
     oldi.castSucc) :=
   Eq.symm hbaseTree ▸
    oldChoice;
  (
  ∀ {A B : TreeSequence G e0}
   (hAB : A = B)
   (C : Finset (Fin k))
   (phi :
    PartialEdgeColoring E k)
   (ch :
    MaximumDefectiveChoice G
     e0 A C phi),
  (hAB ▸ ch).edge = ch.edge ∧
   (hAB ▸ ch).vertex =
     ch.vertex ∧
    (hAB ▸
        ch).otherEndpoint =
      ch.otherEndpoint ∧
     (hAB ▸ ch).color =
      ch.color) →
  (Eq.symm hbaseTree ▸
       oldChoice).edge =
     oldChoice.edge ∧
    (Eq.symm hbaseTree ▸
        oldChoice).vertex =
      oldChoice.vertex ∧
     (Eq.symm hbaseTree ▸
         oldChoice).otherEndpoint =
       oldChoice.otherEndpoint ∧
      (Eq.symm hbaseTree ▸
         oldChoice).color =
       oldChoice.color →
  oldChoiceOnNew.edge =
    oldChoice.edge →
  oldChoiceOnNew.vertex =
    oldChoice.vertex →
  oldChoiceOnNew.otherEndpoint =
    oldChoice.otherEndpoint →
  oldChoiceOnNew.color =
    oldChoice.color →
  ({oldChoiceOnNew.edge} : Finset E) =
    {
     newChoicePE.edge } →
  ({oldChoiceOnNew.color, oldGamma} : Finset (Fin k)) =
    { newChoicePE.color,
     newGamma } →
  newChoicePE.edge =
    oldChoiceOnNew.edge →
  s(oldChoiceOnNew.vertex,
     oldChoiceOnNew.otherEndpoint) =
    s(newChoicePE.vertex,
     newChoicePE.otherEndpoint) →
  newChoicePE.vertex =
    oldChoiceOnNew.vertex →
  newChoicePE.otherEndpoint =
    oldChoiceOnNew.otherEndpoint →
  (
  ∀
   (X :
    TreeSequence G
     e0)
   (C :
    Finset
     (Fin k))
   (phi :
    PartialEdgeColoring
     E k)
   (ch :
    MaximumDefectiveChoice
     G e0 X C phi)
   (g : Fin k)
   (second :
    PartialEdgeColoring
     E k),
  IsProperEdgeColoring
    G second →
  StableColoring
    X
    (insert
     ch.color C)
    ch.selected
    second →
  g ∈
    MissingColors
     G
     ch.selected
     ch.vertex →
  have post :
   PartialEdgeColoring
    E k :=
   TwoColorComponentSwap
    G second g
    ch.color
    (Sum.inl
     ch.vertex);
  ch.color ∈
    MissingColors
     G post
     ch.vertex ∧
   g ∉
     MissingColors
      G post
      ch.vertex ∧
    g ≠
     ch.color) →
  oldChoice.color ∈
    MissingColors
     G
     (originalPrefix.series.data.coloring
      oldi.succ)
     oldChoice.vertex →
  oldGamma ∉
    MissingColors
     G
     (originalPrefix.series.data.coloring
      oldi.succ)
     oldChoice.vertex →
  oldGamma ≠
    oldChoice.color →
  newChoicePE.color ∈
    MissingColors
     G
     (corr.replacementSeries.data.coloring
      oldi.succ)
     newChoicePE.vertex →
  newGamma ∉
    MissingColors
     G
     (corr.replacementSeries.data.coloring
      oldi.succ)
     newChoicePE.vertex →
  newGamma ≠
    newChoicePE.color →
  MissingColors
     G
     (originalPrefix.series.data.coloring
      oldi.succ)
     oldChoice.vertex =
    MissingColors
     G
     (corr.replacementSeries.data.coloring
      oldi.succ)
     oldChoice.vertex →
  MissingColors
     G
     (originalPrefix.series.data.coloring
      oldi.succ)
     (Eq.symm
        hbaseTree ▸
       oldChoice).vertex =
    MissingColors
     G
     (corr.replacementSeries.data.coloring
      oldi.succ)
     newChoicePE.vertex →
  oldChoiceOnNew.color ∈
    MissingColors
     G
     (originalPrefix.series.data.coloring
      oldi.succ)
     oldChoiceOnNew.vertex →
  oldGamma ∉
    MissingColors
     G
     (originalPrefix.series.data.coloring
      oldi.succ)
     oldChoiceOnNew.vertex →
  newChoicePE.edge =
    oldChoiceOnNew.edge →
  newChoicePE.vertex =
    oldChoiceOnNew.vertex →
  newChoicePE.otherEndpoint =
    oldChoiceOnNew.otherEndpoint →
  newChoicePE.color =
    oldChoiceOnNew.color →
  newGamma =
    oldGamma →
  newChoicePE.color =
    available.delta →
  newGamma =
    available.gamma →
  oldChoice.color =
    available.delta →
  oldGamma =
    available.gamma →
  newChoicePE.vertex =
    oldChoice.vertex →
  newChoicePE.otherEndpoint =
    oldChoice.otherEndpoint →
  (
  ∀
   {rounds' :
    ℕ}
   {input' :
    PartialEdgeColoring
     E
     k}
   (series :
    TashkinovSeries
     G
     k
     rounds'
     e0
     input')
   (j :
    Fin
     rounds'),
  series.data.kind
     j.succ =
    some
     TashkinovExtensionKind.RE →
  series.data.coloring
    j.succ =
   series.data.coloring
    j.castSucc) →
  (
  ∀
   {rounds' :
    ℕ}
   {input' :
    PartialEdgeColoring
     E
     k}
   (series :
    TashkinovSeries
     G
     k
     rounds'
     e0
     input')
   (a
    b :
    Fin
     (rounds' +
      1)),
  (↑a :
     ℕ) ≤
    (↑b :
     ℕ) →
  (
  ∀
   (j :
    Fin
     (rounds' +
      1)),
  (↑a :
     ℕ) <
    (↑j :
     ℕ) →
  (↑j :
     ℕ) ≤
    (↑b :
     ℕ) →
  series.data.kind
    j =
   some
    TashkinovExtensionKind.RE) →
  series.data.coloring
    b =
   series.data.coloring
    a) →
  corr.replacementSeries.data.coloring
     (Fin.last
      originalPrefix.rounds) =
    corr.replacementSeries.data.coloring
     oldi.succ →
  originalPrefix.series.data.coloring
     (Fin.last
      originalPrefix.rounds) =
    originalPrefix.series.data.coloring
     oldi.succ →
  corr.replacementSeries.data.coloring
     oldi.succ =
    sigmaPrev →
  originalPrefix.series.data.coloring
     replacementLast =
    ett.series.data.coloring
     q.castSucc →
  originalPrefix.series.data.coloring
     oldi.succ =
    ett.series.data.coloring
     q.castSucc →
  available.delta ∈
    MissingColors
     G
     sigmaPrev
     newChoicePE.vertex →
  available.gamma ∉
    MissingColors
     G
     sigmaPrev
     newChoicePE.vertex →
  available.delta ∈
    MissingColors
     G
     (ett.series.data.coloring
      (⟨ett.rounds -
          1,
  have
   this :
   1 ≤
    T.length :=
   T.positive;
  Decidable.byContradiction
   fun
    (a :
     ¬ett.rounds -
        1 <
       ett.rounds) ↦
   (by
    omega)⟩ :
        Fin
         ett.rounds).castSucc)
     oldChoice.vertex →
  available.gamma ∉
    MissingColors
     G
     (ett.series.data.coloring
      (⟨ett.rounds -
          1,
  have
   this :
   1 ≤
    T.length :=
   T.positive;
  Decidable.byContradiction
   fun
    (a :
     ¬ett.rounds -
        1 <
       ett.rounds) ↦
   (by
    omega)⟩ :
        Fin
         ett.rounds).castSucc)
     oldChoice.vertex →
  available.gamma ≠
    available.delta →
  (
  ∀
   (r :
    Fin
     originalPrefix.rounds),
  TreeSequenceInitialSegment
   (originalPrefix.series.data.tree
    r.succ.castSucc)
   (originalPrefix.series.data.tree
    r.succ.succ)) →
  (
  ∀
   (A
    B
    C :
    TreeSequence
     G
     e0),
  TreeSequenceInitialSegment
    A
    B →
  TreeSequenceInitialSegment
    B
    C →
  TreeSequenceInitialSegment
   A
   C) →
  (
  ∀
   (d :
    ℕ)
   (idx :
    Fin
     (originalPrefix.rounds +
      2)),
  (↑idx :
      ℕ) +
     d =
    originalPrefix.rounds +
     1 →
  1 ≤
    (↑idx :
     ℕ) →
  TreeSequenceInitialSegment
   (originalPrefix.series.data.tree
    idx)
   (originalPrefix.series.data.tree
    (Fin.last
     (originalPrefix.rounds +
      1)))) →
  False

private abbrev helperBranch280Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds)
   (_ :
    (
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
  {generating' : PartialEdgeColoring E k}
  (lower : ExtendedTashkinovTree G k e0 input' T' generating') (_ : (0 : ℕ) < lower.rounds)
  (_ : lower.rounds < ett.rounds) (_ : MaximumProperty lower),
  (
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tnext : TreeSequence G e0 := lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ)));
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tnext (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ (alpha beta : Fin k),
  alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma Tnext →
  TreeInterchangeable G Tnext sigma alpha beta) ∧
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc;
  ∀ (v : V) (gamma delta : Fin k),
  lower.series.data.kind n = some TashkinovExtensionKind.PE →
  lower.series.data.chosenVertex n = some v →
  lower.series.data.gamma n = some gamma →
  lower.series.data.delta n = some delta →
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tn (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ w ∈ TreeSequenceVertexSet Tn,
   Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔ w = v))
   (sigmaPrev : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G sigmaPrev)
   (_ : IsOneEdgeUncolored sigmaPrev e0)
   (_ :
    IsProperEdgeColoring G
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (_ :
    IsOneEdgeUncolored
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc) e0)
   (_ :
    StableColoring
     (ett.series.data.tree (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).succ.castSucc)
     (TashkinovStoredColors ett.series.data
      (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
          ett.rounds).castSucc)
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc)
     sigmaPrev)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (_ : MaximumProperty originalPrefix)
   (_ :
    (
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i)))
   (_ :
    (
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i = ett.series.data.coloring (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
   originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
     originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i)))
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc))
   (_ : corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev)
   (_ : MaximumProperty corr.replacementETT)
   (_ :
    ¬Nonempty
      (RevisitingExtensionCertificate ett.series.data
       (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
           ett.rounds).castSucc))
   (_ :
    ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
        ett.rounds) : Fin ett.rounds).succ =
     Fin.last ett.rounds)
   (_ : (0 : ℕ) < originalPrefix.rounds)
   (_ :
    Fin.castLE
      (Decidable.byContradiction fun (a : ¬originalPrefix.rounds + (1 : ℕ) ≤ ett.rounds + (1 : ℕ)) ↦
       by omega)
      (Fin.last originalPrefix.rounds : Fin (originalPrefix.rounds + (1 : ℕ))) =
     ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
         ett.rounds) : Fin ett.rounds).castSucc)
   (_ :
    corr.replacementSeries.data.tree
      (Fin.last originalPrefix.rounds : Fin (originalPrefix.rounds + (1 : ℕ))).succ =
     ett.series.data.tree
      ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
          ett.rounds) : Fin ett.rounds).succ.castSucc)
   (_ :
    originalPrefix.series.data.tree
      (Fin.last originalPrefix.rounds : Fin (originalPrefix.rounds + (1 : ℕ))).castSucc =
     ett.series.data.tree
      ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
          ett.rounds) : Fin ett.rounds).castSucc.castSucc)
   (_ :
    (
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
  {generating' : PartialEdgeColoring E k}
  (base : ExtendedTashkinovTree G k e0 input' T' generating') (_ : (0 : ℕ) < base.rounds)
  (_ : base.rounds < ett.rounds) (_ : MaximumProperty base) (r : ℕ)
  (series : TashkinovSeries G k r e0 input') (_ : base.rounds = r) (_ : base.series ≍ series)
  (a : Fin (r + (1 : ℕ))) (v : V) (gamma delta : Fin k) (_ : (0 : ℕ) < (↑a : ℕ))
  (_ : series.data.kind a = some TashkinovExtensionKind.PE)
  (_ : series.data.chosenVertex a = some v) (_ : series.data.gamma a = some gamma)
  (_ : series.data.delta a = some delta) (_ : IsProperEdgeColoring G (series.data.coloring a))
  (_ : IsOneEdgeUncolored (series.data.coloring a) e0),
  ∀ w ∈ TreeSequenceVertexSet (series.data.tree a.castSucc),
   Sum.inl w ∈ TwoColorComponent G (series.data.coloring a) gamma delta (Sum.inl v) ↔ w = v))
   (available :
    RevisitingExtensionCertificate corr.replacementSeries.data (Fin.last originalPrefix.rounds))
   (_ : (0 : ℕ) < (↑(available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) : ℕ))
   (_ :
    originalPrefix.series.data.kind (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) =
     some TashkinovExtensionKind.PE)
   (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k)
   (_ :
    ParallelExtensionColor originalPrefix.series.data oldi.castSucc oldChoice.selected
     oldChoice.vertex oldGamma)
   (oldSecond : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G oldSecond)
   (_ :
    StableColoring (originalPrefix.series.data.tree oldi.succ.castSucc)
     (insert oldChoice.color (TashkinovStoredColors originalPrefix.series.data oldi.castSucc))
     oldChoice.selected oldSecond)
   (_ :
    originalPrefix.series.data.coloring oldi.succ =
     TwoColorComponentSwap G oldSecond oldGamma oldChoice.color (Sum.inl oldChoice.vertex))
   (_ : IsProperEdgeColoring G (originalPrefix.series.data.coloring oldi.succ))
   (_ : IsOneEdgeUncolored (originalPrefix.series.data.coloring oldi.succ) e0)
   (_ : originalPrefix.series.data.stored oldi.succ = { oldChoice.color, oldGamma })
   (_ : originalPrefix.series.data.connectingEdges oldi.succ = { oldChoice.edge })
   (_ : originalPrefix.series.data.kind oldi.succ = some TashkinovExtensionKind.PE)
   (_ : originalPrefix.series.data.chosenVertex oldi.succ = some oldChoice.vertex)
   (_ : originalPrefix.series.data.delta oldi.succ = some oldChoice.color)
   (_ : originalPrefix.series.data.gamma oldi.succ = some oldGamma)
   (_ : (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) = oldi.succ),
  False

private abbrev helperHtreePrefixFull719Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds)
   (sigmaPrev : PartialEdgeColoring E k)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
  (
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc))
   (available :
    RevisitingExtensionCertificate corr.replacementSeries.data (Fin.last originalPrefix.rounds)),
  ∀ (oldi : Fin originalPrefix.rounds)
   (_ :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (_ : Fin k),
  (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) = oldi.succ →
  oldi.succ = (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) →
  ∀ (_ : originalPrefix.rounds < ett.rounds),
  ∀ (fulli : Fin ett.rounds),
  fulli.succ =
    (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) (available.earlier : Fin
          (originalPrefix.rounds + (1 : ℕ))) :
     Fin (ett.rounds + (1 : ℕ))) →
  originalPrefix.series.data.tree oldi.succ.castSucc =
   ett.series.data.tree fulli.succ.castSucc

private abbrev helperBranch3084Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
   (⟨ett.rounds - (1 : ℕ), by
     have := GoldbergSeymour.TreeSequence.positive T
     omega⟩ :
    Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - (1 : ℕ),
         by
         have := GoldbergSeymour.TreeSequence.positive T
         omega⟩ :
        Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
  (
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i =
   ett.series.data.tree
    (Fin.castLE
     (by
      have := GoldbergSeymour.TreeSequence.positive T
      omega)
     i)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i =
    ett.series.data.coloring
     (Fin.castLE
      (by
       have := GoldbergSeymour.TreeSequence.positive T
       omega)
      i) ∧
   originalPrefix.series.data.stored i =
     ett.series.data.stored
      (Fin.castLE
       (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
       i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges
       (Fin.castLE
        (by
         have := GoldbergSeymour.TreeSequence.positive T
         omega)
        i) ∧
     originalPrefix.series.data.kind i =
       ett.series.data.kind
        (Fin.castLE
         (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
         i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data
        (Fin.castLE
         (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
         i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  ¬Nonempty
     (RevisitingExtensionCertificate ett.series.data
      (⟨ett.rounds - (1 : ℕ),
         by
         have := GoldbergSeymour.TreeSequence.positive T
         omega⟩ :
        Fin ett.rounds).castSucc) →
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) :=
   Fin.last originalPrefix.rounds;
  Fin.castLE
     (by
      have := GoldbergSeymour.TreeSequence.positive T
      omega)
     replacementLast =
    (⟨ett.rounds - (1 : ℕ),
       by
       have := GoldbergSeymour.TreeSequence.positive T
       omega⟩ :
      Fin ett.rounds).castSucc →
  corr.replacementSeries.data.tree replacementLast.succ =
    ett.series.data.tree
     (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
       Fin ett.rounds).succ.castSucc →
  ∀
   (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  originalPrefix.series.data.stored oldi.succ =
    (insert oldChoice.color ({ oldGamma } : Finset (Fin k)) : Finset (Fin k)) →
  originalPrefix.series.data.connectingEdges oldi.succ =
    ({ oldChoice.edge } : Finset E) →
  earlierPrefix = oldi.succ →
  oldi.succ = earlierPrefix →
  ∀ (newGamma : Fin k)
   (newChoicePE :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
     (corr.replacementSeries.data.coloring oldi.castSucc))
   (hbaseTree :
    corr.replacementSeries.data.tree oldi.succ.castSucc =
     originalPrefix.series.data.tree oldi.succ.castSucc),
  (
  ∀ {A B : TreeSequence G e0} (hAB : A = B) (C : Finset (Fin k))
   (phi : PartialEdgeColoring E k) (ch : MaximumDefectiveChoice G e0 A C phi),
  (@Eq.rec (@TreeSequence V E G e0) A
      (fun (x : @TreeSequence V E G e0) (h : @Eq (@TreeSequence V E G e0) A x) ↦
       @MaximumDefectiveChoice V E inst inst_1 G k e0 x C phi)
      ch B hAB).edge =
    ch.edge ∧
   (@Eq.rec (@TreeSequence V E G e0) A
       (fun (x : @TreeSequence V E G e0) (h : @Eq (@TreeSequence V E G e0) A x) ↦
        @MaximumDefectiveChoice V E inst inst_1 G k e0 x C phi)
       ch B hAB).vertex =
     ch.vertex ∧
    (@Eq.rec (@TreeSequence V E G e0) A
        (fun (x : @TreeSequence V E G e0) (h : @Eq (@TreeSequence V E G e0) A x) ↦
         @MaximumDefectiveChoice V E inst inst_1 G k e0 x C phi)
        ch B hAB).otherEndpoint =
      ch.otherEndpoint ∧
     (@Eq.rec (@TreeSequence V E G e0) A
        (fun (x : @TreeSequence V E G e0) (h : @Eq (@TreeSequence V E G e0) A x) ↦
         @MaximumDefectiveChoice V E inst inst_1 G k e0 x C phi)
        ch B hAB).color =
      ch.color) →
  (
  ∀ (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
   (ch : MaximumDefectiveChoice G e0 X C phi) (g : Fin k)
   (second : PartialEdgeColoring E k),
  IsProperEdgeColoring G second →
  StableColoring X (insert ch.color C : Finset (Fin k)) ch.selected second →
  g ∈ MissingColors G ch.selected ch.vertex →
  let post : PartialEdgeColoring E k :=
   TwoColorComponentSwap G second g ch.color (Sum.inl ch.vertex);
  ch.color ∈ MissingColors G post ch.vertex ∧
   g ∉ MissingColors G post ch.vertex ∧ g ≠ ch.color) →
  oldChoice.color ∈
    MissingColors G (originalPrefix.series.data.coloring oldi.succ)
     oldChoice.vertex →
  oldGamma ∉
    MissingColors G (originalPrefix.series.data.coloring oldi.succ)
     oldChoice.vertex →
  oldChoice.color = available.delta →
  oldGamma = available.gamma →
  available.returnVertex ∈
    TreeSequenceVertexSet
     (originalPrefix.series.data.tree earlierPrefix.castSucc) →
  let originalReturnGraph : SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc)
    available.gamma available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges, edge ∈ originalReturnGraph.edgeSet),
  let originalReturnPath :
   originalReturnGraph.Walk (Sum.inr available.edge)
    (Sum.inl available.returnVertex) :=
   available.returnPath.transfer originalReturnGraph returnEdgeTransfer;
  originalReturnPath.IsPath →
  (
  ∀ (z : V ⊕ E),
  z ∈ originalReturnPath.support ↔ z ∈ available.returnPath.support) →
  Sum.inl available.returnVertex ∈
    TwoColorComponent G (ett.series.data.coloring q.castSucc)
     available.gamma available.delta (Sum.inr available.edge) →
  Sum.inl available.outsideEndpoint ∈
    TwoColorComponent G (ett.series.data.coloring q.castSucc)
     available.gamma available.delta (Sum.inr available.edge) →
  ∀ (horiginalRoundsLess : originalPrefix.rounds < ett.rounds)
   (originalCycle :
    TwoColorCycle G (ett.series.data.coloring q.castSucc) available.gamma
     available.delta),
  (
  ∀ (x : V ⊕ E),
  x ∈ originalCycle.walk.support ↔
   x ∈
    TwoColorComponent G (ett.series.data.coloring q.castSucc)
     available.gamma available.delta (Sum.inr available.edge)) →
  let oldEarlier : Fin (ett.rounds + (1 : ℕ)) :=
   Fin.castLE
    (by
     have := GoldbergSeymour.TreeSequence.positive T
     omega)
    earlierPrefix;
  ett.series.data.kind oldEarlier = some TashkinovExtensionKind.PE →
  ∀ (fulli : Fin ett.rounds)
   (fullChoice :
    MaximumDefectiveChoice G e0
     (ett.series.data.tree fulli.succ.castSucc)
     (TashkinovStoredColors ett.series.data fulli.castSucc)
     (ett.series.data.coloring fulli.castSucc))
   (fullGamma : Fin k),
  ParallelExtensionColor ett.series.data fulli.castSucc
    fullChoice.selected fullChoice.vertex fullGamma →
  ∀ (fullSecond : PartialEdgeColoring E k),
  IsProperEdgeColoring G fullSecond →
  StableColoring (ett.series.data.tree fulli.succ.castSucc)
    (insert fullChoice.color
      (TashkinovStoredColors ett.series.data fulli.castSucc) :
     Finset (Fin k))
    fullChoice.selected fullSecond →
  ett.series.data.coloring fulli.succ =
    TwoColorComponentSwap G fullSecond fullGamma fullChoice.color
     (Sum.inl fullChoice.vertex) →
  ett.series.data.stored fulli.succ =
    (insert fullChoice.color ({ fullGamma } : Finset (Fin k)) :
     Finset (Fin k)) →
  ett.series.data.connectingEdges fulli.succ =
    ({ fullChoice.edge } : Finset E) →
  ett.series.data.delta fulli.succ = some fullChoice.color →
  ett.series.data.gamma fulli.succ = some fullGamma →
  oldEarlier = fulli.succ →
  False

private abbrev helperHoriginalPathInQ1511Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
   (⟨ett.rounds - (1 : ℕ), by
     have := GoldbergSeymour.TreeSequence.positive T
     omega⟩ :
    Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring
      (⟨ett.rounds - (1 : ℕ),
         by
         have := GoldbergSeymour.TreeSequence.positive T
         omega⟩ :
        Fin ett.rounds).castSucc))
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let originalReturnGraph : SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.gamma
    available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges, edge ∈ originalReturnGraph.edgeSet),
  let originalReturnPath :
   originalReturnGraph.Walk (Sum.inr available.edge) (Sum.inl available.returnVertex) :=
   available.returnPath.transfer originalReturnGraph returnEdgeTransfer;
  ∀ z ∈ originalReturnPath.support,
   z ∈
    TwoColorComponent G (ett.series.data.coloring q.castSucc) available.gamma available.delta
     (Sum.inr available.edge)

private abbrev helperContinuation1990Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
      hroundLarge⟩ : Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
   (_ :
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i))
   (_ :
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i = ett.series.data.coloring (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
   originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
     originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i))
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc))
   (_ :
    ¬Nonempty
      (RevisitingExtensionCertificate ett.series.data
       (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
           ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀
   (_ :
    Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) replacementLast =
     (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
         ett.rounds).castSucc)
   (_ :
    corr.replacementSeries.data.tree replacementLast.succ =
     ett.series.data.tree (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).succ.castSucc)
   (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k) (_ : oldChoice.color = available.delta)
   (_ : oldGamma = available.gamma)
   (_ :
    available.returnVertex ∈
     TreeSequenceVertexSet (originalPrefix.series.data.tree earlierPrefix.castSucc)),
  let originalReturnGraph : SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.gamma
    available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges, edge ∈ originalReturnGraph.edgeSet),
  let originalReturnPath :
   originalReturnGraph.Walk (Sum.inr available.edge) (Sum.inl available.returnVertex) :=
   available.returnPath.transfer originalReturnGraph returnEdgeTransfer;
  ∀ (_ : originalReturnPath.IsPath)
   (_ :
  ∀ (z : V ⊕ E),
  z ∈ originalReturnPath.support ↔ z ∈ available.returnPath.support)
   (_ :
    Sum.inl available.returnVertex ∈
     TwoColorComponent G
      (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
          hroundLarge⟩ : Fin ett.rounds).castSucc)
      available.gamma available.delta (Sum.inr available.edge))
   (_ :
    Sum.inl available.outsideEndpoint ∈
     TwoColorComponent G
      (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
          hroundLarge⟩ : Fin ett.rounds).castSucc)
      available.gamma available.delta (Sum.inr available.edge))
   (_ : originalPrefix.rounds < ett.rounds)
   (originalCycle :
    TwoColorCycle G
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc)
     available.gamma available.delta)
   (_ :
  ∀ (x : V ⊕ E),
  x ∈ originalCycle.walk.support ↔
   x ∈
    TwoColorComponent G
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc)
     available.gamma available.delta (Sum.inr available.edge)),
  let oldEarlier : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) earlierPrefix;
  ∀ (_ : ett.series.data.kind oldEarlier = some TashkinovExtensionKind.PE)
   (fulli : Fin ett.rounds)
   (fullChoice :
    MaximumDefectiveChoice G e0 (ett.series.data.tree fulli.succ.castSucc)
     (TashkinovStoredColors ett.series.data fulli.castSucc)
     (ett.series.data.coloring fulli.castSucc))
   (fullGamma : Fin k)
   (_ : ett.series.data.delta fulli.succ = some fullChoice.color)
   (_ : ett.series.data.gamma fulli.succ = some fullGamma)
   (_ : fulli.succ = oldEarlier)
   (htreePrefixFull :
    originalPrefix.series.data.tree oldi.succ.castSucc =
     ett.series.data.tree fulli.succ.castSucc),
  let prefixChoiceOnFull :
   MaximumDefectiveChoice G e0 (ett.series.data.tree fulli.succ.castSucc)
    (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc) :=
   (htreePrefixFull ▸ oldChoice);
  ∀ (_ : prefixChoiceOnFull.color = oldChoice.color)
   (_ :
    ({ prefixChoiceOnFull.edge } : Finset E) = ({ fullChoice.edge } : Finset E))
   (_ :
    (insert prefixChoiceOnFull.color ({ oldGamma } : Finset (Fin k)) : Finset (Fin k)) =
     (insert fullChoice.color ({ fullGamma } : Finset (Fin k)) : Finset (Fin k)))
   (_ :
    fullChoice.color ∈
     MissingColors G (ett.series.data.coloring fulli.succ) fullChoice.vertex)
   (_ :
    fullGamma ∉ MissingColors G (ett.series.data.coloring fulli.succ) fullChoice.vertex)
   (_ :
    MissingColors G (originalPrefix.series.data.coloring oldi.succ)
      prefixChoiceOnFull.vertex =
     MissingColors G (ett.series.data.coloring fulli.succ) fullChoice.vertex)
   (_ :
    prefixChoiceOnFull.color ∈
     MissingColors G (originalPrefix.series.data.coloring oldi.succ)
      prefixChoiceOnFull.vertex)
   (_ :
    oldGamma ∉
     MissingColors G (originalPrefix.series.data.coloring oldi.succ)
      prefixChoiceOnFull.vertex),
  False

private abbrev helperBranch1721Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds),
  ∀ (sigmaPrev : PartialEdgeColoring E k)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
  (
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i = ett.series.data.coloring (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
   originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
     originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  ¬Nonempty
     (RevisitingExtensionCertificate ett.series.data
      (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
          ett.rounds).castSucc) →
  Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr)
     (Fin.last originalPrefix.rounds : Fin (originalPrefix.rounds + (1 : ℕ))) =
    ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
        ett.rounds) : Fin ett.rounds).castSucc →
  corr.replacementSeries.data.tree
     (Fin.last originalPrefix.rounds : Fin (originalPrefix.rounds + (1 : ℕ))).succ =
    ett.series.data.tree
     ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
         ett.rounds) : Fin ett.rounds).succ.castSucc →
  ∀
   (available :
    RevisitingExtensionCertificate corr.replacementSeries.data
     (Fin.last originalPrefix.rounds)),
  ∀ (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k),
  originalPrefix.series.data.stored oldi.succ =
    (insert oldChoice.color ({ oldGamma } : Finset (Fin k)) : Finset (Fin k)) →
  originalPrefix.series.data.connectingEdges oldi.succ =
    ({ oldChoice.edge } : Finset E) →
  (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) = oldi.succ →
  oldi.succ = (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) →
  ∀ (_ : Fin k)
   (_ :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
     (corr.replacementSeries.data.coloring oldi.castSucc))
   (_ :
    corr.replacementSeries.data.tree oldi.succ.castSucc =
     originalPrefix.series.data.tree oldi.succ.castSucc),
  (
  ∀ {A B : TreeSequence G e0} (hAB : A = B) (C : Finset (Fin k))
   (phi : PartialEdgeColoring E k) (ch : MaximumDefectiveChoice G e0 A C phi),
  (@Eq.rec (@TreeSequence V E G e0) A
      (fun (x : @TreeSequence V E G e0) (_ : @Eq (@TreeSequence V E G e0) A x) ↦
       @MaximumDefectiveChoice V E inst inst_1 G k e0 x C phi)
      ch B hAB).edge =
    ch.edge ∧
   (@Eq.rec (@TreeSequence V E G e0) A
       (fun (x : @TreeSequence V E G e0) (_ : @Eq (@TreeSequence V E G e0) A x) ↦
        @MaximumDefectiveChoice V E inst inst_1 G k e0 x C phi)
       ch B hAB).vertex =
     ch.vertex ∧
    (@Eq.rec (@TreeSequence V E G e0) A
        (fun (x : @TreeSequence V E G e0) (_ : @Eq (@TreeSequence V E G e0) A x) ↦
         @MaximumDefectiveChoice V E inst inst_1 G k e0 x C phi)
        ch B hAB).otherEndpoint =
      ch.otherEndpoint ∧
     (@Eq.rec (@TreeSequence V E G e0) A
        (fun (x : @TreeSequence V E G e0) (_ : @Eq (@TreeSequence V E G e0) A x) ↦
         @MaximumDefectiveChoice V E inst inst_1 G k e0 x C phi)
        ch B hAB).color =
      ch.color) →
  (
  ∀ (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
   (ch : MaximumDefectiveChoice G e0 X C phi) (g : Fin k)
   (second : PartialEdgeColoring E k),
  IsProperEdgeColoring G second →
  StableColoring X (insert ch.color C : Finset (Fin k)) ch.selected second →
  g ∈ MissingColors G ch.selected ch.vertex →
  let post : PartialEdgeColoring E k :=
   TwoColorComponentSwap G second g ch.color (Sum.inl ch.vertex);
  ch.color ∈ MissingColors G post ch.vertex ∧
   g ∉ MissingColors G post ch.vertex ∧ g ≠ ch.color) →
  oldChoice.color ∈
    MissingColors G (originalPrefix.series.data.coloring oldi.succ)
     oldChoice.vertex →
  oldGamma ∉
    MissingColors G (originalPrefix.series.data.coloring oldi.succ)
     oldChoice.vertex →
  oldChoice.color = available.delta →
  oldGamma = available.gamma →
  available.returnVertex ∈
    TreeSequenceVertexSet
     (originalPrefix.series.data.tree
      (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))).castSucc) →
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges,
     edge ∈
      (TwoColorIncidenceGraph G
         (ett.series.data.coloring
          ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
              ett.rounds) :
            Fin ett.rounds).castSucc)
         available.gamma available.delta :
        SimpleGraph (V ⊕ E)).edgeSet),
  (available.returnPath.transfer
      (TwoColorIncidenceGraph G
        (ett.series.data.coloring
         ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
             ett.rounds) :
           Fin ett.rounds).castSucc)
        available.gamma available.delta :
       SimpleGraph (V ⊕ E))
      returnEdgeTransfer :
     (TwoColorIncidenceGraph G
         (ett.series.data.coloring
          ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
              ett.rounds) :
            Fin ett.rounds).castSucc)
         available.gamma available.delta :
        SimpleGraph (V ⊕ E)).Walk
      (Sum.inr available.edge) (Sum.inl available.returnVertex)).IsPath →
  (
  ∀ (z : V ⊕ E),
  z ∈
    (available.returnPath.transfer
       (TwoColorIncidenceGraph G
         (ett.series.data.coloring
          ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
              ett.rounds) :
            Fin ett.rounds).castSucc)
         available.gamma available.delta :
        SimpleGraph (V ⊕ E))
       returnEdgeTransfer :
      (TwoColorIncidenceGraph G
          (ett.series.data.coloring
           ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
               ett.rounds) :
             Fin ett.rounds).castSucc)
          available.gamma available.delta :
         SimpleGraph (V ⊕ E)).Walk
       (Sum.inr available.edge)
       (Sum.inl available.returnVertex)).support ↔
   z ∈ available.returnPath.support) →
  Sum.inl available.returnVertex ∈
    TwoColorComponent G
     (ett.series.data.coloring
      ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
          ett.rounds) :
        Fin ett.rounds).castSucc)
     available.gamma available.delta (Sum.inr available.edge) →
  Sum.inl available.outsideEndpoint ∈
    TwoColorComponent G
     (ett.series.data.coloring
      ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
          ett.rounds) :
        Fin ett.rounds).castSucc)
     available.gamma available.delta (Sum.inr available.edge) →
  ∀ (_ : originalPrefix.rounds < ett.rounds)
   (originalCycle :
    TwoColorCycle G
     (ett.series.data.coloring
      ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
          ett.rounds) :
        Fin ett.rounds).castSucc)
     available.gamma available.delta),
  (
  ∀ (x : V ⊕ E),
  x ∈ originalCycle.walk.support ↔
   x ∈
    TwoColorComponent G
     (ett.series.data.coloring
      ((⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
          ett.rounds) :
        Fin ett.rounds).castSucc)
     available.gamma available.delta (Sum.inr available.edge)) →
  ett.series.data.kind
     (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr)
       (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) :
      Fin (ett.rounds + (1 : ℕ))) =
    some TashkinovExtensionKind.PE →
  ∀ (fulli : Fin ett.rounds)
   (fullChoice :
    MaximumDefectiveChoice G e0
     (ett.series.data.tree fulli.succ.castSucc)
     (TashkinovStoredColors ett.series.data fulli.castSucc)
     (ett.series.data.coloring fulli.castSucc))
   (fullGamma : Fin k),
  ParallelExtensionColor ett.series.data fulli.castSucc
    fullChoice.selected fullChoice.vertex fullGamma →
  ∀ (fullSecond : PartialEdgeColoring E k),
  IsProperEdgeColoring G fullSecond →
  StableColoring (ett.series.data.tree fulli.succ.castSucc)
    (insert fullChoice.color
      (TashkinovStoredColors ett.series.data fulli.castSucc) :
     Finset (Fin k))
    fullChoice.selected fullSecond →
  ett.series.data.coloring fulli.succ =
    TwoColorComponentSwap G fullSecond fullGamma fullChoice.color
     (Sum.inl fullChoice.vertex) →
  ett.series.data.stored fulli.succ =
    (insert fullChoice.color ({ fullGamma } : Finset (Fin k)) :
     Finset (Fin k)) →
  ett.series.data.connectingEdges fulli.succ =
    ({ fullChoice.edge } : Finset E) →
  ett.series.data.delta fulli.succ = some fullChoice.color →
  ett.series.data.gamma fulli.succ = some fullGamma →
  (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr)
      (available.earlier :
       Fin (originalPrefix.rounds + (1 : ℕ))) :
     Fin (ett.rounds + (1 : ℕ))) =
    fulli.succ →
  False

private abbrev helperPePostStatus3432Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
   (e0 : E) (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
   (ch : MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
  IsProperEdgeColoring G second →
  StableColoring X (insert ch.color C : Finset (Fin k)) ch.selected second →
  g ∈ MissingColors G ch.selected ch.vertex →
  let post : PartialEdgeColoring E k :=
   TwoColorComponentSwap G second g ch.color (Sum.inl ch.vertex);
  ch.color ∈ MissingColors G post ch.vertex ∧ g ∉ MissingColors G post ch.vertex ∧ g ≠ ch.color

private abbrev helperContinuation4070Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds)
   (_ :
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
  (0 : ℕ) < lower.rounds →
  lower.rounds < ett.rounds →
  MaximumProperty lower →
  (
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tnext : TreeSequence G e0 :=
   lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ)));
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tnext (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ (alpha beta : Fin k),
  alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma Tnext →
  TreeInterchangeable G Tnext sigma alpha beta) ∧
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc;
  ∀ (v : V) (gamma delta : Fin k),
  lower.series.data.kind n = some TashkinovExtensionKind.PE →
  lower.series.data.chosenVertex n = some v →
  lower.series.data.gamma n = some gamma →
  lower.series.data.delta n = some delta →
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tn (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ w ∈ TreeSequenceVertexSet Tn,
   Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔ w = v),
  let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
      hroundLarge⟩ : Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
   (_ :
    IsProperEdgeColoring G
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (_ :
    IsOneEdgeUncolored
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc) e0)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (_ : MaximumProperty originalPrefix)
   (_ :
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i))
   (_ :
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i = ett.series.data.coloring (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
   originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
     originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i))
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc))
   (_ : MaximumProperty corr.replacementETT)
   (_ :
    ¬Nonempty
      (RevisitingExtensionCertificate ett.series.data
       (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
           ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (_ : (0 : ℕ) < originalPrefix.rounds)
   (_ :
    Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) replacementLast =
     (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
         ett.rounds).castSucc)
   (_ :
    corr.replacementSeries.data.tree replacementLast.succ =
     ett.series.data.tree (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).succ.castSucc)
   (_ :
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (base : ExtendedTashkinovTree G k e0 input' T' generating'),
  (0 : ℕ) < base.rounds →
  base.rounds < ett.rounds →
  MaximumProperty base →
  ∀ (r : ℕ) (series : TashkinovSeries G k r e0 input'),
  base.rounds = r →
  base.series ≍ series →
  ∀ (a : Fin (r + (1 : ℕ))) (v : V) (gamma delta : Fin k),
  (0 : ℕ) < (↑a : ℕ) →
  series.data.kind a = some TashkinovExtensionKind.PE →
  series.data.chosenVertex a = some v →
  series.data.gamma a = some gamma →
  series.data.delta a = some delta →
  IsProperEdgeColoring G (series.data.coloring a) →
  IsOneEdgeUncolored (series.data.coloring a) e0 →
  ∀ w ∈ TreeSequenceVertexSet (series.data.tree a.castSucc),
   Sum.inl w ∈
     TwoColorComponent G (series.data.coloring a) gamma delta (Sum.inl v) ↔
    w = v)
   (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀
   (_ :
    originalPrefix.series.data.kind earlierPrefix = some TashkinovExtensionKind.PE)
   (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k)
   (_ : IsProperEdgeColoring G (originalPrefix.series.data.coloring oldi.succ))
   (_ : IsOneEdgeUncolored (originalPrefix.series.data.coloring oldi.succ) e0)
   (_ :
    originalPrefix.series.data.stored oldi.succ =
     (insert oldChoice.color ({ oldGamma } : Finset (Fin k)) : Finset (Fin k)))
   (_ :
    originalPrefix.series.data.connectingEdges oldi.succ = ({ oldChoice.edge } : Finset E))
   (_ : originalPrefix.series.data.kind oldi.succ = some TashkinovExtensionKind.PE)
   (_ : originalPrefix.series.data.chosenVertex oldi.succ = some oldChoice.vertex)
   (_ : originalPrefix.series.data.delta oldi.succ = some oldChoice.color)
   (_ : originalPrefix.series.data.gamma oldi.succ = some oldGamma)
   (_ : earlierPrefix = oldi.succ) (_ : oldi.succ = earlierPrefix)
   (newGamma : Fin k)
   (newChoicePE :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
     (corr.replacementSeries.data.coloring oldi.castSucc))
   (_ : IsProperEdgeColoring G (corr.replacementSeries.data.coloring oldi.succ))
   (_ : IsOneEdgeUncolored (corr.replacementSeries.data.coloring oldi.succ) e0)
   (_ : corr.replacementSeries.data.kind oldi.succ = some TashkinovExtensionKind.PE)
   (_ :
    corr.replacementSeries.data.chosenVertex oldi.succ = some newChoicePE.vertex)
   (_ : corr.replacementSeries.data.delta oldi.succ = some newChoicePE.color)
   (_ : corr.replacementSeries.data.gamma oldi.succ = some newGamma)
   (hbaseTree :
    corr.replacementSeries.data.tree oldi.succ.castSucc =
     originalPrefix.series.data.tree oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc) :=
   (Eq.symm hbaseTree ▸ oldChoice);
  ∀
   (_ :
  ∀ {A B : TreeSequence G e0} (hAB : A = B) (C : Finset (Fin k))
   (phi : PartialEdgeColoring E k) (ch : MaximumDefectiveChoice G e0 A C phi),
  (hAB ▸ ch).edge = ch.edge ∧
   (hAB ▸ ch).vertex = ch.vertex ∧
    (hAB ▸ ch).otherEndpoint = ch.otherEndpoint ∧ (hAB ▸ ch).color = ch.color)
   (_ : oldChoiceOnNew.color = oldChoice.color)
   (_ :
  ∀ (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
   (ch : MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
  IsProperEdgeColoring G second →
  StableColoring X (insert ch.color C : Finset (Fin k)) ch.selected second →
  g ∈ MissingColors G ch.selected ch.vertex →
  let post : PartialEdgeColoring E k :=
   TwoColorComponentSwap G second g ch.color (Sum.inl ch.vertex);
  ch.color ∈ MissingColors G post ch.vertex ∧
   g ∉ MissingColors G post ch.vertex ∧ g ≠ ch.color)
   (_ :
    oldChoice.color ∈
     MissingColors G (originalPrefix.series.data.coloring oldi.succ) oldChoice.vertex)
   (_ :
    oldGamma ∉ MissingColors G (originalPrefix.series.data.coloring oldi.succ) oldChoice.vertex)
   (_ : oldGamma ≠ oldChoice.color) (_ : newGamma ≠ newChoicePE.color)
   (_ : newChoicePE.color = oldChoiceOnNew.color)
   (_ : newGamma = oldGamma)
   (_ : newChoicePE.color = available.delta)
   (_ : newGamma = available.gamma)
   (_ : oldChoice.color = available.delta)
   (_ : oldGamma = available.gamma)
   (_ : newChoicePE.vertex = oldChoice.vertex)
   (_ : corr.replacementSeries.data.coloring oldi.succ = sigmaPrev)
   (_ :
    originalPrefix.series.data.coloring replacementLast = ett.series.data.coloring q.castSucc)
   (_ :
    originalPrefix.series.data.coloring oldi.succ = ett.series.data.coloring q.castSucc)
   (_ :
    available.delta ∈ MissingColors G (ett.series.data.coloring q.castSucc) oldChoice.vertex)
   (_ : available.gamma ≠ available.delta)
   (_ :
    oldChoice.vertex ∈
     TreeSequenceVertexSet
      (originalPrefix.series.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ)))))
   (_ :
    available.returnVertex ∈
     TreeSequenceVertexSet (originalPrefix.series.data.tree earlierPrefix.castSucc))
   (_ :
    available.returnVertex ∈
     TreeSequenceVertexSet
      (originalPrefix.series.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ))))),
  let originalReturnGraph : SimpleGraph (V ⊕ E) :=
   TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.gamma
    available.delta;
  ∀
   (returnEdgeTransfer :
    ∀ edge ∈ available.returnPath.edges, edge ∈ originalReturnGraph.edgeSet),
  let originalReturnPath :
   originalReturnGraph.Walk (Sum.inr available.edge) (Sum.inl available.returnVertex) :=
   available.returnPath.transfer originalReturnGraph returnEdgeTransfer;
  ∀ (_ : originalReturnPath.IsPath)
   (_ :
  ∀ (z : V ⊕ E),
  z ∈ originalReturnPath.support ↔ z ∈ available.returnPath.support)
   (_ :
    Sum.inl available.returnVertex ∈
     TwoColorComponent G (ett.series.data.coloring q.castSucc) available.gamma available.delta
      (Sum.inr available.edge))
   (_ :
    Sum.inl available.outsideEndpoint ∈
     TwoColorComponent G (ett.series.data.coloring q.castSucc) available.gamma available.delta
      (Sum.inr available.edge))
   (_ :
    TwoColorNontrivialPathComponent G (ett.series.data.coloring q.castSucc) available.gamma
     available.delta (Sum.inl oldChoice.vertex))
   (_ :
    ∃
     v ∈
      TreeSequenceVertexSet
       (originalPrefix.series.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ)))),
     Sum.inl v ∈
      TwoColorComponent G (ett.series.data.coloring q.castSucc) available.gamma
       available.delta (Sum.inl oldChoice.vertex))
   (_ :
    ((TwoColorIncidenceGraph G (corr.replacementSeries.data.coloring replacementLast)
        available.gamma available.delta).neighborSet
      (Sum.inl newChoicePE.vertex)).Subsingleton),
  False

private abbrev helperContinuation4611Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) < ett.rounds)
   (_ :
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
  (0 : ℕ) < lower.rounds →
  lower.rounds < ett.rounds →
  MaximumProperty lower →
  (
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tnext : TreeSequence G e0 :=
   lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ)));
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tnext (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ (alpha beta : Fin k),
  alpha ∈ TreeMissingColors sigma Tnext ∨ beta ∈ TreeMissingColors sigma Tnext →
  TreeInterchangeable G Tnext sigma alpha beta) ∧
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc;
  ∀ (v : V) (gamma delta : Fin k),
  lower.series.data.kind n = some TashkinovExtensionKind.PE →
  lower.series.data.chosenVertex n = some v →
  lower.series.data.gamma n = some gamma →
  lower.series.data.delta n = some delta →
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tn (TashkinovStoredColors lower.series.data n)
    (lower.series.data.coloring n) sigma →
  ∀ w ∈ TreeSequenceVertexSet Tn,
   Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔ w = v),
  let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
      hroundLarge⟩ : Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k) (_ : IsProperEdgeColoring G sigmaPrev)
   (_ :
    IsProperEdgeColoring G
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (_ :
    IsOneEdgeUncolored
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc) e0)
   (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
     (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).castSucc))
   (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (_ : MaximumProperty originalPrefix)
   (_ :
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i = ett.series.data.tree (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i))
   (_ :
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i = ett.series.data.coloring (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
   originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
    originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
     originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i) ∧
      TashkinovStoredColors originalPrefix.series.data i =
       TashkinovStoredColors ett.series.data (Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) i))
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
     (ett.series.data.tree (Fin.last ett.rounds).castSucc))
   (_ : MaximumProperty corr.replacementETT)
   (_ :
    ¬Nonempty
      (RevisitingExtensionCertificate ett.series.data
       (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
           ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (_ : corr.replacementSeries.data.coloring replacementLast = sigmaPrev)
   (_ : (0 : ℕ) < originalPrefix.rounds)
   (_ :
    Fin.castLE
      (positivePrefixPrefixBound ett.rounds originalPrefix.rounds _ hr) replacementLast =
     (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds hroundLarge⟩ : Fin
         ett.rounds).castSucc)
   (_ :
    corr.replacementSeries.data.tree replacementLast.succ =
     ett.series.data.tree (⟨ett.rounds - (1 : ℕ), positivePrefixPredecessorBound ett.rounds
         hroundLarge⟩ : Fin ett.rounds).succ.castSucc)
   (_ :
  ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
   {generating' : PartialEdgeColoring E k}
   (base : ExtendedTashkinovTree G k e0 input' T' generating'),
  (0 : ℕ) < base.rounds →
  base.rounds < ett.rounds →
  MaximumProperty base →
  ∀ (r : ℕ) (series : TashkinovSeries G k r e0 input'),
  base.rounds = r →
  base.series ≍ series →
  ∀ (a : Fin (r + (1 : ℕ))) (v : V) (gamma delta : Fin k),
  (0 : ℕ) < (↑a : ℕ) →
  series.data.kind a = some TashkinovExtensionKind.PE →
  series.data.chosenVertex a = some v →
  series.data.gamma a = some gamma →
  series.data.delta a = some delta →
  IsProperEdgeColoring G (series.data.coloring a) →
  IsOneEdgeUncolored (series.data.coloring a) e0 →
  ∀ w ∈ TreeSequenceVertexSet (series.data.tree a.castSucc),
   Sum.inl w ∈
     TwoColorComponent G (series.data.coloring a) gamma delta (Sum.inl v) ↔
    w = v)
   (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀
   (_ :
    originalPrefix.series.data.kind earlierPrefix = some TashkinovExtensionKind.PE)
   (oldi : Fin originalPrefix.rounds)
   (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
     (originalPrefix.series.data.coloring oldi.castSucc))
   (oldGamma : Fin k)
   (_ : IsProperEdgeColoring G (originalPrefix.series.data.coloring oldi.succ))
   (_ : IsOneEdgeUncolored (originalPrefix.series.data.coloring oldi.succ) e0)
   (_ :
    originalPrefix.series.data.stored oldi.succ =
     (insert oldChoice.color ({ oldGamma } : Finset (Fin k)) : Finset (Fin k)))
   (_ :
    originalPrefix.series.data.connectingEdges oldi.succ = ({ oldChoice.edge } : Finset E))
   (_ : originalPrefix.series.data.kind oldi.succ = some TashkinovExtensionKind.PE)
   (_ : originalPrefix.series.data.chosenVertex oldi.succ = some oldChoice.vertex)
   (_ : originalPrefix.series.data.delta oldi.succ = some oldChoice.color)
   (_ : originalPrefix.series.data.gamma oldi.succ = some oldGamma)
   (_ : earlierPrefix = oldi.succ) (_ : oldi.succ = earlierPrefix)
   (newGamma : Fin k)
   (newChoicePE :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
     (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
     (corr.replacementSeries.data.coloring oldi.castSucc))
   (_ : IsProperEdgeColoring G (corr.replacementSeries.data.coloring oldi.succ))
   (_ : IsOneEdgeUncolored (corr.replacementSeries.data.coloring oldi.succ) e0)
   (_ : corr.replacementSeries.data.kind oldi.succ = some TashkinovExtensionKind.PE)
   (_ :
    corr.replacementSeries.data.chosenVertex oldi.succ = some newChoicePE.vertex)
   (_ : corr.replacementSeries.data.delta oldi.succ = some newChoicePE.color)
   (_ : corr.replacementSeries.data.gamma oldi.succ = some newGamma)
   (hbaseTree :
    corr.replacementSeries.data.tree oldi.succ.castSucc =
     originalPrefix.series.data.tree oldi.succ.castSucc),
  let oldChoiceOnNew :
   MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc) :=
   (Eq.symm hbaseTree ▸ oldChoice);
  ∀
   (_ :
  ∀ {A B : TreeSequence G e0} (hAB : A = B) (C : Finset (Fin k))
   (phi : PartialEdgeColoring E k) (ch : MaximumDefectiveChoice G e0 A C phi),
  (hAB ▸ ch).edge = ch.edge ∧
   (hAB ▸ ch).vertex = ch.vertex ∧
    (hAB ▸ ch).otherEndpoint = ch.otherEndpoint ∧ (hAB ▸ ch).color = ch.color)
   (_ : oldChoiceOnNew.color = oldChoice.color)
   (_ :
  ∀ (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
   (ch : MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
  IsProperEdgeColoring G second →
  StableColoring X (insert ch.color C : Finset (Fin k)) ch.selected second →
  g ∈ MissingColors G ch.selected ch.vertex →
  let post : PartialEdgeColoring E k :=
   TwoColorComponentSwap G second g ch.color (Sum.inl ch.vertex);
  ch.color ∈ MissingColors G post ch.vertex ∧
   g ∉ MissingColors G post ch.vertex ∧ g ≠ ch.color)
   (_ :
    oldChoice.color ∈
     MissingColors G (originalPrefix.series.data.coloring oldi.succ) oldChoice.vertex)
   (_ :
    oldGamma ∉ MissingColors G (originalPrefix.series.data.coloring oldi.succ) oldChoice.vertex)
   (_ : oldGamma ≠ oldChoice.color) (_ : newGamma ≠ newChoicePE.color)
   (_ : newChoicePE.color = oldChoiceOnNew.color)
   (_ : newGamma = oldGamma)
   (_ : newChoicePE.color = available.delta)
   (_ : newGamma = available.gamma)
   (_ : oldChoice.color = available.delta)
   (_ : oldGamma = available.gamma)
   (_ : newChoicePE.vertex = oldChoice.vertex)
   (_ : corr.replacementSeries.data.coloring oldi.succ = sigmaPrev)
   (_ :
    originalPrefix.series.data.coloring replacementLast = ett.series.data.coloring q.castSucc)
   (_ :
    originalPrefix.series.data.coloring oldi.succ = ett.series.data.coloring q.castSucc)
   (_ : available.delta ∈ MissingColors G sigmaPrev newChoicePE.vertex)
   (_ :
    available.delta ∈ MissingColors G (ett.series.data.coloring q.castSucc) oldChoice.vertex)
   (_ :
    available.gamma ∉ MissingColors G (ett.series.data.coloring q.castSucc) oldChoice.vertex)
   (_ : available.gamma ≠ available.delta)
   (_ :
    oldChoice.vertex ∈
     TreeSequenceVertexSet
      (originalPrefix.series.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ)))))
   (_ :
    available.returnVertex ∈
     TreeSequenceVertexSet (originalPrefix.series.data.tree earlierPrefix.castSucc))
   (_ :
    available.returnVertex ∈
     TreeSequenceVertexSet
      (originalPrefix.series.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ)))))
   (_ :
  ∀ (f : E) (_ : Sum.inr f ∈ available.returnPath.support),
  TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) f ∧
   (sigmaPrev f = some available.gamma ∨ sigmaPrev f = some available.delta))
   (_ :
  ∀ (f : E) (_ : Sum.inr f ∈ available.returnPath.support),
  sigmaPrev f = ett.series.data.coloring q.castSucc f),
  False

private noncomputable abbrev helperOriginalCertificate1229.{u_1, u_2} :
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
  (generating : PartialEdgeColoring E k) →
  (ett : ExtendedTashkinovTree G k e0 input T generating) →
  (hroundLarge : (1 : ℕ) < ett.rounds) →
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  (sigmaPrev : PartialEdgeColoring E k) →
  (originalPrefix :
      ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin ett.rounds).castSucc)) →
  (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) →
  (
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i =
      ett.series.data.coloring
        (Fin.castLE
          (by
            have := GoldbergSeymour.TreeSequence.positive T
            omega)
          i) ∧
    originalPrefix.series.data.stored i =
        ett.series.data.stored
          (Fin.castLE
            (by
              have :=
                GoldbergSeymour.TreeSequence.positive T
              omega)
            i) ∧
      originalPrefix.series.data.connectingEdges i =
          ett.series.data.connectingEdges
            (Fin.castLE
              (by
                have :=
                  GoldbergSeymour.TreeSequence.positive T
                omega)
              i) ∧
        originalPrefix.series.data.kind i =
            ett.series.data.kind
              (Fin.castLE
                (by
                  have :=
                    GoldbergSeymour.TreeSequence.positive T
                  omega)
                i) ∧
          TashkinovStoredColors originalPrefix.series.data
              i =
            TashkinovStoredColors ett.series.data
              (Fin.castLE
                (by
                  have :=
                    GoldbergSeymour.TreeSequence.positive T
                  omega)
                i)) →
  (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix
        sigmaPrev
        (ett.series.data.tree
          (Fin.last ett.rounds).castSucc)) →
  let replacementLast :
    Fin (originalPrefix.rounds + (1 : ℕ)) :=
    Fin.last originalPrefix.rounds;
  Fin.castLE
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
        replacementLast =
      (⟨ett.rounds - (1 : ℕ),
            by
            have := GoldbergSeymour.TreeSequence.positive T
            omega⟩ :
          Fin ett.rounds).castSucc →
  (available :
      RevisitingExtensionCertificate
        corr.replacementSeries.data replacementLast) →
  let earlierPrefix :
    Fin (originalPrefix.rounds + (1 : ℕ)) :=
    available.earlier;
  (oldi : Fin originalPrefix.rounds) →
  (oldChoice :
      MaximumDefectiveChoice G e0
        (originalPrefix.series.data.tree
          oldi.succ.castSucc)
        (TashkinovStoredColors
          originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring
          oldi.castSucc)) →
  (oldGamma : Fin k) →
  available.returnVertex ∈
      TreeSequenceVertexSet
        (originalPrefix.series.data.tree
          earlierPrefix.castSucc) →
  let originalReturnGraph :
    SimpleGraph (V ⊕ E) :=
    TwoColorIncidenceGraph G
      (ett.series.data.coloring q.castSucc)
      available.gamma available.delta;
  (returnEdgeTransfer :
      ∀ edge ∈ available.returnPath.edges,
        edge ∈ originalReturnGraph.edgeSet) →
  let originalReturnPath :
    originalReturnGraph.Walk
      (Sum.inr available.edge)
      (Sum.inl available.returnVertex) :=
    available.returnPath.transfer
      originalReturnGraph returnEdgeTransfer;
  originalReturnPath.IsPath →
  (
  ∀ (z : V ⊕ E),
  z ∈ originalReturnPath.support ↔
    z ∈ available.returnPath.support) →
  Sum.inl available.returnVertex ∈
      TwoColorComponent G
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
                by
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    T
                omega⟩ :
              Fin ett.rounds).castSucc)
        available.gamma available.delta
        (Sum.inr available.edge) →
  Sum.inl available.outsideEndpoint ∈
      TwoColorComponent G
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
                by
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    T
                omega⟩ :
              Fin ett.rounds).castSucc)
        available.gamma available.delta
        (Sum.inr available.edge) →
  (horiginalRoundsLess :
      originalPrefix.rounds <
        ett.rounds) →
  (originalCycle :
      TwoColorCycle G
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ),
                by
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    T
                omega⟩ :
              Fin
                ett.rounds).castSucc)
        available.gamma
        available.delta) →
  (
  ∀ (x : V ⊕ E),
  x ∈
      originalCycle.walk.support ↔
    x ∈
      TwoColorComponent G
        (ett.series.data.coloring
          (⟨ett.rounds -
                  (1 : ℕ),
                by
                have :=
                  GoldbergSeymour.TreeSequence.positive
                    T
                omega⟩ :
              Fin
                ett.rounds).castSucc)
        available.gamma
        available.delta
        (Sum.inr
          available.edge)) →
  let oldEarlier :
    Fin
      (ett.rounds + (1 : ℕ)) :=
    Fin.castLE
      (by
        have :=
          GoldbergSeymour.TreeSequence.positive
            T
        omega)
      earlierPrefix;
  ett.series.data.kind
        oldEarlier =
      some
        TashkinovExtensionKind.PE →
  (fulli : Fin ett.rounds) →
  (fullChoice :
      MaximumDefectiveChoice
        G e0
        (ett.series.data.tree
          fulli.succ.castSucc)
        (TashkinovStoredColors
          ett.series.data
          fulli.castSucc)
        (ett.series.data.coloring
          fulli.castSucc)) →
  (fullGamma : Fin k) →
  ett.series.data.delta
        fulli.succ =
      some
        fullChoice.color →
  ett.series.data.gamma
        fulli.succ =
      some fullGamma →
  fulli.succ =
      oldEarlier →
  originalPrefix.series.data.tree
        oldi.succ.castSucc =
      ett.series.data.tree
        fulli.succ.castSucc →
  fullChoice.color =
      available.delta →
  fullGamma =
      available.gamma →
  ett.series.data.tree
        q.castSucc.succ =
      corr.replacementSeries.data.tree
        replacementLast.succ →
  originalPrefix.series.data.tree
        earlierPrefix.castSucc =
      ett.series.data.tree
        oldEarlier.castSucc →
  (∀
      z ∈
        originalReturnPath.support,
      z ∈
        TwoColorComponent
          G
          (ett.series.data.coloring
            q.castSucc)
          available.gamma
          available.delta
          (Sum.inr
            available.edge)) →
  RevisitingExtensionCertificate
    ett.series.data
    q.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix hr
      hprefixData corr replacementLast hlastMap available earlierPrefix oldi oldChoice oldGamma
      hreturnInOldEarlier originalReturnGraph returnEdgeTransfer originalReturnPath
      horiginalReturnIsPath horiginalReturnSupport hreturnInQ houtsideInQ horiginalRoundsLess
      originalCycle hcycleFull oldEarlier hfullEarlierKind fulli fullChoice fullGamma
      fullCurrentDelta fullCurrentGamma hfullIndex htreePrefixFull hfullDeltaAvailable
      hfullGammaAvailable hcertificateCurrentTree hprefixEarlierTree horiginalPathInQ
  exact {
    earlier := oldEarlier
    earlierPositive := by
      simpa [oldEarlier, earlierPrefix] using
        available.earlierPositive
    earlierAtMost := by
      have hle := available.earlierAtMost
      have hlastVals := congrArg Fin.val hlastMap
      simpa [oldEarlier, earlierPrefix] using
        hle.trans_eq hlastVals
    earlierPE := hfullEarlierKind
    interveningRevisiting := by
      apply revisitingExtensionKindsInPrefix <;> assumption
    gamma := available.gamma
    delta := available.delta
    earlierGamma := by
      rw [← hfullIndex, fullCurrentGamma,
        hfullGammaAvailable]
    earlierDelta := by
      rw [← hfullIndex, fullCurrentDelta,
        hfullDeltaAvailable]
    cycle := originalCycle
    meetsEarlier := by
      refine ⟨available.returnVertex, ?_, ?_⟩
      · rw [← hprefixEarlierTree]
        exact hreturnInOldEarlier
      · exact (hcycleFull _).2 hreturnInQ
    leavesCurrent := by
      refine ⟨available.outsideEndpoint, ?_, ?_⟩
      · rw [hcertificateCurrentTree]
        exact available.outsideNotCurrent
      · exact (hcycleFull _).2 houtsideInQ
    edge := available.edge
    edgeOnCycle := (hcycleFull _).2 rfl
    edgeBoundary := by
      rw [hcertificateCurrentTree]
      exact available.edgeBoundary
    insideEndpoint := available.insideEndpoint
    outsideEndpoint := available.outsideEndpoint
    insideInCurrent := by
      rw [hcertificateCurrentTree]
      exact available.insideInCurrent
    outsideNotCurrent := by
      rw [hcertificateCurrentTree]
      exact available.outsideNotCurrent
    edgeEnds := available.edgeEnds
    returnVertex := available.returnVertex
    returnInEarlier := by
      rw [← hprefixEarlierTree]
      exact hreturnInOldEarlier
    returnPath := originalReturnPath
    returnPathIsPath := horiginalReturnIsPath
    returnPathOnCycle := by
      intro z hz
      exact (hcycleFull z).2 (horiginalPathInQ z hz)
    returnPathInternal := by
      intro v hv
      have hvAvailable : Sum.inl v ∈
          available.returnPath.support :=
        (horiginalReturnSupport (Sum.inl v)).mp hv
      rw [hcertificateCurrentTree]
      exact available.returnPathInternal v hvAvailable
  }

private theorem helper_peRootOnly_167.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hroundLarge : (1 : ℕ) < ett.rounds)
      (_ :
        (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
     {generating' : PartialEdgeColoring E k}
     (lower : ExtendedTashkinovTree G k e0 input' T' generating')
     (_ : (0 : ℕ) < lower.rounds) (_ : lower.rounds < ett.rounds)
     (_ : MaximumProperty lower),
    (
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tnext : TreeSequence G e0 :=
    lower.series.data.tree (Fin.last (lower.rounds + (1 : ℕ)));
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tnext (TashkinovStoredColors lower.series.data n)
      (lower.series.data.coloring n) sigma →
  ∀ (alpha beta : Fin k),
  alpha ∈ TreeMissingColors sigma Tnext ∨
      beta ∈ TreeMissingColors sigma Tnext →
  TreeInterchangeable G Tnext sigma alpha beta) ∧
  let n : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
  let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc;
  ∀ (v : V) (gamma delta : Fin k),
  lower.series.data.kind n = some TashkinovExtensionKind.PE →
  lower.series.data.chosenVertex n = some v →
  lower.series.data.gamma n = some gamma →
  lower.series.data.delta n = some delta →
  ∀ (sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring Tn (TashkinovStoredColors lower.series.data n)
      (lower.series.data.coloring n) sigma →
  ∀ w ∈ TreeSequenceVertexSet Tn,
    Sum.inl w ∈
        TwoColorComponent G sigma gamma delta (Sum.inl v) ↔
      w = v))
      (originalPrefix :
        ExtendedTashkinovTree G k e0 input
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (ett.series.data.coloring
            (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc))
      (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ))
      {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (base : ExtendedTashkinovTree G k e0 input' T' generating')
      (_ : (0 : ℕ) < base.rounds) (_ : base.rounds < ett.rounds)
      (_ : MaximumProperty base) (r : ℕ) (series : TashkinovSeries G k r e0 input')
      (_ : base.rounds = r) (_ : base.series ≍ series) (a : Fin (r + (1 : ℕ))) (v : V)
      (gamma delta : Fin k) (_ : (0 : ℕ) < (↑a : ℕ))
      (_ : series.data.kind a = some TashkinovExtensionKind.PE)
      (_ : series.data.chosenVertex a = some v) (_ : series.data.gamma a = some gamma)
      (_ : series.data.delta a = some delta)
      (_ : IsProperEdgeColoring G (series.data.coloring a))
      (_ : IsOneEdgeUncolored (series.data.coloring a) e0),
  ∀ w ∈ TreeSequenceVertexSet (series.data.tree a.castSucc),
    Sum.inl w ∈ TwoColorComponent G (series.data.coloring a) gamma delta (Sum.inl v) ↔
      w = v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge hlower originalPrefix hr input' T'
      generating' base hp hl hm r series hrSeries hseries
  cases hrSeries
  cases hseries
  intro a v gamma delta ha hk hv hg hd hproper hone
  by_cases hlast : a.val = base.rounds
  · have haLast : a = Fin.last base.rounds := Fin.ext hlast
    subst a
    exact (hlower base hp hl hm).2 v gamma delta hk hv hg hd
      (base.series.data.coloring (Fin.last base.rounds)) hproper hone
      ⟨(by intros; rfl), (by intros; rfl)⟩
  · have habefore : a.val < base.rounds := by
      have habound := a.isLt
      omega
    obtain ⟨restricted, hrRestricted, hmaxRestricted, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input' T' generating' base hm
        a.val (by omega) habefore
    have hrestrictedPositive : 0 < restricted.rounds := by
      rw [hrRestricted]
      exact ha
    have hrestrictedLess : restricted.rounds < ett.rounds := by
      rw [hrRestricted]
      exact habefore.trans hl
    let lastRestricted : Fin (restricted.rounds + 1) :=
      Fin.last restricted.rounds
    have hmap : Fin.castLE (by omega) lastRestricted = a := by
      apply Fin.ext
      simp [lastRestricted, hrRestricted]
    have htree : restricted.series.data.tree lastRestricted.castSucc =
        base.series.data.tree a.castSucc := by
      calc
        restricted.series.data.tree lastRestricted.castSucc =
            base.series.data.tree
              (Fin.castLE (by omega) lastRestricted.castSucc) :=
          htrees lastRestricted.castSucc
        _ = base.series.data.tree a.castSucc := by
          congr 1
          apply Fin.ext
          simp [lastRestricted, hrRestricted]
    rcases hdata lastRestricted with
      ⟨hc, _, _, hkind, hvertex, _, hdelta, hgamma, _, _⟩
    rw [hmap] at hc hkind hvertex hdelta hgamma
    have hroot := (hlower restricted hrestrictedPositive hrestrictedLess
      hmaxRestricted).2 v gamma delta
      (by simpa only [← hkind] using hk)
      (by simpa only [← hvertex] using hv)
      (by simpa only [← hgamma] using hg)
      (by simpa only [← hdelta] using hd)
      (base.series.data.coloring a) hproper hone (by
        change StableColoring _ _
          (restricted.series.data.coloring lastRestricted) _
        rw [hc]
        exact ⟨(by intros; rfl), (by intros; rfl)⟩)
    intro w hw
    apply hroot w
    change w ∈ TreeSequenceVertexSet
      (restricted.series.data.tree lastRestricted.castSucc)
    rw [htree]
    exact hw

private theorem helper_reStepColoring_872.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds) (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree
    G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc)),
  originalPrefix.rounds = ett.rounds - (1 : ℕ) →
  ∀ (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
    (Fin.last ett.rounds).castSucc)) (_ : RevisitingExtensionCertificate
    corr.replacementSeries.data (Fin.last originalPrefix.rounds)) (oldi : Fin
    originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree
    oldi.succ.castSucc) (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)) (_ _ : Fin k) (_ :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
    (corr.replacementSeries.data.coloring oldi.castSucc)),
  corr.replacementSeries.data.tree
    oldi.succ.castSucc = originalPrefix.series.data.tree oldi.succ.castSucc →
  ∀ {rounds' : ℕ}
    {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0 input') (j :
    Fin rounds'),
  series.data.kind j.succ = some TashkinovExtensionKind.RE →
  series.data.coloring j.succ = series.data.coloring j.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      available oldi oldChoice oldGamma newGamma newChoicePE hbaseTree rounds' input' series j hj
  have hstep := series.certified j.succ
  generalize hslot : j.succ = slot at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored
      initialEdges initialKind initialVertex initialOutside
      initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero j hslot).elim
  | SE i prevProper prevOne prevClosed prevNotStrong noRE
      ch alternative coloring stored edges kind vertex
      outside delta gamma adjoined adjoinedExactly closed
      ordered strict =>
      have hbad := kind.symm.trans
        (by simpa [hslot] using hj)
      cases hbad
  | PE i prevProper prevOne prevClosed prevNotStrong noRE
      ch alternativeFails gamma gammaRule second
      secondProper secondOne secondStable exit coloring
      coloringProper coloringOne stored edges kind vertex
      outside delta gammaValue closed ordered strict =>
      have hbad := kind.symm.trans
        (by simpa [hslot] using hj)
      cases hbad
  | RE i prevProper prevOne prevClosed prevNotStrong cert
      coloring stored edges kind vertex outside delta gamma
      adjoined adjoinedExactly closed ordered strict =>
      have hi : i = j := by
        apply Fin.ext
        have hv := congrArg Fin.val hslot
        simp only [Fin.val_succ] at hv
        omega
      subst i
      simpa [hslot] using coloring

private theorem helper_reIntervalColoring_913.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds) (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree
    G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc)),
  originalPrefix.rounds = ett.rounds - (1 : ℕ) →
  ∀ (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
    (Fin.last ett.rounds).castSucc)) (_ : RevisitingExtensionCertificate
    corr.replacementSeries.data (Fin.last originalPrefix.rounds)) (oldi : Fin
    originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree
    oldi.succ.castSucc) (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)) (_ _ : Fin k) (_ :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
    (corr.replacementSeries.data.coloring oldi.castSucc)),
  corr.replacementSeries.data.tree
    oldi.succ.castSucc = originalPrefix.series.data.tree oldi.succ.castSucc →
  (
  ∀ {rounds' : ℕ}
   {input' : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0 input') (j :
   Fin rounds'),
  series.data.kind j.succ = some TashkinovExtensionKind.RE →
  series.data.coloring j.succ = series.data.coloring j.castSucc) →
  ∀ {rounds' : ℕ} {input' :
    PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0 input') (a b : Fin
    (rounds' + (1 : ℕ))),
  (↑a : ℕ) ≤ (↑b : ℕ) →
  (
  ∀ (j : Fin (rounds' + (1 : ℕ))),
  (↑a : ℕ) <
    (↑j : ℕ) →
  (↑j : ℕ) ≤ (↑b : ℕ) →
  series.data.kind j = some TashkinovExtensionKind.RE) →
  series.data.coloring b = series.data.coloring a := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      available oldi oldChoice oldGamma newGamma newChoicePE hbaseTree reStepColoring rounds'
      input' series a b hab hbetween
  have coloringAlong : ∀ m : ℕ, a.val ≤ m →
      m ≤ b.val → ∀ x : Fin (rounds' + 1),
      x.val = m →
        series.data.coloring x = series.data.coloring a := by
    intro m ham
    induction m, ham using Nat.le_induction with
    | base =>
        intro hmb x hx
        have hxa : x = a := by
          apply Fin.ext
          omega
        rw [hxa]
    | succ m ham ih =>
        intro hmb x hx
        let j : Fin rounds' := ⟨m, by
          have hbLt := b.isLt
          omega⟩
        have hjKind : series.data.kind j.succ =
            some TashkinovExtensionKind.RE := by
          apply hbetween j.succ
          · simp [j]
            omega
          · simp [j]
            omega
        have hstep := reStepColoring series j hjKind
        have hxj : x = j.succ := by
          apply Fin.ext
          simp [j, hx]
        calc
          series.data.coloring x =
              series.data.coloring j.succ := by rw [hxj]
          _ = series.data.coloring j.castSucc := hstep
          _ = series.data.coloring a :=
            ih (by omega) j.castSucc (by simp [j])
  exact coloringAlong b.val hab le_rfl b rfl

private theorem helper_stepSegment_1041.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds) (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree
    G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc)),
  originalPrefix.rounds = ett.rounds - (1 : ℕ) →
  ∀ (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
    (Fin.last ett.rounds).castSucc)) (_ : RevisitingExtensionCertificate
    corr.replacementSeries.data (Fin.last originalPrefix.rounds)) (oldi : Fin
    originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree
    oldi.succ.castSucc) (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)) (_ _ : Fin k) (_ :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
    (corr.replacementSeries.data.coloring oldi.castSucc)),
  corr.replacementSeries.data.tree
    oldi.succ.castSucc = originalPrefix.series.data.tree oldi.succ.castSucc →
  ∀ (r : Fin
    originalPrefix.rounds),
  TreeSequenceInitialSegment (originalPrefix.series.data.tree
    r.succ.castSucc) (originalPrefix.series.data.tree r.succ.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      available oldi oldChoice oldGamma newGamma newChoicePE hbaseTree r
  have hstep := originalPrefix.series.certified r.succ
  generalize hslot : r.succ = slot at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored
      initialEdges initialKind initialVertex initialOutside
      initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero r hslot).elim
  | SE i prevProper prevOne prevClosed prevNotStrong noRE ch
      alternative coloring stored edges kind vertex outside
      delta gamma adjoined adjoinedExactly closed ordered strict =>
      have hi : i = r := by
        apply Fin.ext
        have hv := congrArg Fin.val hslot
        simp only [Fin.val_succ] at hv
        omega
      subst i
      simpa [hslot] using ordered
  | PE i prevProper prevOne prevClosed prevNotStrong noRE ch
      alternativeFails gamma gammaRule second secondProper
      secondOne secondStable exit coloring coloringProper
      coloringOne stored edges kind vertex outside delta
      gammaValue closed ordered strict =>
      have hi : i = r := by
        apply Fin.ext
        have hv := congrArg Fin.val hslot
        simp only [Fin.val_succ] at hv
        omega
      subst i
      simpa [hslot] using ordered
  | RE i prevProper prevOne prevClosed prevNotStrong cert
      coloring stored edges kind vertex outside delta gamma
      adjoined adjoinedExactly closed ordered strict =>
      have hi : i = r := by
        apply Fin.ext
        have hv := congrArg Fin.val hslot
        simp only [Fin.val_succ] at hv
        omega
      subst i
      simpa [hslot] using ordered

private theorem helper_treeToFinal_1111.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds) (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree
    G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc)),
  originalPrefix.rounds = ett.rounds - (1 : ℕ) →
  ∀ (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
    (Fin.last ett.rounds).castSucc)) (_ : RevisitingExtensionCertificate
    corr.replacementSeries.data (Fin.last originalPrefix.rounds)) (oldi : Fin
    originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree
    oldi.succ.castSucc) (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)) (_ _ : Fin k) (_ :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
    (corr.replacementSeries.data.coloring oldi.castSucc)),
  corr.replacementSeries.data.tree
    oldi.succ.castSucc = originalPrefix.series.data.tree oldi.succ.castSucc →
  (
  ∀ (r : Fin
   originalPrefix.rounds),
  TreeSequenceInitialSegment (originalPrefix.series.data.tree
    r.succ.castSucc) (originalPrefix.series.data.tree r.succ.succ)) →
  (
  ∀ (A B C : TreeSequence
   G e0),
  TreeSequenceInitialSegment A B →
  TreeSequenceInitialSegment B C →
  TreeSequenceInitialSegment A C) →
  ∀ (d : ℕ) (idx : Fin (originalPrefix.rounds + (2 : ℕ))),
  (↑idx : ℕ) + d = originalPrefix.rounds + (1 : ℕ) →
  (1 : ℕ) ≤ (↑idx : ℕ) →
  TreeSequenceInitialSegment (originalPrefix.series.data.tree idx)
  (originalPrefix.series.data.tree (Fin.last (originalPrefix.rounds + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      available oldi oldChoice oldGamma newGamma newChoicePE hbaseTree stepSegment segmentTrans d
  induction d with
  | zero =>
      intro idx hidx hpos
      have hi : idx =
          Fin.last (originalPrefix.rounds + 1) := by
        apply Fin.ext
        simp
        omega
      rw [hi]
      exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  | succ d ih =>
      intro idx hidx hpos
      have hlt : idx.val < originalPrefix.rounds + 1 := by
        omega
      let r : Fin originalPrefix.rounds :=
        ⟨idx.val - 1, by omega⟩
      have hleft : idx = r.succ.castSucc := by
        apply Fin.ext
        simp [r]
        omega
      let next : Fin (originalPrefix.rounds + 2) :=
        ⟨idx.val + 1, by omega⟩
      have hright : next = r.succ.succ := by
        apply Fin.ext
        simp [next, r]
        omega
      have hfirst : TreeSequenceInitialSegment
          (originalPrefix.series.data.tree idx)
          (originalPrefix.series.data.tree next) := by
        rw [hleft, hright]
        exact stepSegment r
      exact segmentTrans _ _ _ hfirst
        (ih next (by simp [next]; omega)
          (by simp [next]))

private theorem helper_returnEdgeTransfer_1317.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds),
  ∀ (sigmaPrev : PartialEdgeColoring E k) (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc))
    (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
    (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev →
  ∀
    (available : RevisitingExtensionCertificate corr.replacementSeries.data (Fin.last
    originalPrefix.rounds)),
  (
  ∀ (f : E),
  Sum.inr f ∈ available.returnPath.support →
  sigmaPrev
    f = ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds) : Fin
    ett.rounds).castSucc f) →
  ∀ edge ∈ available.returnPath.edges, edge ∈
    (TwoColorIncidenceGraph G (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ), by omega⟩ :
    Fin ett.rounds) : Fin ett.rounds).castSucc) available.gamma available.delta : SimpleGraph
    (V ⊕ E)).edgeSet := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge
  set q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds)
  intro sigmaPrev originalPrefix corr hcorrFinalColor
  set replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
              originalPrefix.rounds
  intro available copyReturnEdge
  set replacementReturnGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G
      (corr.replacementSeries.data.coloring replacementLast)
                    available.gamma
                  available.delta
  set originalReturnGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G
      (ett.series.data.coloring q.castSucc) available.gamma
                    available.delta
  intro edge hedge
  induction edge using Sym2.inductionOn with
  | _ a b =>
      have haSupport :=
        available.returnPath.fst_mem_support_of_mem_edges
          hedge
      have hbSupport :=
        available.returnPath.snd_mem_support_of_mem_edges
          hedge
      have habReplacement : replacementReturnGraph.Adj a b := by
        simpa [replacementReturnGraph] using
          available.returnPath.edges_subset_edgeSet hedge
      cases a with
      | inl v =>
          cases b with
          | inl w =>
              simp [replacementReturnGraph, TwoColorIncidenceGraph] at habReplacement
          | inr f =>
              have hdata : Incident G v f ∧
                  (corr.replacementSeries.data.coloring
                        replacementLast f =
                      some available.gamma ∨
                    corr.replacementSeries.data.coloring
                        replacementLast f =
                      some available.delta) := by
                simpa [replacementReturnGraph,
                  TwoColorIncidenceGraph] using habReplacement
              have hcopy := copyReturnEdge f hbSupport
              have hfinal :
                  corr.replacementSeries.data.coloring
                      replacementLast f = sigmaPrev f := by
                simpa [replacementLast] using
                  congrFun hcorrFinalColor f
              simpa [originalReturnGraph,
                TwoColorIncidenceGraph, hfinal, hcopy] using hdata
      | inr f =>
          cases b with
          | inl v =>
              have hdata : Incident G v f ∧
                  (corr.replacementSeries.data.coloring
                        replacementLast f =
                      some available.gamma ∨
                    corr.replacementSeries.data.coloring
                        replacementLast f =
                      some available.delta) := by
                simpa [replacementReturnGraph,
                  TwoColorIncidenceGraph] using habReplacement
              have hcopy := copyReturnEdge f haSupport
              have hfinal :
                  corr.replacementSeries.data.coloring
                      replacementLast f = sigmaPrev f := by
                simpa [replacementLast] using
                  congrFun hcorrFinalColor f
              simpa [originalReturnGraph,
                TwoColorIncidenceGraph, hfinal, hcopy] using hdata
          | inr g =>
              simp [replacementReturnGraph, TwoColorIncidenceGraph] at habReplacement

private theorem helper_htreePrefixFull_719.{u_1, u_2} :
    helperHtreePrefixFull719Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr
      hprefixTrees corr available
  set earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier
  intro oldi oldChoice oldGamma hbaseTarget holdIndex horiginalRoundsLess
  set oldEarlier : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE (by omega)
                      earlierPrefix
  intro fulli hfullIndex
  calc
    originalPrefix.series.data.tree
        oldi.succ.castSucc =
        ett.series.data.tree
          (Fin.castLE (by omega)
            oldi.succ.castSucc) :=
      hprefixTrees oldi.succ.castSucc
    _ = ett.series.data.tree fulli.succ.castSucc := by
      congr 1
      apply Fin.ext
      have holdVals := congrArg Fin.val holdIndex
      have hfullVals := congrArg Fin.val hfullIndex
      change oldi.val + 1 = earlierPrefix.val at holdVals
      change fulli.val + 1 = earlierPrefix.val at hfullVals
      simp only [Fin.val_castLE, Fin.val_castSucc,
        Fin.val_succ]
      omega

private theorem helper_hpostColorPrefixFull_1435.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc))
  (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
  (
  ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))),
  originalPrefix.series.data.coloring i =
      ett.series.data.coloring
        (Fin.castLE
          (by
            have := GoldbergSeymour.TreeSequence.positive T
            omega)
          i) ∧
    originalPrefix.series.data.stored i =
        ett.series.data.stored
          (Fin.castLE
            (by
              have := GoldbergSeymour.TreeSequence.positive T
              omega)
            i) ∧
      originalPrefix.series.data.connectingEdges i =
          ett.series.data.connectingEdges
            (Fin.castLE
              (by
                have := GoldbergSeymour.TreeSequence.positive T
                omega)
              i) ∧
        originalPrefix.series.data.kind i =
            ett.series.data.kind
              (Fin.castLE
                (by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega)
                i) ∧
          TashkinovStoredColors originalPrefix.series.data i =
            TashkinovStoredColors ett.series.data
              (Fin.castLE
                (by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega)
                i)) →
  ∀
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data
      replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
    (_ :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc))
    (_ : Fin k),
  oldi.succ = earlierPrefix →
  ∀ (horiginalRoundsLess : originalPrefix.rounds < ett.rounds),
  let oldEarlier : Fin (ett.rounds + (1 : ℕ)) :=
    Fin.castLE
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      earlierPrefix;
  ∀ (fulli : Fin ett.rounds),
  oldEarlier = fulli.succ →
  originalPrefix.series.data.tree oldi.succ.castSucc = ett.series.data.tree
      fulli.succ.castSucc →
  originalPrefix.series.data.coloring oldi.succ = ett.series.data.coloring
      fulli.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr
      hprefixData corr replacementLast available earlierPrefix oldi oldChoice oldGamma holdIndex
      horiginalRoundsLess oldEarlier fulli hfullTarget htreePrefixFull
  calc
    originalPrefix.series.data.coloring oldi.succ =
        originalPrefix.series.data.coloring
          earlierPrefix := by rw [holdIndex]
    _ = ett.series.data.coloring
          (Fin.castLE (by omega) earlierPrefix) :=
      (hprefixData earlierPrefix).1
    _ = ett.series.data.coloring fulli.succ := by
      congr 1

private theorem helper_hprefixEarlierTree_1498.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc))
  (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
  (
  ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))),
  originalPrefix.series.data.tree i =
    ett.series.data.tree
      (Fin.castLE
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
        i)) →
  ∀
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data
      replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
    (_ :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc))
    (_ : Fin k) (horiginalRoundsLess : originalPrefix.rounds < ett.rounds),
  let oldEarlier : Fin (ett.rounds + (1 : ℕ)) :=
    Fin.castLE
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      earlierPrefix;
  ∀ (fulli : Fin ett.rounds)
    (_ :
      MaximumDefectiveChoice G e0 (ett.series.data.tree fulli.succ.castSucc)
        (TashkinovStoredColors ett.series.data fulli.castSucc)
            (ett.series.data.coloring fulli.castSucc))
    (_ : Fin k),
  originalPrefix.series.data.tree oldi.succ.castSucc = ett.series.data.tree
      fulli.succ.castSucc →
  originalPrefix.series.data.tree earlierPrefix.castSucc = ett.series.data.tree
      oldEarlier.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr
      hprefixTrees corr replacementLast available earlierPrefix oldi oldChoice oldGamma
      horiginalRoundsLess oldEarlier fulli fullChoice fullGamma htreePrefixFull
  calc
    originalPrefix.series.data.tree
        earlierPrefix.castSucc =
        ett.series.data.tree
          (Fin.castLE (by omega)
            earlierPrefix.castSucc) :=
      hprefixTrees earlierPrefix.castSucc
    _ = ett.series.data.tree oldEarlier.castSucc := by
      congr 1

private theorem helper_horiginalPathInQ_1511.{u_1, u_2} :
    helperHoriginalPathInQ1511Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix corr
      replacementLast available originalReturnGraph returnEdgeTransfer originalReturnPath z hz
  obtain ⟨m, hm, hmle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  change originalReturnGraph.connectedComponentMk z =
    originalReturnGraph.connectedComponentMk
      (Sum.inr available.edge)
  rw [← hm]
  exact (SimpleGraph.ConnectedComponent.sound
    (originalReturnPath.take m).reachable).symm

private theorem helper_continuation_1990.{u_1, u_2} :
    helperContinuation1990Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix hr
      hprefixTrees hprefixData corr noRevisiting replacementLast hlastMap hreplacementCurrentTree
      available earlierPrefix oldi oldChoice oldGamma holdDeltaAvailable holdGammaAvailable
      hreturnInOldEarlier originalReturnGraph returnEdgeTransfer originalReturnPath
      horiginalReturnIsPath horiginalReturnSupport hreturnInQ houtsideInQ horiginalRoundsLess
      originalCycle hcycleFull oldEarlier hfullEarlierKind fulli fullChoice fullGamma
      fullCurrentDelta fullCurrentGamma hfullIndex htreePrefixFull prefixChoiceOnFull
      hprefColorCast hfullEdgePairs hfullColorPairs hfullDeltaMissing hfullGammaNotMissing
      hmissingPrefixFull hprefDeltaForFull hprefGammaForFull
  have hfullIdentified := TdEarlierPEWitnessIdentification
    G k e0
    (ett.series.data.tree fulli.succ.castSucc)
    (TashkinovStoredColors originalPrefix.series.data
      oldi.castSucc)
    (TashkinovStoredColors ett.series.data fulli.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)
    (ett.series.data.coloring fulli.castSucc)
    prefixChoiceOnFull fullChoice oldGamma fullGamma
    (originalPrefix.series.data.coloring oldi.succ)
    (ett.series.data.coloring fulli.succ)
    hfullEdgePairs hfullColorPairs hmissingPrefixFull
    hprefDeltaForFull hprefGammaForFull
    hfullDeltaMissing hfullGammaNotMissing
  rcases hfullIdentified with ⟨hfullIdentifiedEdge,
    hfullIdentifiedVertex, hfullIdentifiedOther,
    hfullIdentifiedDelta, hfullIdentifiedGamma⟩
  have hfullDeltaAvailable : fullChoice.color =
      available.delta :=
    hfullIdentifiedDelta.trans
      (hprefColorCast.trans holdDeltaAvailable)
  have hfullGammaAvailable : fullGamma =
      available.gamma :=
    hfullIdentifiedGamma.trans holdGammaAvailable
  have hcurrentIndex : q.castSucc.succ =
      q.succ.castSucc := by
    apply Fin.ext
    rfl
  have hcertificateCurrentTree :
      ett.series.data.tree q.castSucc.succ =
        corr.replacementSeries.data.tree
          replacementLast.succ := by
    rw [hcurrentIndex, hreplacementCurrentTree]
  have hprefixEarlierTree :
      originalPrefix.series.data.tree
          earlierPrefix.castSucc =
        ett.series.data.tree oldEarlier.castSucc := by
    apply helper_hprefixEarlierTree_1498 <;> assumption
  have horiginalPathInQ : ∀ z,
      z ∈ originalReturnPath.support →
        z ∈ TwoColorComponent G
          (ett.series.data.coloring q.castSucc)
          available.gamma available.delta
          (Sum.inr available.edge) := by
    apply helper_horiginalPathInQ_1511; assumption
  let originalCertificate : RevisitingExtensionCertificate
      ett.series.data q.castSucc := by
    exact helperOriginalCertificate1229 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@hr) (@hprefixData) (@corr) (@hlastMap)
        (@available) (@oldi) (@oldChoice) (@oldGamma) (@hreturnInOldEarlier)
        (@returnEdgeTransfer) (@horiginalReturnIsPath) (@horiginalReturnSupport) (@hreturnInQ)
        (@houtsideInQ) (@horiginalRoundsLess) (@originalCycle) (@hcycleFull) (@hfullEarlierKind)
        (@fulli) (@fullChoice) (@fullGamma) (@fullCurrentDelta) (@fullCurrentGamma) (@hfullIndex)
        (@htreePrefixFull) (@hfullDeltaAvailable) (@hfullGammaAvailable)
        (@hcertificateCurrentTree) (@hprefixEarlierTree) (@horiginalPathInQ)
  exact noRevisiting ⟨originalCertificate⟩

private theorem helper_branch_1721.{u_1, u_2} :
    helperBranch1721Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge
  set q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds)
  intro sigmaPrev originalPrefix hr hprefixTrees hprefixData corr noRevisiting
  set replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
                    originalPrefix.rounds
  intro hlastMap hreplacementCurrentTree available
  set earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier
  intro oldi oldChoice oldGamma oldCurrentStored oldCurrentEdges hbaseTarget holdIndex newGamma
      newChoicePE hbaseTree transportChoiceFields pePostStatus holdDeltaMissing
      holdGammaNotMissing holdDeltaAvailable holdGammaAvailable hreturnInOldEarlier
  set originalReturnGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G
                                                      (ett.series.data.coloring q.castSucc)
                                                    available.gamma available.delta
  intro returnEdgeTransfer
  set originalReturnPath : originalReturnGraph.Walk (Sum.inr
                                                        available.edge)
                                                      (Sum.inl available.returnVertex) :=
                                                          available.returnPath.transfer
                                                        originalReturnGraph returnEdgeTransfer
  intro horiginalReturnIsPath horiginalReturnSupport hreturnInQ houtsideInQ horiginalRoundsLess
      originalCycle hcycleFull
  set oldEarlier : Fin (ett.rounds +
                                                                  (1 : ℕ)) := Fin.castLE (by
                                                                      omega) earlierPrefix
  intro hfullEarlierKind fulli fullChoice fullGamma fullGammaRule fullSecond fullSecondProper
      fullSecondStable fullCurrentColoring fullCurrentStored fullCurrentEdges fullCurrentDelta
      fullCurrentGamma hfullTarget
  have hfullIndex : fulli.succ = oldEarlier := by
    simpa using hfullTarget.symm
  have htreePrefixFull :
      originalPrefix.series.data.tree
          oldi.succ.castSucc =
        ett.series.data.tree fulli.succ.castSucc := by
    apply helper_htreePrefixFull_719 <;> assumption
  let prefixChoiceOnFull : MaximumDefectiveChoice G e0
      (ett.series.data.tree fulli.succ.castSucc)
      (TashkinovStoredColors originalPrefix.series.data
        oldi.castSucc)
      (originalPrefix.series.data.coloring oldi.castSucc) :=
    htreePrefixFull ▸ oldChoice
  have htransportFull := transportChoiceFields
    htreePrefixFull
    (TashkinovStoredColors originalPrefix.series.data
      oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)
    oldChoice
  have hprefEdgeCast : prefixChoiceOnFull.edge =
      oldChoice.edge := htransportFull.1
  have hprefVertexCast : prefixChoiceOnFull.vertex =
      oldChoice.vertex := htransportFull.2.1
  have hprefOtherCast : prefixChoiceOnFull.otherEndpoint =
      oldChoice.otherEndpoint := htransportFull.2.2.1
  have hprefColorCast : prefixChoiceOnFull.color =
      oldChoice.color := htransportFull.2.2.2
  have hfullMap : Fin.castLE (by omega) earlierPrefix =
      oldEarlier := by rfl
  have hfullEdgePairs :
      ({prefixChoiceOnFull.edge} : Finset E) =
        {fullChoice.edge} := by
    have hprefEdges :
        originalPrefix.series.data.connectingEdges
            earlierPrefix = {oldChoice.edge} := by
      simpa only [holdIndex] using oldCurrentEdges
    have hfullEdges : ett.series.data.connectingEdges
        oldEarlier = {fullChoice.edge} := by
      simpa only [hfullIndex] using fullCurrentEdges
    simpa only [hprefEdgeCast] using
      hprefEdges.symm.trans
        (((hprefixData earlierPrefix).2.2.1.trans
          (by rw [hfullMap])).trans hfullEdges)
  have hfullColorPairs :
      ({prefixChoiceOnFull.color, oldGamma} :
          Finset (Fin k)) =
        {fullChoice.color, fullGamma} := by
    have hprefStored : originalPrefix.series.data.stored
        earlierPrefix = {oldChoice.color, oldGamma} := by
      simpa only [holdIndex] using oldCurrentStored
    have hfullStored : ett.series.data.stored oldEarlier =
        {fullChoice.color, fullGamma} := by
      simpa only [hfullIndex] using fullCurrentStored
    simpa only [hprefColorCast] using
      hprefStored.symm.trans
        (((hprefixData earlierPrefix).2.1.trans
          (by rw [hfullMap])).trans hfullStored)
  have hfullEdgeIdentity : fullChoice.edge =
      prefixChoiceOnFull.edge := by
    apply Finset.mem_singleton.mp
    rw [hfullEdgePairs]
    exact Finset.mem_singleton_self _
  have hfullEnds : s(prefixChoiceOnFull.vertex,
        prefixChoiceOnFull.otherEndpoint) =
      s(fullChoice.vertex, fullChoice.otherEndpoint) := by
    calc
      s(prefixChoiceOnFull.vertex,
          prefixChoiceOnFull.otherEndpoint) =
          G.ends prefixChoiceOnFull.edge :=
        prefixChoiceOnFull.edgeEnds.symm
      _ = G.ends fullChoice.edge :=
        congrArg G.ends hfullEdgeIdentity.symm
      _ = s(fullChoice.vertex,
          fullChoice.otherEndpoint) := fullChoice.edgeEnds
  have hfullVertexIdentity : fullChoice.vertex =
      prefixChoiceOnFull.vertex := by
    rcases Sym2.eq_iff.mp hfullEnds with
        hstraight | hcross
    · exact hstraight.1.symm
    · exfalso
      exact fullChoice.otherOutside
        (hcross.1 ▸
          prefixChoiceOnFull.vertexDefective.1)
  have hfullOtherIdentity : fullChoice.otherEndpoint =
      prefixChoiceOnFull.otherEndpoint := by
    rcases Sym2.eq_iff.mp hfullEnds with
        hstraight | hcross
    · exact hstraight.2.symm
    · exfalso
      exact prefixChoiceOnFull.otherOutside
        (hcross.2 ▸ fullChoice.vertexDefective.1)
  obtain ⟨hfullDeltaMissing, hfullGammaNotMissing,
      hfullColorNe⟩ := pePostStatus
    (ett.series.data.tree fulli.succ.castSucc)
    (TashkinovStoredColors ett.series.data fulli.castSucc)
    (ett.series.data.coloring fulli.castSucc)
    fullChoice fullGamma fullSecond fullSecondProper
    fullSecondStable fullGammaRule.1
  rw [← fullCurrentColoring] at hfullDeltaMissing hfullGammaNotMissing
  have hpostColorPrefixFull :
      originalPrefix.series.data.coloring oldi.succ =
        ett.series.data.coloring fulli.succ := by
    apply helper_hpostColorPrefixFull_1435 <;> assumption
  have hmissingPrefixFull : MissingColors G
      (originalPrefix.series.data.coloring oldi.succ)
        prefixChoiceOnFull.vertex =
    MissingColors G
      (ett.series.data.coloring fulli.succ)
        fullChoice.vertex := by
    rw [hpostColorPrefixFull, hfullVertexIdentity]
  have hprefDeltaForFull : prefixChoiceOnFull.color ∈
      MissingColors G
        (originalPrefix.series.data.coloring oldi.succ)
        prefixChoiceOnFull.vertex := by
    simpa only [hprefColorCast, hprefVertexCast] using
      holdDeltaMissing
  have hprefGammaForFull : oldGamma ∉ MissingColors G
      (originalPrefix.series.data.coloring oldi.succ)
      prefixChoiceOnFull.vertex := by
    simpa only [hprefVertexCast] using
      holdGammaNotMissing
  exact helper_continuation_1990 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr)
      (@noRevisiting) (@hlastMap) (@hreplacementCurrentTree) (@available) (@oldi) (@oldChoice)
      (@oldGamma) (@holdDeltaAvailable) (@holdGammaAvailable) (@hreturnInOldEarlier)
      (@returnEdgeTransfer) (@horiginalReturnIsPath) (@horiginalReturnSupport) (@hreturnInQ)
      (@houtsideInQ) (@horiginalRoundsLess) (@originalCycle) (@hcycleFull) (@hfullEarlierKind)
      (@fulli) (@fullChoice) (@fullGamma) (@fullCurrentDelta) (@fullCurrentGamma) (@hfullIndex)
      (@htreePrefixFull) (@hprefColorCast) (@hfullEdgePairs) (@hfullColorPairs)
      (@hfullDeltaMissing) (@hfullGammaNotMissing) (@hmissingPrefixFull) (@hprefDeltaForFull)
      (@hprefGammaForFull)
private theorem helper_segmentTrans_1816.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0
    : E) (A B C : TreeSequence G e0),
  TreeSequenceInitialSegment A B →
  TreeSequenceInitialSegment B C →
  TreeSequenceInitialSegment A C := by
  classical
  intro V E G e0 A B C hAB hBC
  rcases hAB with ⟨hlenAB, hvertexAB, hedgeAB⟩
  rcases hBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
  refine ⟨hlenAB.trans hlenBC, ?_, ?_⟩
  · intro x
    calc
      C.vertex (Fin.castLE
          (Nat.succ_le_succ (hlenAB.trans hlenBC)) x) =
          C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
            (Fin.castLE (Nat.succ_le_succ hlenAB) x)) := by
              congr 1
      _ = B.vertex
          (Fin.castLE (Nat.succ_le_succ hlenAB) x) :=
        hvertexBC _
      _ = A.vertex x := hvertexAB x
  · intro x
    calc
      C.edge (Fin.castLE (hlenAB.trans hlenBC) x) =
          C.edge (Fin.castLE hlenBC
            (Fin.castLE hlenAB x)) := by congr 1
      _ = B.edge (Fin.castLE hlenAB x) := hedgeBC _
      _ = A.edge x := hedgeAB x

private theorem helper_replacementReturnEdgeData_1963.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds),
  ∀ (sigmaPrev : PartialEdgeColoring E k) (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc))
    (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
    (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev →
  corr.replacementSeries.data.tree (Fin.last originalPrefix.rounds : Fin
  (originalPrefix.rounds + (1 : ℕ))).succ = ett.series.data.tree ((⟨ett.rounds - (1 : ℕ), by
  omega⟩ : Fin ett.rounds) : Fin ett.rounds).succ.castSucc →
  ∀ (available :
    RevisitingExtensionCertificate corr.replacementSeries.data (Fin.last
    originalPrefix.rounds)),
  ¬available.returnPath.Nil →
  ∀ (f : E),
  Sum.inr f ∈
    available.returnPath.support →
  TreeIncidentEdge (ett.series.data.tree ((⟨ett.rounds - (1 :
    ℕ), by omega⟩ : Fin ett.rounds) : Fin ett.rounds).succ.castSucc) f ∧ (sigmaPrev f = some
    available.gamma ∨ sigmaPrev f = some available.delta) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge
  set q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds)
  intro sigmaPrev originalPrefix corr hcorrFinalColor
  set replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
              originalPrefix.rounds
  intro hreplacementCurrentTree available hreturnNotNil f hf
  obtain ⟨node, hnode, hadj⟩ :=
    SimpleGraph.adj_of_mem_walk_support available.returnPath
      hreturnNotNil hf
  cases node with
  | inl v =>
      have hdataRaw : Incident G v f ∧
          (corr.replacementSeries.data.coloring
                replacementLast f = some available.gamma ∨
            corr.replacementSeries.data.coloring
                replacementLast f = some available.delta) := by
        simpa [TwoColorIncidenceGraph] using hadj
      have hdata : Incident G v f ∧
          (sigmaPrev f = some available.gamma ∨
            sigmaPrev f = some available.delta) := by
        simpa [replacementLast, hcorrFinalColor] using hdataRaw
      refine ⟨⟨v, ?_, hdata.1⟩, hdata.2⟩
      rw [← hreplacementCurrentTree]
      exact available.returnPathInternal v hnode
  | inr g =>
      simp [TwoColorIncidenceGraph] at hadj

private theorem helper_hreturnNeOld_2171.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds) (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree
    G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc))
    (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
    (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  ∀ (available :
    RevisitingExtensionCertificate corr.replacementSeries.data (Fin.last
    originalPrefix.rounds)) (oldi : Fin originalPrefix.rounds) (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)) (newChoicePE : MaximumDefectiveChoice
    G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc) (TashkinovStoredColors
    corr.replacementSeries.data oldi.castSucc) (corr.replacementSeries.data.coloring
    oldi.castSucc)),
  newChoicePE.vertex = oldChoice.vertex →
  ((TwoColorIncidenceGraph G
    (corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds : Fin
    (originalPrefix.rounds + (1 : ℕ)))) available.gamma available.delta).neighborSet (Sum.inl
    newChoicePE.vertex)).Subsingleton →
  available.returnVertex ≠ oldChoice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix corr
  set replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds
  intro available oldi oldChoice newChoicePE hnewVertexOld hreplacementLeaf heq
  have hsupport : Sum.inl newChoicePE.vertex ∈
      available.cycle.walk.support := by
    rw [hnewVertexOld, ← heq]
    apply available.returnPathOnCycle
    simp
  let rotated := available.cycle.walk.rotate
    (Sum.inl newChoicePE.vertex) hsupport
  have hrotated : rotated.IsCycle :=
    available.cycle.isCycle.rotate hsupport
  have hfirst : (TwoColorIncidenceGraph G
      (corr.replacementSeries.data.coloring replacementLast)
      available.gamma available.delta).Adj
        (Sum.inl newChoicePE.vertex) rotated.snd :=
    rotated.adj_snd hrotated.not_nil
  have hlast : (TwoColorIncidenceGraph G
      (corr.replacementSeries.data.coloring replacementLast)
      available.gamma available.delta).Adj
        (Sum.inl newChoicePE.vertex) rotated.penultimate :=
    (rotated.adj_penultimate hrotated.not_nil).symm
  exact hrotated.snd_ne_penultimate
    (hreplacementLeaf hfirst hlast)

private theorem helper_hbaseColorConstant_1908.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds) (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree
    G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc)),
  originalPrefix.rounds = ett.rounds - (1 : ℕ) →
  ∀ (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
    (Fin.last ett.rounds).castSucc)),
  ∀ (available : RevisitingExtensionCertificate
    corr.replacementSeries.data (Fin.last originalPrefix.rounds)),
  (0 : ℕ) <
    (↑(available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) : ℕ) →
  ∀ (oldi : Fin
    originalPrefix.rounds) (_ : MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree
    oldi.succ.castSucc) (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)) (_ : Fin k),
  (available.earlier : Fin
    (originalPrefix.rounds + (1 : ℕ))) = oldi.succ →
  oldi.succ = (available.earlier : Fin
    (originalPrefix.rounds + (1 : ℕ))) →
  ∀ (_ : Fin k) (_ : MaximumDefectiveChoice G e0
    (corr.replacementSeries.data.tree oldi.succ.castSucc) (TashkinovStoredColors
    corr.replacementSeries.data oldi.castSucc) (corr.replacementSeries.data.coloring
    oldi.castSucc)),
  corr.replacementSeries.data.tree oldi.succ.castSucc =
    originalPrefix.series.data.tree oldi.succ.castSucc →
  (
  ∀ {rounds' : ℕ} {input' :
   PartialEdgeColoring E k} (series : TashkinovSeries G k rounds' e0 input') (a b : Fin
   (rounds' + (1 : ℕ))),
  (↑a : ℕ) ≤ (↑b : ℕ) →
  (
  ∀ (j : Fin (rounds' + (1 : ℕ))),
  (↑a : ℕ) <
    (↑j : ℕ) →
  (↑j : ℕ) ≤ (↑b : ℕ) →
  series.data.kind j = some TashkinovExtensionKind.RE) →
  series.data.coloring b = series.data.coloring a) →
  originalPrefix.series.data.coloring
    (Fin.last originalPrefix.rounds : Fin (originalPrefix.rounds + (1 : ℕ))) =
    originalPrefix.series.data.coloring oldi.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
  set replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
              originalPrefix.rounds
  intro available
  set earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier
  intro hearlierPositive oldi oldChoice oldGamma hbaseTarget holdIndex newGamma newChoicePE
      hbaseTree reIntervalColoring
  apply reIntervalColoring originalPrefix.series oldi.succ
    replacementLast
  · have hvals := congrArg Fin.val holdIndex
    simp [replacementLast] at hvals ⊢
  · intro j hjLower hjUpper
    rw [← corr.extensionKindsAgree j]
    apply available.interveningRevisiting j
    · omega
    · have hvals := congrArg Fin.val holdIndex
      simp only [Fin.val_succ] at hvals
      omega
    · exact hjUpper

private theorem helper_hreturnInOldEarlier_2009.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds) (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree
    G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc))
    (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
    (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (available :
    RevisitingExtensionCertificate corr.replacementSeries.data (Fin.last
    originalPrefix.rounds)),
  ∀ (oldi : Fin originalPrefix.rounds),
  oldi.succ =
    (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) →
  oldi.succ =
    (available.earlier : Fin (originalPrefix.rounds + (1 : ℕ))) →
  corr.replacementSeries.data.tree oldi.succ.castSucc = originalPrefix.series.data.tree
  oldi.succ.castSucc →
  available.returnVertex ∈ TreeSequenceVertexSet
    (originalPrefix.series.data.tree (available.earlier : Fin (originalPrefix.rounds + (1 :
    ℕ))).castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix corr available
  set earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier
  intro oldi holdIndex hnewIndex hbaseTree
  have htreeEarlier : corr.replacementSeries.data.tree
        earlierPrefix.castSucc =
      originalPrefix.series.data.tree
        earlierPrefix.castSucc := by
    calc
      corr.replacementSeries.data.tree
          earlierPrefix.castSucc =
          corr.replacementSeries.data.tree
            oldi.succ.castSucc := by
              congr 1
              exact congrArg Fin.castSucc hnewIndex.symm
      _ = originalPrefix.series.data.tree
            oldi.succ.castSucc := hbaseTree
      _ = originalPrefix.series.data.tree
            earlierPrefix.castSucc := by
              congr 1
              exact congrArg Fin.castSucc holdIndex
  rw [← htreeEarlier]
  simpa [earlierPrefix] using available.returnInEarlier

private theorem helper_hcomponentDistinct_2345.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [
    Fintype E] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating) (hroundLarge : (1 : ℕ) <
    ett.rounds),
  ∀ (sigmaPrev : PartialEdgeColoring E k) (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds).castSucc))
    (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
    (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (available :
    RevisitingExtensionCertificate corr.replacementSeries.data (Fin.last
    originalPrefix.rounds)),
  ∀ (oldi : Fin originalPrefix.rounds) (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)),
  oldi.succ = (available.earlier : Fin
    (originalPrefix.rounds + (1 : ℕ))) →
  available.returnVertex ∈ TreeSequenceVertexSet
    (originalPrefix.series.data.tree (available.earlier : Fin (originalPrefix.rounds + (1 :
    ℕ))).castSucc) →
  Sum.inl available.returnVertex ∈ TwoColorComponent G
    (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds) : Fin
    ett.rounds).castSucc) available.gamma available.delta (Sum.inr available.edge) →
  (∀ w ∈
    TreeSequenceVertexSet (originalPrefix.series.data.tree oldi.succ.castSucc), Sum.inl w ∈
    TwoColorComponent G (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin
    ett.rounds) : Fin ett.rounds).castSucc) available.gamma available.delta (Sum.inl
    oldChoice.vertex) ↔ w = oldChoice.vertex) →
  Sum.inl available.returnVertex ∉
    TwoColorComponent G sigmaPrev available.gamma available.delta (Sum.inl oldChoice.vertex) →
  TwoColorComponent G (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin
  ett.rounds) : Fin ett.rounds).castSucc) available.gamma available.delta (Sum.inl
  oldChoice.vertex) ≠ TwoColorComponent G (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ),
  by omega⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) available.gamma available.delta
  (Sum.inr available.edge) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge
  set q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds)
  intro sigmaPrev originalPrefix corr available
  set earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier
  intro oldi oldChoice holdIndex hreturnInOldEarlier hreturnInQ hcomponentOnly
      hreplacementRootAvoidsReturn heq
  have hreturnExitOriginal : Sum.inl available.returnVertex ∈
      TwoColorComponent G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta
        (Sum.inl oldChoice.vertex) := by
    rw [heq]
    exact hreturnInQ
  have hreturnExitSecond : Sum.inl available.returnVertex ∈
      TwoColorComponent G sigmaPrev available.gamma available.delta
        (Sum.inl oldChoice.vertex) := by
    have hreturnEq := (hcomponentOnly available.returnVertex
      (by simpa only [holdIndex] using hreturnInOldEarlier)).1
        hreturnExitOriginal
    rw [hreturnEq]
    rfl
  exact hreplacementRootAvoidsReturn hreturnExitSecond

private theorem helper_hindices_2256.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc)),
  originalPrefix.rounds = ett.rounds - (1 : ℕ) →
  ∀
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data
      replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds),
  earlierPrefix = oldi.succ →
  oldi.succ = earlierPrefix →
  ∀ (newi : Fin originalPrefix.rounds),
  earlierPrefix = newi.succ →
  newi.succ =
    earlierPrefix →
  oldi = newi := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      replacementLast available earlierPrefix oldi hbaseTarget holdIndex newi hnewTarget hnewIndex
  apply Fin.ext
  have holdVals := congrArg Fin.val holdIndex
  have hnewVals := congrArg Fin.val hnewIndex
  simp only [Fin.val_succ] at holdVals hnewVals
  omega

private theorem helper_hedgeSecond_2373.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E)
  (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
  (ch : MaximumDefectiveChoice G e0 X C phi) (second : PartialEdgeColoring E k),
  StableColoring X (insert ch.color C : Finset (Fin k)) ch.selected second →
  second ch.edge =
    some ch.color := by
  classical
  intro V E _ _ G k e0 X C phi ch second hsecondStable
  exact (hsecondStable.1 ch.edge
    ⟨ch.vertex, ch.vertexDefective.1, ch.edgeIncident⟩
    ⟨ch.color, Finset.mem_union_right _
      (Finset.mem_insert_self _ _), ch.edgeColor⟩).trans
        ch.edgeColor

private theorem helper_hne_2379.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E)
  (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
  (ch : MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
  g ∈ MissingColors G second ch.vertex →
  second ch.edge = some ch.color →
  g ≠ ch.color := by
  classical
  intro V E _ _ G k e0 X C phi ch g second hgSecond hedgeSecond heq
  have hpresent : g ∈ PresentColors G second ch.vertex := by
    simp only [PresentColors, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨ch.edge, ch.edgeIncident,
      by simpa [heq] using hedgeSecond⟩
  have hnotPresent : g ∉ PresentColors G second ch.vertex := by
    simpa [MissingColors] using hgSecond
  exact hnotPresent hpresent

private theorem helper_hreplacementColorConstant_2536.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc)),
  originalPrefix.rounds = ett.rounds - (1 : ℕ) →
  ∀
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data
      replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  (0 : ℕ) < (↑earlierPrefix : ℕ) →
  ∀ (oldi : Fin originalPrefix.rounds)
    (_ :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc))
    (_ : Fin k),
  earlierPrefix = oldi.succ →
  ∀ (_ : Fin k)
    (_ :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
          oldi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
        (corr.replacementSeries.data.coloring oldi.castSucc)),
  oldi.succ = earlierPrefix →
  corr.replacementSeries.data.tree oldi.succ.castSucc =
      originalPrefix.series.data.tree oldi.succ.castSucc →
  (
  ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series :
     TashkinovSeries G k rounds' e0 input')
     (a b : Fin (rounds' + (1 : ℕ))),
  (↑a : ℕ) ≤ (↑b : ℕ) →
  (
  ∀ (j : Fin (rounds' + (1 : ℕ))),
  (↑a : ℕ) < (↑j : ℕ) →
  (↑j : ℕ) ≤ (↑b : ℕ) →
  series.data.kind j = some
    TashkinovExtensionKind.RE) →
  series.data.coloring b = series.data.coloring a) →
  corr.replacementSeries.data.coloring replacementLast =
    corr.replacementSeries.data.coloring oldi.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      replacementLast available earlierPrefix hearlierPositive oldi oldChoice oldGamma
      hbaseTarget newGamma newChoicePE hnewIndex hbaseTree reIntervalColoring
  apply reIntervalColoring corr.replacementSeries
    oldi.succ replacementLast
  · have hvals := congrArg Fin.val hnewIndex
    simp [replacementLast] at hvals ⊢
  · intro j hjLower hjUpper
    apply available.interveningRevisiting j
    · omega
    · have hvals := congrArg Fin.val hnewIndex
      simp only [Fin.val_succ] at hvals
      omega
    · exact hjUpper

private theorem helper_hbaseColorConstant_2550.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc)),
  originalPrefix.rounds = ett.rounds - (1 : ℕ) →
  ∀
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data
      replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  (0 : ℕ) < (↑earlierPrefix : ℕ) →
  ∀ (oldi : Fin originalPrefix.rounds)
    (_ :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc))
    (_ : Fin k),
  earlierPrefix = oldi.succ →
  oldi.succ = earlierPrefix →
  ∀ (_ : Fin k)
    (_ :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
          oldi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
        (corr.replacementSeries.data.coloring oldi.castSucc)),
  corr.replacementSeries.data.tree oldi.succ.castSucc =
      originalPrefix.series.data.tree oldi.succ.castSucc →
  (
  ∀ {rounds' : ℕ} {input' : PartialEdgeColoring E k} (series :
     TashkinovSeries G k rounds' e0 input')
     (a b : Fin (rounds' + (1 : ℕ))),
  (↑a : ℕ) ≤ (↑b : ℕ) →
  (
  ∀ (j : Fin (rounds' + (1 : ℕ))),
  (↑a : ℕ) < (↑j : ℕ) →
  (↑j : ℕ) ≤ (↑b : ℕ) →
  series.data.kind j = some
    TashkinovExtensionKind.RE) →
  series.data.coloring b = series.data.coloring a) →
  originalPrefix.series.data.coloring replacementLast =
    originalPrefix.series.data.coloring oldi.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      replacementLast available earlierPrefix hearlierPositive oldi oldChoice oldGamma
      hbaseTarget holdIndex newGamma newChoicePE hbaseTree reIntervalColoring
  apply helper_hbaseColorConstant_1908 <;> assumption
private theorem helper_hnewDeltaSigmaPrev_2577.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc))
  (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast)
    (oldi : Fin originalPrefix.rounds)
    (newChoicePE :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
        (corr.replacementSeries.data.coloring oldi.castSucc)),
  newChoicePE.color ∈ MissingColors G (corr.replacementSeries.data.coloring oldi.succ)
      newChoicePE.vertex →
  newChoicePE.color = available.delta →
  corr.replacementSeries.data.coloring oldi.succ = sigmaPrev →
  available.delta ∈ MissingColors G sigmaPrev newChoicePE.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix corr
      replacementLast available oldi newChoicePE hnewDeltaMissing hnewDeltaAvailable
      hnewPostSigmaPrev
  have hm := hnewDeltaMissing
  rw [hnewDeltaAvailable] at hm
  exact Eq.mp (congrArg (fun phi => available.delta ∈
    MissingColors G phi newChoicePE.vertex)
      hnewPostSigmaPrev) hm

private theorem helper_hnewGammaSigmaPrevNot_2584.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc))
  (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast)
    (oldi : Fin originalPrefix.rounds) (newGamma : Fin k)
    (newChoicePE :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
        (corr.replacementSeries.data.coloring oldi.castSucc)),
  newGamma ∉ MissingColors G (corr.replacementSeries.data.coloring oldi.succ)
      newChoicePE.vertex →
  newGamma = available.gamma →
  corr.replacementSeries.data.coloring oldi.succ = sigmaPrev →
  available.gamma ∉ MissingColors G sigmaPrev newChoicePE.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix corr
      replacementLast available oldi newGamma newChoicePE hnewGammaNotMissing hnewGammaAvailable
      hnewPostSigmaPrev
  have hm := hnewGammaNotMissing
  rw [hnewGammaAvailable] at hm
  exact Eq.mp (congrArg (fun phi => available.gamma ∉
    MissingColors G phi newChoicePE.vertex)
      hnewPostSigmaPrev) hm

private theorem helper_holdDeltaOriginal_2591.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ), by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
    (originalPrefix :
      ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin ett.rounds).castSucc))
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast)
    (oldi : Fin originalPrefix.rounds)
    (oldChoice :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc)),
  oldChoice.color ∈ MissingColors G (originalPrefix.series.data.coloring oldi.succ)
      oldChoice.vertex →
  oldChoice.color = available.delta →
  originalPrefix.series.data.coloring oldi.succ = ett.series.data.coloring q.castSucc →
  available.delta ∈ MissingColors G (ett.series.data.coloring q.castSucc)
      oldChoice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix corr
      replacementLast available oldi oldChoice holdDeltaMissing holdDeltaAvailable holdPostOriginal
  have hm := holdDeltaMissing
  rw [holdDeltaAvailable] at hm
  exact Eq.mp (congrArg (fun phi => available.delta ∈
    MissingColors G phi oldChoice.vertex)
      holdPostOriginal) hm

private theorem helper_holdGammaOriginalNot_2599.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ), by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
    (originalPrefix :
      ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin ett.rounds).castSucc))
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast)
    (oldi : Fin originalPrefix.rounds)
    (oldChoice :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc)),
  ∀ oldGamma ∉ MissingColors G (originalPrefix.series.data.coloring oldi.succ)
      oldChoice.vertex,
  oldGamma = available.gamma →
  originalPrefix.series.data.coloring oldi.succ = ett.series.data.coloring q.castSucc →
  available.gamma ∉ MissingColors G (ett.series.data.coloring q.castSucc)
      oldChoice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix corr
      replacementLast available oldi oldChoice oldGamma holdGammaNotMissing holdGammaAvailable
      holdPostOriginal
  have hm := holdGammaNotMissing
  rw [holdGammaAvailable] at hm
  exact Eq.mp (congrArg (fun phi => available.gamma ∉
    MissingColors G phi oldChoice.vertex)
      holdPostOriginal) hm

private theorem helper_missingPreviousToTn_2668.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ), by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  TreeSequenceInitialSegment (ett.series.data.tree q.castSucc.castSucc) (ett.series.data.tree
      q.succ.castSucc) →
  ∀ c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc) (ett.series.data.tree
      q.castSucc.castSucc),
    c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc) (ett.series.data.tree
        q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q hpreviousToTn c hc
  simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
  obtain ⟨v, hv, hvc⟩ := hc
  exact ⟨v,
    TreeSequenceInitialSegmentVertexSetSubset
      hpreviousToTn hv, hvc⟩

private theorem helper_hreturnInQ_2783.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ), by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
    (originalPrefix :
      ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin ett.rounds).castSucc))
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let originalReturnGraph : SimpleGraph (V ⊕ E) :=
    TwoColorIncidenceGraph G (ett.series.data.coloring q.castSucc) available.gamma
        available.delta;
  ∀ (returnEdgeTransfer : ∀ edge ∈ available.returnPath.edges, edge ∈
      originalReturnGraph.edgeSet),
  let _ : originalReturnGraph.Walk (Sum.inr available.edge) (Sum.inl
      available.returnVertex) :=
    available.returnPath.transfer originalReturnGraph returnEdgeTransfer;
  Sum.inl available.returnVertex ∈
    TwoColorComponent G (ett.series.data.coloring q.castSucc) available.gamma
        available.delta
      (Sum.inr available.edge) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix corr
      replacementLast available originalReturnGraph returnEdgeTransfer originalReturnPath
  change originalReturnGraph.connectedComponentMk
      (Sum.inl available.returnVertex) =
    originalReturnGraph.connectedComponentMk
      (Sum.inr available.edge)
  exact (SimpleGraph.ConnectedComponent.sound
    originalReturnPath.reachable).symm

private theorem helper_hedgeOriginalActive_2794.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ), by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
    (originalPrefix :
      ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin ett.rounds).castSucc))
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  (
  ∀ (f : E),
  Sum.inr f ∈ available.returnPath.support →
  TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) f ∧
    (sigmaPrev f = some available.gamma ∨ sigmaPrev f = some available.delta)) →
  (
  ∀ (f : E),
  Sum.inr f ∈ available.returnPath.support →
  sigmaPrev f =
    ett.series.data.coloring q.castSucc f) →
  ett.series.data.coloring q.castSucc available.edge = some available.gamma ∨
    ett.series.data.coloring q.castSucc available.edge = some available.delta := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix corr
      replacementLast available replacementReturnEdgeData copyReturnEdge
  have hsupport : Sum.inr available.edge ∈
      available.returnPath.support := by simp
  have hdata :=
    (replacementReturnEdgeData available.edge hsupport).2
  have hcopy := copyReturnEdge available.edge hsupport
  rw [hcopy] at hdata
  exact hdata

private theorem helper_houtsideInQ_2806.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ), by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
    (originalPrefix :
      ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin ett.rounds).castSucc))
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  ett.series.data.coloring q.castSucc available.edge = some available.gamma ∨
      ett.series.data.coloring q.castSucc available.edge = some available.delta →
  Sum.inl available.outsideEndpoint ∈
    TwoColorComponent G (ett.series.data.coloring q.castSucc) available.gamma
        available.delta
      (Sum.inr available.edge) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix corr
      replacementLast available hedgeOriginalActive
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  have houtIncident : Incident G available.outsideEndpoint
      available.edge := by
    unfold Incident
    rw [available.edgeEnds]
    exact Sym2.mem_mk_right _ _
  simp [TwoColorIncidenceGraph,
    houtIncident, hedgeOriginalActive]

private theorem helper_hreplacementRootAvoidsReturn_2970.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc))
  (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
    (oldChoice :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc)),
  oldi.succ = earlierPrefix →
  corr.replacementSeries.data.tree oldi.succ.castSucc = originalPrefix.series.data.tree
      oldi.succ.castSucc →
  available.returnVertex ∈ TreeSequenceVertexSet (originalPrefix.series.data.tree
      earlierPrefix.castSucc) →
  available.returnVertex ≠ oldChoice.vertex →
  (∀ w ∈ TreeSequenceVertexSet (corr.replacementSeries.data.tree
      oldi.succ.castSucc),
      Sum.inl w ∈ TwoColorComponent G sigmaPrev available.gamma available.delta
          (Sum.inl oldChoice.vertex) ↔
        w = oldChoice.vertex) →
  Sum.inl available.returnVertex ∉
    TwoColorComponent G sigmaPrev available.gamma available.delta (Sum.inl
        oldChoice.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix corr
      replacementLast available earlierPrefix oldi oldChoice holdIndex hbaseTree
      hreturnInOldEarlier hreturnNeOld hreplacementComponentOnly hreturn
  apply hreturnNeOld
  apply (hreplacementComponentOnly available.returnVertex ?_).1 hreturn
  rw [hbaseTree]
  simpa only [holdIndex] using hreturnInOldEarlier

private theorem helper_branch_3047.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc))
  (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
  (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
    (_ :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc))
    (_ _ : Fin k)
    (_ :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
        (corr.replacementSeries.data.coloring oldi.castSucc))
    (_ :
      corr.replacementSeries.data.tree oldi.succ.castSucc = originalPrefix.series.data.tree
          oldi.succ.castSucc)
    (horiginalRoundsLess : originalPrefix.rounds < ett.rounds),
  let oldEarlier : Fin (ett.rounds + (1 : ℕ)) :=
    Fin.castLE
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      earlierPrefix;
  ett.series.data.kind oldEarlier = some TashkinovExtensionKind.PE →
  ett.series.data.kind (0 : Fin (ett.rounds + (1 : ℕ))) = none →
  oldEarlier = (0 : Fin (ett.rounds + (1 : ℕ))) →
  False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      replacementLast available earlierPrefix oldi oldChoice oldGamma newGamma newChoicePE
      hbaseTree horiginalRoundsLess oldEarlier hfullEarlierKind initialKindFull hfullTarget
  have hk : ett.series.data.kind 0 =
      some TashkinovExtensionKind.PE := by
    rw [← hfullTarget]
    exact hfullEarlierKind
  have hbad := initialKindFull.symm.trans hk
  simp at hbad

private theorem helper_branch_3057.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc))
  (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
  (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
    (_ :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc))
    (_ _ : Fin k)
    (_ :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
        (corr.replacementSeries.data.coloring oldi.castSucc))
    (_ :
      corr.replacementSeries.data.tree oldi.succ.castSucc = originalPrefix.series.data.tree
          oldi.succ.castSucc)
    (horiginalRoundsLess : originalPrefix.rounds < ett.rounds),
  let oldEarlier : Fin (ett.rounds + (1 : ℕ)) :=
    Fin.castLE
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      earlierPrefix;
  ett.series.data.kind oldEarlier = some TashkinovExtensionKind.PE →
  ∀ (fulli : Fin ett.rounds),
  ett.series.data.kind fulli.succ = some TashkinovExtensionKind.SE →
  oldEarlier =
    fulli.succ →
  False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      replacementLast available earlierPrefix oldi oldChoice oldGamma newGamma newChoicePE
      hbaseTree horiginalRoundsLess oldEarlier hfullEarlierKind fulli fullCurrentKind hfullTarget
  have hk : ett.series.data.kind fulli.succ =
      some TashkinovExtensionKind.PE := by
    rw [← hfullTarget]
    exact hfullEarlierKind
  have hbad := fullCurrentKind.symm.trans hk
  cases hbad

private theorem helper_branch_3071.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive T
              omega⟩ :
            Fin ett.rounds).castSucc))
  (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
  (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
  ∀ (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
    (_ :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc))
    (_ _ : Fin k)
    (_ :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
        (corr.replacementSeries.data.coloring oldi.castSucc))
    (_ :
      corr.replacementSeries.data.tree oldi.succ.castSucc = originalPrefix.series.data.tree
          oldi.succ.castSucc)
    (horiginalRoundsLess : originalPrefix.rounds < ett.rounds),
  let oldEarlier : Fin (ett.rounds + (1 : ℕ)) :=
    Fin.castLE
      (by
        have := GoldbergSeymour.TreeSequence.positive T
        omega)
      earlierPrefix;
  ett.series.data.kind oldEarlier = some TashkinovExtensionKind.PE →
  ∀ (fulli : Fin ett.rounds),
  ett.series.data.kind fulli.succ = some TashkinovExtensionKind.RE →
  oldEarlier =
    fulli.succ →
  False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix hr corr
      replacementLast available earlierPrefix oldi oldChoice oldGamma newGamma newChoicePE
      hbaseTree horiginalRoundsLess oldEarlier hfullEarlierKind fulli fullCurrentKind hfullTarget
  have hk : ett.series.data.kind fulli.succ =
      some TashkinovExtensionKind.PE := by
    rw [← hfullTarget]
    exact hfullEarlierKind
  have hbad := fullCurrentKind.symm.trans hk
  cases hbad

private theorem helper_branch_3084.{u_1, u_2} :
    helperBranch3084Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix hr
      hprefixTrees hprefixData corr noRevisiting replacementLast hlastMap hreplacementCurrentTree
      available earlierPrefix oldi oldChoice oldGamma oldCurrentStored oldCurrentEdges
      hbaseTarget holdIndex newGamma newChoicePE hbaseTree transportChoiceFields pePostStatus
      holdDeltaMissing holdGammaNotMissing holdDeltaAvailable holdGammaAvailable
      hreturnInOldEarlier originalReturnGraph returnEdgeTransfer originalReturnPath
      horiginalReturnIsPath horiginalReturnSupport hreturnInQ houtsideInQ horiginalRoundsLess
      originalCycle hcycleFull oldEarlier hfullEarlierKind fulli fullChoice fullGamma
      fullGammaRule fullSecond fullSecondProper fullSecondStable fullCurrentColoring
      fullCurrentStored fullCurrentEdges fullCurrentDelta fullCurrentGamma hfullTarget
  exact helper_branch_1721 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge)
      (@sigmaPrev) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr) (@noRevisiting)
      (@hlastMap) (@hreplacementCurrentTree) (@available) (@oldi) (@oldChoice) (@oldGamma)
      (@oldCurrentStored) (@oldCurrentEdges) (@hbaseTarget) (@holdIndex) (@newGamma)
      (@newChoicePE) (@hbaseTree) (@transportChoiceFields) (@pePostStatus) (@holdDeltaMissing)
      (@holdGammaNotMissing) (@holdDeltaAvailable) (@holdGammaAvailable) (@hreturnInOldEarlier)
      (@returnEdgeTransfer) (@horiginalReturnIsPath) (@horiginalReturnSupport) (@hreturnInQ)
      (@houtsideInQ) (@horiginalRoundsLess) (@originalCycle) (@hcycleFull) (@hfullEarlierKind)
      (@fulli) (@fullChoice) (@fullGamma) (@fullGammaRule) (@fullSecond) (@fullSecondProper)
      (@fullSecondStable) (@fullCurrentColoring) (@fullCurrentStored) (@fullCurrentEdges)
      (@fullCurrentDelta) (@fullCurrentGamma) (@hfullTarget)

private theorem helper_pePostStatus_3432.{u_1, u_2} :
    helperPePostStatus3432Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 X C phi ch g second hsecondProper hsecondStable hgSelected
  dsimp
  have hgSecond : g ∈ MissingColors G second ch.vertex := by
    rw [hsecondStable.2 ch.vertex ch.vertexDefective.1]
    exact hgSelected
  have hedgeSecond : second ch.edge = some ch.color := by
    apply helper_hedgeSecond_2373; assumption
  have hne : g ≠ ch.color := by
    apply helper_hne_2379 <;> assumption
  have hedgeComponent : Sum.inr ch.edge ∈
      TwoColorComponent G second g ch.color
        (Sum.inl ch.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph,
      ch.edgeIncident, hedgeSecond]
  have hmissingDelta : ch.color ∈ MissingColors G
      (TwoColorComponentSwap G second g ch.color
        (Sum.inl ch.vertex)) ch.vertex := by
    exact (TwoColorComponentSwapMissingBehavior G second g
      ch.color hne hsecondProper (Sum.inl ch.vertex)).2.1
        ch.vertex rfl hgSecond
  have hedgePost : TwoColorComponentSwap G second g ch.color
      (Sum.inl ch.vertex) ch.edge = some g := by
    simp [TwoColorComponentSwap, hedgeComponent, hedgeSecond,
      hne.symm]
  have hgammaPresent : g ∈ PresentColors G
      (TwoColorComponentSwap G second g ch.color
        (Sum.inl ch.vertex)) ch.vertex := by
    simp only [PresentColors, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨ch.edge, ch.edgeIncident, hedgePost⟩
  exact ⟨hmissingDelta,
    by simpa [MissingColors] using hgammaPresent, hne⟩

private theorem helper_continuation_4070.{u_1, u_2} :
    helperContinuation4070Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge hlower q sigmaPrev previousProper
      previousOneUncolored originalPrefix hr hprefixMP hprefixTrees hprefixData corr hcorrMP
      noRevisiting replacementLast horiginalPositive hlastMap hreplacementCurrentTree peRootOnly
      available earlierPrefix hbaseEarlierKind oldi oldChoice oldGamma oldCurrentProper
      oldCurrentOne oldCurrentStored oldCurrentEdges oldCurrentKind oldCurrentVertex
      oldCurrentDelta oldCurrentGamma hbaseTarget holdIndex newGamma newChoicePE newCurrentProper
      newCurrentOne newCurrentKind newCurrentVertex newCurrentDelta newCurrentGamma hbaseTree
      oldChoiceOnNew transportChoiceFields holdColorCast pePostStatus holdDeltaMissing
      holdGammaNotMissing holdColorNe hnewColorNe hidentifiedDelta hidentifiedGamma
      hnewDeltaAvailable hnewGammaAvailable holdDeltaAvailable holdGammaAvailable hnewVertexOld
      hnewPostSigmaPrev hbaseFinalColor holdPostOriginal holdDeltaOriginal hgammaDeltaNe
      holdVertexFinal hreturnInOldEarlier hreturnInFinal originalReturnGraph returnEdgeTransfer
      originalReturnPath horiginalReturnIsPath horiginalReturnSupport hreturnInQ houtsideInQ
      hpathComponent hpathMeetsFinal hreplacementLeaf
  have hreturnNeOld : available.returnVertex ≠
      oldChoice.vertex := by
    apply helper_hreturnNeOld_2171 <;> assumption
  have horiginalRoundsLess : originalPrefix.rounds < ett.rounds := by
    rw [hr]
    omega
  have holdRootOnly := peRootOnly originalPrefix horiginalPositive
    horiginalRoundsLess hprefixMP originalPrefix.rounds
    originalPrefix.series rfl HEq.rfl oldi.succ oldChoice.vertex
    oldGamma oldChoice.color (by simp) oldCurrentKind
    oldCurrentVertex oldCurrentGamma oldCurrentDelta
    oldCurrentProper oldCurrentOne
  have hreplacementPositive : 0 < corr.replacementETT.rounds := by
    rw [corr.rungAgreement]
    exact horiginalPositive
  have hreplacementLess : corr.replacementETT.rounds < ett.rounds := by
    rw [corr.rungAgreement]
    exact horiginalRoundsLess
  have hnewRootOnly := peRootOnly corr.replacementETT
    hreplacementPositive hreplacementLess hcorrMP originalPrefix.rounds
    corr.replacementSeries corr.rungAgreement corr.seriesPresentation
    oldi.succ newChoicePE.vertex newGamma newChoicePE.color
    (by simp) newCurrentKind newCurrentVertex newCurrentGamma
    newCurrentDelta newCurrentProper newCurrentOne
  have hcomponentOnly : ∀ w,
      w ∈ TreeSequenceVertexSet
        (originalPrefix.series.data.tree oldi.succ.castSucc) →
      (Sum.inl w ∈ TwoColorComponent G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta (Sum.inl oldChoice.vertex) ↔
        w = oldChoice.vertex) := by
    simpa only [holdPostOriginal, holdGammaAvailable,
      holdDeltaAvailable] using holdRootOnly
  have hreplacementComponentOnly : ∀ w,
      w ∈ TreeSequenceVertexSet
        (corr.replacementSeries.data.tree oldi.succ.castSucc) →
      (Sum.inl w ∈ TwoColorComponent G sigmaPrev
        available.gamma available.delta (Sum.inl oldChoice.vertex) ↔
        w = oldChoice.vertex) := by
    simpa only [hnewPostSigmaPrev, hnewGammaAvailable,
      hnewDeltaAvailable, hnewVertexOld] using hnewRootOnly
  have hreplacementRootAvoidsReturn :
      Sum.inl available.returnVertex ∉ TwoColorComponent G sigmaPrev
        available.gamma available.delta (Sum.inl oldChoice.vertex) := by
    apply helper_hreplacementRootAvoidsReturn_2970 <;> assumption
  have hcomponentDistinct :=
    helper_hcomponentDistinct_2345 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@available) (@oldi) (@oldChoice)
        (@holdIndex) (@hreturnInOldEarlier) (@hreturnInQ) (@hcomponentOnly)
        (@hreplacementRootAvoidsReturn)
  have hQMeetsFinal : ∃ v ∈ TreeSequenceVertexSet
      (originalPrefix.series.data.tree
        (Fin.last (originalPrefix.rounds + 1))),
      Sum.inl v ∈ TwoColorComponent G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta
        (Sum.inr available.edge) :=
    ⟨available.returnVertex, hreturnInFinal, hreturnInQ⟩
  have hlowerColor : originalPrefix.series.data.coloring
        (Fin.last originalPrefix.rounds) =
      ett.series.data.coloring q.castSucc := by
    simpa [replacementLast] using hbaseFinalColor
  have hstableLower : StableColoring
      (originalPrefix.series.data.tree
        (Fin.last (originalPrefix.rounds + 1)))
      (TashkinovStoredColors originalPrefix.series.data
        (Fin.last originalPrefix.rounds))
      (originalPrefix.series.data.coloring
        (Fin.last originalPrefix.rounds))
      (ett.series.data.coloring q.castSucc) := by
    rw [hlowerColor]
    exact ⟨(by intros; rfl), (by intros; rfl)⟩
  have hdeltaLower : available.delta ∈ TreeMissingColors
      (ett.series.data.coloring q.castSucc)
      (originalPrefix.series.data.tree
        (Fin.last (originalPrefix.rounds + 1))) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨oldChoice.vertex, holdVertexFinal,
      holdDeltaOriginal⟩
  have hlowerPackage := hlower originalPrefix
    horiginalPositive horiginalRoundsLess hprefixMP
  have hinterchangeLower := hlowerPackage.1
    (ett.series.data.coloring q.castSucc) previousProper
    previousOneUncolored hstableLower available.gamma
    available.delta (Or.inr hdeltaLower)
  have hcycleComponent :=
    TwoColorInterchangeableDistinctComponentCycle G
      (originalPrefix.series.data.tree
        (Fin.last (originalPrefix.rounds + 1)))
      (ett.series.data.coloring q.castSucc)
      available.gamma available.delta previousProper
      (Sum.inl oldChoice.vertex) (Sum.inr available.edge)
      hpathComponent.1 hinterchangeLower hpathMeetsFinal
      hQMeetsFinal hcomponentDistinct
  obtain ⟨originalCycle, hcycleFull⟩ := hcycleComponent
  let oldEarlier : Fin (ett.rounds + 1) :=
    Fin.castLE (by omega) earlierPrefix
  have holdEarlierMap : oldEarlier =
      Fin.castLE (by omega) earlierPrefix := rfl
  have hfullEarlierKind : ett.series.data.kind oldEarlier =
      some TashkinovExtensionKind.PE := by
    rw [holdEarlierMap, ← (hprefixData earlierPrefix).2.2.2.1]
    exact hbaseEarlierKind
  have hfullStep := ett.series.certified oldEarlier
  generalize hfullTarget : oldEarlier = fullTarget at hfullStep
  cases hfullStep with
  | initial tripleFull seedLengthFull initialColoringFull
      initialStoredFull initialEdgesFull initialKindFull
      initialVertexFull initialOutsideFull initialDeltaFull
      initialGammaFull initialClosureFull =>
          exact helper_branch_3047 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
              (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@available) (@oldi)
              (@oldChoice) (@oldGamma) (@newGamma) (@newChoicePE) (@hbaseTree)
              (@horiginalRoundsLess) (@hfullEarlierKind) (@initialKindFull) (@hfullTarget)
  | SE fulli fullPreviousProper fullPreviousOne
      fullPreviousClosed fullPreviousNotStrong fullNoRE
      fullChoice fullAlternative fullCurrentColoring
      fullCurrentStored fullCurrentEdges fullCurrentKind
      fullCurrentVertex fullCurrentOutside fullCurrentDelta
      fullCurrentGamma fullAdjoined fullAdjoinedExactly
      fullClosedExtension fullOrderedExtension
      fullStrictExtension =>
          exact helper_branch_3057 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
              (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@available) (@oldi)
              (@oldChoice) (@oldGamma) (@newGamma) (@newChoicePE) (@hbaseTree)
              (@horiginalRoundsLess) (@hfullEarlierKind) (@fulli) (@fullCurrentKind) (@hfullTarget)
  | RE fulli fullPreviousProper fullPreviousOne
      fullPreviousClosed fullPreviousNotStrong fullAvailable
      fullCurrentColoring fullCurrentStored fullCurrentEdges
      fullCurrentKind fullCurrentVertex fullCurrentOutside
      fullCurrentDelta fullCurrentGamma fullAdjoined
      fullAdjoinedExactly fullClosedExtension
      fullOrderedExtension fullStrictExtension =>
          exact helper_branch_3071 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
              (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@available) (@oldi)
              (@oldChoice) (@oldGamma) (@newGamma) (@newChoicePE) (@hbaseTree)
              (@horiginalRoundsLess) (@hfullEarlierKind) (@fulli) (@fullCurrentKind) (@hfullTarget)
  | PE fulli fullPreviousProper fullPreviousOne
      fullPreviousClosed fullPreviousNotStrong fullNoRE
      fullChoice fullAlternativeFails fullGamma fullGammaRule
      fullSecond fullSecondProper fullSecondOne
      fullSecondStable fullExit fullCurrentColoring
      fullCurrentProper fullCurrentOne fullCurrentStored
      fullCurrentEdges fullCurrentKind fullCurrentVertex
      fullCurrentOutside fullCurrentDelta fullCurrentGamma
      fullClosedExtension fullOrderedExtension
      fullStrictExtension =>
          exact helper_branch_3084 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
              (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData)
              (@corr) (@noRevisiting) (@hlastMap) (@hreplacementCurrentTree) (@available) (@oldi)
              (@oldChoice) (@oldGamma) (@oldCurrentStored) (@oldCurrentEdges) (@hbaseTarget)
              (@holdIndex) (@newGamma) (@newChoicePE) (@hbaseTree) (@transportChoiceFields)
              (@pePostStatus) (@holdDeltaMissing) (@holdGammaNotMissing) (@holdDeltaAvailable)
              (@holdGammaAvailable) (@hreturnInOldEarlier) (@returnEdgeTransfer)
              (@horiginalReturnIsPath) (@horiginalReturnSupport) (@hreturnInQ) (@houtsideInQ)
              (@horiginalRoundsLess) (@originalCycle) (@hcycleFull) (@hfullEarlierKind) (@fulli)
              (@fullChoice) (@fullGamma) (@fullGammaRule) (@fullSecond) (@fullSecondProper)
              (@fullSecondStable) (@fullCurrentColoring) (@fullCurrentStored) (@fullCurrentEdges)
              (@fullCurrentDelta) (@fullCurrentGamma) (@hfullTarget)

private theorem helper_continuation_4611.{u_1, u_2} :
    helperContinuation4611Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge hlower q sigmaPrev hsigmaPrevProper
      previousProper previousOneUncolored originalPrefix hr hprefixMP hprefixTrees hprefixData
      corr hcorrMP noRevisiting replacementLast hcorrFinalColor horiginalPositive hlastMap
      hreplacementCurrentTree peRootOnly available earlierPrefix hbaseEarlierKind oldi oldChoice
      oldGamma oldCurrentProper oldCurrentOne oldCurrentStored oldCurrentEdges oldCurrentKind
      oldCurrentVertex oldCurrentDelta oldCurrentGamma hbaseTarget holdIndex newGamma newChoicePE
      newCurrentProper newCurrentOne newCurrentKind newCurrentVertex newCurrentDelta
      newCurrentGamma hbaseTree oldChoiceOnNew transportChoiceFields holdColorCast pePostStatus
      holdDeltaMissing holdGammaNotMissing holdColorNe hnewColorNe hidentifiedDelta
      hidentifiedGamma hnewDeltaAvailable hnewGammaAvailable holdDeltaAvailable
      holdGammaAvailable hnewVertexOld hnewPostSigmaPrev hbaseFinalColor holdPostOriginal
      hnewDeltaSigmaPrev holdDeltaOriginal holdGammaOriginalNot hgammaDeltaNe holdVertexFinal
      hreturnInOldEarlier hreturnInFinal replacementReturnEdgeData copyReturnEdge
  let replacementReturnGraph := TwoColorIncidenceGraph G
    (corr.replacementSeries.data.coloring replacementLast)
    available.gamma available.delta
  let originalReturnGraph := TwoColorIncidenceGraph G
    (ett.series.data.coloring q.castSucc) available.gamma
    available.delta
  have returnEdgeTransfer :=
    helper_returnEdgeTransfer_1317 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@hcorrFinalColor) (@available)
        (@copyReturnEdge)
  let originalReturnPath :=
    available.returnPath.transfer originalReturnGraph
      returnEdgeTransfer
  have horiginalReturnIsPath : originalReturnPath.IsPath :=
    available.returnPathIsPath.transfer returnEdgeTransfer
  have horiginalReturnSupport : ∀ z,
      z ∈ originalReturnPath.support ↔
        z ∈ available.returnPath.support := by
    intro z
    simp [originalReturnPath]
  have hreturnInQ :=
    helper_hreturnInQ_2783 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge)
        (@sigmaPrev) (@originalPrefix) (@corr) (@available) (@returnEdgeTransfer)
  have hedgeOriginalActive :=
    helper_hedgeOriginalActive_2794 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@available)
        (@replacementReturnEdgeData) (@copyReturnEdge)
  have houtsideInQ :=
    helper_houtsideInQ_2806 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge)
        (@sigmaPrev) (@originalPrefix) (@corr) (@available) (@hedgeOriginalActive)
  have hgammaPresentOriginal : available.gamma ∈
      PresentColors G (ett.series.data.coloring q.castSucc)
        oldChoice.vertex := by
    simpa [MissingColors] using holdGammaOriginalNot
  obtain ⟨pathEdge, hpathEdgeIncident, hpathEdgeColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter,
      Finset.mem_univ, true_and] using hgammaPresentOriginal
  have hpathEdgeComponent : Sum.inr pathEdge ∈
      TwoColorComponent G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta
        (Sum.inl oldChoice.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph,
      hpathEdgeIncident, hpathEdgeColor]
  have hleafDegree : @SimpleGraph.degree _
      (TwoColorIncidenceGraph G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta)
      (Sum.inl oldChoice.vertex) (Fintype.ofFinite _) ≤ 1 := by
    have hgraphSwapOrder :
        TwoColorIncidenceGraph G
            (ett.series.data.coloring q.castSucc)
            available.delta available.gamma =
          TwoColorIncidenceGraph G
            (ett.series.data.coloring q.castSucc)
            available.gamma available.delta := by
      ext x y
      cases x <;> cases y <;>
        simp [TwoColorIncidenceGraph, or_comm]
    rw [← hgraphSwapOrder]
    exact MissingColorIncidenceEndpoint G
      (ett.series.data.coloring q.castSucc) available.delta
      available.gamma hgammaDeltaNe.symm previousProper
      oldChoice.vertex holdDeltaOriginal
  have hleaf : Set.Subsingleton
      ((TwoColorIncidenceGraph G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta).neighborSet
          (Sum.inl oldChoice.vertex)) := by
    let : Fintype
        ((TwoColorIncidenceGraph G
          (ett.series.data.coloring q.castSucc)
          available.gamma available.delta).neighborSet
            (Sum.inl oldChoice.vertex)) := Fintype.ofFinite _
    rw [← SimpleGraph.card_neighborSet_eq_degree] at hleafDegree
    have hsub := Fintype.card_le_one_iff.mp hleafDegree
    intro a ha b hb
    exact congrArg Subtype.val
      (hsub ⟨a, ha⟩ ⟨b, hb⟩)
  have hpathComponent : TwoColorNontrivialPathComponent G
      (ett.series.data.coloring q.castSucc)
      available.gamma available.delta
      (Sum.inl oldChoice.vertex) := by
    refine ⟨⟨hgammaDeltaNe, Sum.inl oldChoice.vertex,
      rfl, hleaf⟩, pathEdge, hpathEdgeComponent⟩
  have hpathMeetsFinal : ∃ v ∈ TreeSequenceVertexSet
      (originalPrefix.series.data.tree
        (Fin.last (originalPrefix.rounds + 1))),
      Sum.inl v ∈ TwoColorComponent G
        (ett.series.data.coloring q.castSucc)
        available.gamma available.delta
        (Sum.inl oldChoice.vertex) :=
    ⟨oldChoice.vertex, holdVertexFinal, rfl⟩
  have hreplacementLeafDegree : @SimpleGraph.degree _
      (TwoColorIncidenceGraph G
        (corr.replacementSeries.data.coloring replacementLast)
        available.gamma available.delta)
      (Sum.inl newChoicePE.vertex) (Fintype.ofFinite _) ≤ 1 := by
    have hgraphSwapOrder :
        TwoColorIncidenceGraph G sigmaPrev available.delta
            available.gamma =
          TwoColorIncidenceGraph G sigmaPrev available.gamma
            available.delta := by
      ext x y
      cases x <;> cases y <;>
        simp [TwoColorIncidenceGraph, or_comm]
    have hdegree : @SimpleGraph.degree _
        (TwoColorIncidenceGraph G sigmaPrev available.gamma
          available.delta) (Sum.inl newChoicePE.vertex)
          (Fintype.ofFinite _) ≤ 1 := by
      rw [← hgraphSwapOrder]
      exact MissingColorIncidenceEndpoint G sigmaPrev
        available.delta available.gamma hgammaDeltaNe.symm
        hsigmaPrevProper newChoicePE.vertex hnewDeltaSigmaPrev
    have hcolorEq :
        corr.replacementSeries.data.coloring replacementLast =
          sigmaPrev := by
      simpa [replacementLast] using hcorrFinalColor
    rw [hcolorEq]
    exact hdegree
  have hreplacementLeaf : Set.Subsingleton
      ((TwoColorIncidenceGraph G
        (corr.replacementSeries.data.coloring replacementLast)
        available.gamma available.delta).neighborSet
          (Sum.inl newChoicePE.vertex)) := by
    let : Fintype
        ((TwoColorIncidenceGraph G
          (corr.replacementSeries.data.coloring replacementLast)
          available.gamma available.delta).neighborSet
            (Sum.inl newChoicePE.vertex)) := Fintype.ofFinite _
    rw [← SimpleGraph.card_neighborSet_eq_degree] at hreplacementLeafDegree
    have hsub := Fintype.card_le_one_iff.mp
      hreplacementLeafDegree
    intro a ha b hb
    exact congrArg Subtype.val
      (hsub ⟨a, ha⟩ ⟨b, hb⟩)
  exact helper_continuation_4070 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@hroundLarge) (@hlower) (@sigmaPrev) (@previousProper) (@previousOneUncolored)
      (@originalPrefix) (@hr) (@hprefixMP) (@hprefixTrees) (@hprefixData) (@corr) (@hcorrMP)
      (@noRevisiting) (@horiginalPositive) (@hlastMap) (@hreplacementCurrentTree) (@peRootOnly)
      (@available) (@hbaseEarlierKind) (@oldi) (@oldChoice) (@oldGamma) (@oldCurrentProper)
      (@oldCurrentOne) (@oldCurrentStored) (@oldCurrentEdges) (@oldCurrentKind)
      (@oldCurrentVertex) (@oldCurrentDelta) (@oldCurrentGamma) (@hbaseTarget) (@holdIndex)
      (@newGamma) (@newChoicePE) (@newCurrentProper) (@newCurrentOne) (@newCurrentKind)
      (@newCurrentVertex) (@newCurrentDelta) (@newCurrentGamma) (@hbaseTree)
      (@transportChoiceFields) (@holdColorCast) (@pePostStatus) (@holdDeltaMissing)
      (@holdGammaNotMissing) (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta)
      (@hidentifiedGamma) (@hnewDeltaAvailable) (@hnewGammaAvailable) (@holdDeltaAvailable)
      (@holdGammaAvailable) (@hnewVertexOld) (@hnewPostSigmaPrev) (@hbaseFinalColor)
      (@holdPostOriginal) (@holdDeltaOriginal) (@hgammaDeltaNe) (@holdVertexFinal)
      (@hreturnInOldEarlier) (@hreturnInFinal) (@returnEdgeTransfer) (@horiginalReturnIsPath)
      (@horiginalReturnSupport) (@hreturnInQ) (@houtsideInQ) (@hpathComponent) (@hpathMeetsFinal)
      (@hreplacementLeaf)

private theorem helper_hmissingForIdentification_5050.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds) (sigmaPrev : PartialEdgeColoring E k)
  (originalPrefix :
    ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ), by
              omega⟩ :
            Fin ett.rounds).castSucc))
  (corr :
    CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
      (ett.series.data.tree (Fin.last ett.rounds).castSucc))
  (oldi : Fin originalPrefix.rounds)
  (oldChoice :
    MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
      (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
      (originalPrefix.series.data.coloring oldi.castSucc))
  (newChoicePE :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
      (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
      (corr.replacementSeries.data.coloring oldi.castSucc))
  (hbaseTree :
    corr.replacementSeries.data.tree oldi.succ.castSucc = originalPrefix.series.data.tree
        oldi.succ.castSucc),
  let oldChoiceOnNew :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
      (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
      (originalPrefix.series.data.coloring oldi.castSucc) :=
    (Eq.symm hbaseTree ▸ oldChoice);
  ∀ (_ : oldChoiceOnNew.vertex = oldChoice.vertex)
    (_ : newChoicePE.vertex = oldChoiceOnNew.vertex)
    (_ :
      MissingColors G (originalPrefix.series.data.coloring oldi.succ) oldChoice.vertex =
        MissingColors G (corr.replacementSeries.data.coloring oldi.succ) oldChoice.vertex),
  MissingColors G (originalPrefix.series.data.coloring oldi.succ) oldChoiceOnNew.vertex =
    MissingColors G (corr.replacementSeries.data.coloring oldi.succ) newChoicePE.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge sigmaPrev originalPrefix corr oldi
      oldChoice newChoicePE hbaseTree oldChoiceOnNew holdVertexCast hvertexIdentity
      hmissingSameVertex
  calc
    MissingColors G
        (originalPrefix.series.data.coloring oldi.succ)
        oldChoiceOnNew.vertex =
      MissingColors G
        (originalPrefix.series.data.coloring oldi.succ)
        oldChoice.vertex := congrArg _ holdVertexCast
    _ = MissingColors G
        (corr.replacementSeries.data.coloring oldi.succ)
        oldChoice.vertex := hmissingSameVertex
    _ = MissingColors G
        (corr.replacementSeries.data.coloring oldi.succ)
        newChoicePE.vertex := by
          exact congrArg _
            (hvertexIdentity.trans holdVertexCast).symm

private theorem helper_colorControlAtQ_5343.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
      TreeSequence G e0)
  (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hroundLarge : (1 : ℕ) < ett.rounds),
  let q : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ), by
        omega⟩ :
      Fin ett.rounds);
  ∀ (sigmaPrev : PartialEdgeColoring E k)
    (originalPrefix :
      ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring
          (⟨ett.rounds - (1 : ℕ), by
                omega⟩ :
              Fin ett.rounds).castSucc))
    (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ))
    (corr :
      CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
  let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last
      originalPrefix.rounds;
  ∀ (_ : (0 : ℕ) < originalPrefix.rounds)
    (_ :
      Fin.castLE
          (by
            omega)
          replacementLast =
        (⟨ett.rounds - (1 : ℕ), by
              omega⟩ :
            Fin ett.rounds).castSucc)
    (available : RevisitingExtensionCertificate corr.replacementSeries.data replacementLast),
  let earlierPrefix : Fin (originalPrefix.rounds + (1 : ℕ)) := available.earlier;
  ∀ (oldi : Fin originalPrefix.rounds)
    (oldChoice :
      MaximumDefectiveChoice G e0 (originalPrefix.series.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
        (originalPrefix.series.data.coloring oldi.castSucc))
    (oldGamma newGamma : Fin k)
    (newChoicePE :
      MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data oldi.castSucc)
        (corr.replacementSeries.data.coloring oldi.castSucc))
    (hbaseTree :
      corr.replacementSeries.data.tree oldi.succ.castSucc =
          originalPrefix.series.data.tree oldi.succ.castSucc),
  let oldChoiceOnNew :
    MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree oldi.succ.castSucc)
      (TashkinovStoredColors originalPrefix.series.data oldi.castSucc)
      (originalPrefix.series.data.coloring oldi.castSucc) :=
    (Eq.symm hbaseTree ▸ oldChoice);
  ∀ (holdColorCast : oldChoiceOnNew.color = oldChoice.color) (holdColorNe : oldGamma ≠
      oldChoice.color)
    (hnewColorNe : newGamma ≠ newChoicePE.color) (hidentifiedDelta : newChoicePE.color
        = oldChoiceOnNew.color)
    (hidentifiedGamma : newGamma = oldGamma) (hnewDeltaAvailable : newChoicePE.color =
        available.delta)
    (hnewGammaAvailable : newGamma = available.gamma) (hgammaDeltaNe : available.gamma
        ≠ available.delta)
    (_ :
  ∀ (c : Fin k)
    (_ :
      c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc)
          (ett.series.data.tree q.castSucc.castSucc)),
  c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc)
      (ett.series.data.tree q.succ.castSucc))
    (c : Fin k)
    (_ :
      c ∈
        ett.series.data.stored
          (Fin.castLE
            (by
              omega)
            earlierPrefix)),
  c ∈
    TreeMissingColors (ett.series.data.coloring q.castSucc) (ett.series.data.tree
        q.succ.castSucc) ∪
      TashkinovStoredColors ett.series.data q.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge q sigmaPrev originalPrefix hr corr
      replacementLast horiginalPositive hlastMap available earlierPrefix oldi oldChoice oldGamma
      newGamma newChoicePE hbaseTree oldChoiceOnNew holdColorCast holdColorNe hnewColorNe
      hidentifiedDelta hidentifiedGamma hnewDeltaAvailable hnewGammaAvailable hgammaDeltaNe
      missingPreviousToTn c hc
  by_cases hm : c ∈ TreeMissingColors
      (ett.series.data.coloring q.castSucc)
      (ett.series.data.tree q.castSucc.castSucc)
  · exact Finset.mem_union_left _
      (missingPreviousToTn c hm)
  · apply Finset.mem_union_right
    unfold TashkinovStoredColors
    have hqne : q.castSucc.val ≠ 0 := by
      change ett.rounds - 1 ≠ 0
      omega
    rw [ite_eq_right hqne, Finset.mem_sdiff]
    refine ⟨?_, hm⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ,
      true_and]
    refine ⟨Fin.castLE (by omega) earlierPrefix, ?_⟩
    rw [ite_eq_left]
    · exact hc
    · have hle := available.earlierAtMost
      have hlastVal : replacementLast.val = q.castSucc.val := by
        exact congrArg Fin.val hlastMap
      simpa [earlierPrefix] using hle.trans_eq hlastVal

private theorem positivePrefixReturnTransport.{u_1, u_2} :
    positivePrefixReturnTransportStatement.{u_1, u_2} := by
  classical
  intro «V» «E» «inst» «inst_1» «inst_3» «G» «k» «e0» «input» «T» «generating» «ett» «hroundLarge»
      «hlower» «q» «sigmaPrev» «hsigmaPrevProper» «hsigmaPrevOne» «previousProper»
      «previousOneUncolored» «hsigmaPrevStableQ» «originalPrefix» «hr» «hprefixMP» «hprefixTrees»
      «hprefixData» «corr» «hcorrMP» «noRevisiting» «hqSucc» «replacementLast» «hcorrFinalColor»
      «horiginalPositive» «hlastMap» «hreplacementCurrentTree» «horiginalCurrentTree» «peRootOnly»
      «available» «earlierPrefix» «hearlierPositive» «hbaseEarlierKind» «oldi» «oldChoice»
      «oldGamma» «oldGammaRule» «oldSecond» «oldSecondProper» «oldSecondStable» «oldCurrentColoring»
      «oldCurrentProper» «oldCurrentOne» «oldCurrentStored» «oldCurrentEdges» «oldCurrentKind»
      «oldCurrentVertex» «oldCurrentDelta» «oldCurrentGamma» «hbaseTarget» «holdIndex» «newGamma»
      «newSecond» «newSecondProper» «newPreviousProper» «newPreviousOne» «newPreviousClosed»
      «newPreviousNotStrong» «newNoRE» «newChoicePE» «newAlternativeFails» «newGammaRule»
      «newSecondStable» «newExit» «newCurrentColoring» «newCurrentProper» «newCurrentOne»
      «newCurrentStored» «newCurrentEdges» «newCurrentKind» «newCurrentVertex» «newCurrentOutside»
      «newCurrentDelta» «newCurrentGamma» «newClosedExtension» «newOrderedExtension»
      «newStrictExtension» «hnewTarget» «hnewIndex» «hbaseTree» «oldChoiceOnNew»
      «transportChoiceFields» «htransport» «holdEdgeCast» «holdVertexCast» «holdOtherCast»
      «holdColorCast» «hedgePairs» «hcolorPairs» «hedgeIdentity» «hends» «hvertexIdentity»
      «hotherIdentity» «pePostStatus» «holdDeltaMissing» «holdGammaNotMissing» «holdColorNe»
      «hnewDeltaMissing» «hnewGammaNotMissing» «hnewColorNe» «hmissingSameVertex»
      «hmissingForIdentification» «holdDeltaForIdentification» «holdGammaForIdentification»
      «hidentifiedEdge» «hidentifiedVertex» «hidentifiedOther» «hidentifiedDelta» «hidentifiedGamma»
      «hnewDeltaAvailable» «hnewGammaAvailable» «holdDeltaAvailable» «holdGammaAvailable»
      «hnewVertexOld» «hnewOtherOld» «reStepColoring» «reIntervalColoring»
      «hreplacementColorConstant» «hbaseColorConstant» «hnewPostSigmaPrev» «hbaseFinalColor»
      «holdPostOriginal» «hnewDeltaSigmaPrev» «hnewGammaSigmaPrevNot» «holdDeltaOriginal»
      «holdGammaOriginalNot» «hgammaDeltaNe» «stepSegment» «segmentTrans» «treeToFinal»
  have holdTreeFinal : TreeSequenceInitialSegment
      (originalPrefix.series.data.tree oldi.succ.castSucc)
      (originalPrefix.series.data.tree
        (Fin.last (originalPrefix.rounds + 1))) := by
    apply treeToFinal (originalPrefix.rounds - oldi.val)
    · simp
      omega
    · simp
  have holdVertexFinal : oldChoice.vertex ∈
      TreeSequenceVertexSet
        (originalPrefix.series.data.tree
          (Fin.last (originalPrefix.rounds + 1))) :=
    TreeSequenceInitialSegmentVertexSetSubset holdTreeFinal
      oldChoice.vertexDefective.1
  have hreturnInOldEarlier :=
    helper_hreturnInOldEarlier_2009 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@available) (@oldi) (@holdIndex)
        (@hnewIndex) (@hbaseTree)
  have hreturnInFinal : available.returnVertex ∈
      TreeSequenceVertexSet
        (originalPrefix.series.data.tree
          (Fin.last (originalPrefix.rounds + 1))) :=
    TreeSequenceInitialSegmentVertexSetSubset holdTreeFinal
      (by simpa only [holdIndex] using hreturnInOldEarlier)
  have hpreviousToTn : TreeSequenceInitialSegment
      (ett.series.data.tree q.castSucc.castSucc)
      (ett.series.data.tree q.succ.castSucc) := by
    rw [← horiginalCurrentTree, hqSucc]
    exact originalPrefix.abovePenultimate
  have missingPreviousToTn (c : Fin k)
      (hc : c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc)
        (ett.series.data.tree q.castSucc.castSucc)) :=
    helper_missingPreviousToTn_2668 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@hpreviousToTn) (@c) (@hc)
  have hgammaEarlierStored : available.gamma ∈
      originalPrefix.series.data.stored earlierPrefix := by
    rw [← holdIndex, oldCurrentStored,
      ← holdGammaAvailable]
    simp
  have hdeltaEarlierStored : available.delta ∈
      originalPrefix.series.data.stored earlierPrefix := by
    rw [← holdIndex, oldCurrentStored,
      ← holdDeltaAvailable]
    simp
  have hgammaEarlierStoredFull : available.gamma ∈
      ett.series.data.stored
        (Fin.castLE (by omega) earlierPrefix) := by
    rw [← (hprefixData earlierPrefix).2.1]
    exact hgammaEarlierStored
  have hdeltaEarlierStoredFull : available.delta ∈
      ett.series.data.stored
        (Fin.castLE (by omega) earlierPrefix) := by
    rw [← (hprefixData earlierPrefix).2.1]
    exact hdeltaEarlierStored
  have colorControlAtQ (c : Fin k)
      (hc : c ∈ ett.series.data.stored
        (Fin.castLE (by omega) earlierPrefix)) :=
    helper_colorControlAtQ_5343 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge)
        (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@horiginalPositive) (@hlastMap)
        (@available) (@oldi) (@oldChoice) (@oldGamma) (@newGamma) (@newChoicePE) (@hbaseTree)
        (@holdColorCast) (@holdColorNe) (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma)
        (@hnewDeltaAvailable) (@hnewGammaAvailable) (@hgammaDeltaNe) (@missingPreviousToTn) (@c)
        (@hc)
  have hreturnNotNil : ¬ available.returnPath.Nil := by
    intro hnil
    have hend := SimpleGraph.Walk.Nil.eq hnil
    simp at hend
  have replacementReturnEdgeData (f : E)
      (hf : Sum.inr f ∈ available.returnPath.support) :=
    helper_replacementReturnEdgeData_1963 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@hcorrFinalColor)
        (@hreplacementCurrentTree) (@available) (@hreturnNotNil) (@f) (@hf)
  have copyReturnEdge (f : E)
      (hf : Sum.inr f ∈ available.returnPath.support) :
      sigmaPrev f = ett.series.data.coloring q.castSucc f := by
    obtain ⟨hfIncident, hcolor⟩ :=
      replacementReturnEdgeData f hf
    have hcriterion := (sc1 G e0
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.castSucc)
      (ett.series.data.coloring q.castSucc) sigmaPrev
      previousProper previousOneUncolored hsigmaPrevProper
      hsigmaPrevOne).mp hsigmaPrevStableQ
    apply hcriterion f hfIncident
    rcases hcolor with hgamma | hdelta
    · exact Or.inr ⟨available.gamma,
        colorControlAtQ available.gamma
          hgammaEarlierStoredFull, hgamma⟩
    · exact Or.inr ⟨available.delta,
        colorControlAtQ available.delta
          hdeltaEarlierStoredFull, hdelta⟩
  exact helper_continuation_4611 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@hroundLarge) (@hlower) (@sigmaPrev) (@hsigmaPrevProper) (@previousProper)
      (@previousOneUncolored) (@originalPrefix) (@hr) (@hprefixMP) (@hprefixTrees) (@hprefixData)
      (@corr) (@hcorrMP) (@noRevisiting) (@hcorrFinalColor) (@horiginalPositive) (@hlastMap)
      (@hreplacementCurrentTree) (@peRootOnly) (@available) (@hbaseEarlierKind) (@oldi)
      (@oldChoice) (@oldGamma) (@oldCurrentProper) (@oldCurrentOne) (@oldCurrentStored)
      (@oldCurrentEdges) (@oldCurrentKind) (@oldCurrentVertex) (@oldCurrentDelta)
      (@oldCurrentGamma) (@hbaseTarget) (@holdIndex) (@newGamma) (@newChoicePE)
      (@newCurrentProper) (@newCurrentOne) (@newCurrentKind) (@newCurrentVertex)
      (@newCurrentDelta) (@newCurrentGamma) (@hbaseTree) (@transportChoiceFields)
      (@holdColorCast) (@pePostStatus) (@holdDeltaMissing) (@holdGammaNotMissing) (@holdColorNe)
      (@hnewColorNe) (@hidentifiedDelta) (@hidentifiedGamma) (@hnewDeltaAvailable)
      (@hnewGammaAvailable) (@holdDeltaAvailable) (@holdGammaAvailable) (@hnewVertexOld)
      (@hnewPostSigmaPrev) (@hbaseFinalColor) (@holdPostOriginal) (@hnewDeltaSigmaPrev)
      (@holdDeltaOriginal) (@holdGammaOriginalNot) (@hgammaDeltaNe) (@holdVertexFinal)
      (@hreturnInOldEarlier) (@hreturnInFinal) (@replacementReturnEdgeData) (@copyReturnEdge)

private theorem positivePrefixColorIdentification.{u_1, u_2} :
    positivePrefixColorIdentificationStatement.{u_1, u_2} := by
  classical
  intro «V» «E» «inst» «inst_1» «inst_3» «G» «k» «e0» «input» «T» «generating» «ett» «hroundLarge»
      «hlower» «q» «sigmaPrev» «hsigmaPrevProper» «hsigmaPrevOne» «previousProper»
      «previousOneUncolored» «hsigmaPrevStableQ» «originalPrefix» «hr» «hprefixMP» «hprefixTrees»
      «hprefixData» «corr» «hcorrMP» «noRevisiting» «hqSucc» «replacementLast» «hcorrFinalColor»
      «horiginalPositive» «hlastMap» «hreplacementCurrentTree» «horiginalCurrentTree» «peRootOnly»
      «available» «earlierPrefix» «hearlierPositive» «hbaseEarlierKind» «oldi» «oldChoice»
      «oldGamma» «oldGammaRule» «oldSecond» «oldSecondProper» «oldSecondStable» «oldCurrentColoring»
      «oldCurrentProper» «oldCurrentOne» «oldCurrentStored» «oldCurrentEdges» «oldCurrentKind»
      «oldCurrentVertex» «oldCurrentDelta» «oldCurrentGamma» «hbaseTarget» «holdIndex» «newGamma»
      «newSecond» «newSecondProper» «newPreviousProper» «newPreviousOne» «newPreviousClosed»
      «newPreviousNotStrong» «newNoRE» «newChoicePE» «newAlternativeFails» «newGammaRule»
      «newSecondStable» «newExit» «newCurrentColoring» «newCurrentProper» «newCurrentOne»
      «newCurrentStored» «newCurrentEdges» «newCurrentKind» «newCurrentVertex» «newCurrentOutside»
      «newCurrentDelta» «newCurrentGamma» «newClosedExtension» «newOrderedExtension»
      «newStrictExtension» «hnewTarget» «hnewIndex» «hbaseTree» «oldChoiceOnNew»
      «transportChoiceFields» «htransport» «holdEdgeCast» «holdVertexCast» «holdOtherCast»
      «holdColorCast» «hedgePairs» «hcolorPairs» «hedgeIdentity» «hends» «hvertexIdentity»
      «hotherIdentity» «pePostStatus» «holdDeltaMissing» «holdGammaNotMissing» «holdColorNe»
      «hnewDeltaMissing» «hnewGammaNotMissing» «hnewColorNe»
  have hmissingSameVertex : MissingColors G
      (originalPrefix.series.data.coloring oldi.succ)
        oldChoice.vertex =
    MissingColors G
      (corr.replacementSeries.data.coloring oldi.succ)
        oldChoice.vertex := by
    have hs := (corr.replacementStable oldi).2
      oldChoice.vertex (by
        exact oldChoice.vertexDefective.1)
    exact hs.symm
  have hmissingForIdentification :=
    helper_hmissingForIdentification_5050 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@oldi) (@oldChoice) (@newChoicePE)
        (@hbaseTree) (@holdVertexCast) (@hvertexIdentity) (@hmissingSameVertex)
  have holdDeltaForIdentification : oldChoiceOnNew.color ∈
      MissingColors G
        (originalPrefix.series.data.coloring oldi.succ)
        oldChoiceOnNew.vertex := by
    simpa only [holdColorCast, holdVertexCast] using
      holdDeltaMissing
  have holdGammaForIdentification : oldGamma ∉
      MissingColors G
        (originalPrefix.series.data.coloring oldi.succ)
        oldChoiceOnNew.vertex := by
    simpa only [holdVertexCast] using holdGammaNotMissing
  have hidentified := TdEarlierPEWitnessIdentification G k e0
    (corr.replacementSeries.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors originalPrefix.series.data
      oldi.castSucc)
    (TashkinovStoredColors corr.replacementSeries.data
      oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)
    (corr.replacementSeries.data.coloring oldi.castSucc)
    oldChoiceOnNew newChoicePE oldGamma newGamma
    (originalPrefix.series.data.coloring oldi.succ)
    (corr.replacementSeries.data.coloring oldi.succ)
    hedgePairs hcolorPairs hmissingForIdentification
    holdDeltaForIdentification holdGammaForIdentification
    hnewDeltaMissing hnewGammaNotMissing
  rcases hidentified with ⟨hidentifiedEdge,
    hidentifiedVertex, hidentifiedOther, hidentifiedDelta,
    hidentifiedGamma⟩
  have hnewDeltaAvailable : newChoicePE.color =
      available.delta := by
    exact Option.some.inj (newCurrentDelta.symm.trans
      ((congrArg corr.replacementSeries.data.delta
        hnewIndex).trans available.earlierDelta))
  have hnewGammaAvailable : newGamma = available.gamma := by
    exact Option.some.inj (newCurrentGamma.symm.trans
      ((congrArg corr.replacementSeries.data.gamma
        hnewIndex).trans available.earlierGamma))
  have holdDeltaAvailable : oldChoice.color =
      available.delta := by
    exact holdColorCast.symm.trans
      (hidentifiedDelta.symm.trans hnewDeltaAvailable)
  have holdGammaAvailable : oldGamma = available.gamma := by
    exact hidentifiedGamma.symm.trans hnewGammaAvailable
  have hnewVertexOld : newChoicePE.vertex = oldChoice.vertex :=
    hidentifiedVertex.trans holdVertexCast
  have hnewOtherOld : newChoicePE.otherEndpoint =
      oldChoice.otherEndpoint :=
    hidentifiedOther.trans holdOtherCast
  have reStepColoring :=
    @helper_reStepColoring_872 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge) (@sigmaPrev)
        (@originalPrefix) (@hr) (@corr) (@available) (@oldi) (@oldChoice) (@oldGamma) (@newGamma)
        (@newChoicePE) (@hbaseTree)
  have reIntervalColoring :=
    @helper_reIntervalColoring_913 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge) (@sigmaPrev)
        (@originalPrefix) (@hr) (@corr) (@available) (@oldi) (@oldChoice) (@oldGamma) (@newGamma)
        (@newChoicePE) (@hbaseTree) (@reStepColoring)
  have hreplacementColorConstant :=
    helper_hreplacementColorConstant_2536 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@available)
        (@hearlierPositive) (@oldi) (@oldChoice) (@oldGamma) (@hbaseTarget) (@newGamma)
        (@newChoicePE) (@hnewIndex) (@hbaseTree) (@reIntervalColoring)
  have hbaseColorConstant :=
    helper_hbaseColorConstant_2550 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@available)
        (@hearlierPositive) (@oldi) (@oldChoice) (@oldGamma) (@hbaseTarget) (@holdIndex)
        (@newGamma) (@newChoicePE) (@hbaseTree) (@reIntervalColoring)
  have hnewPostSigmaPrev :
      corr.replacementSeries.data.coloring oldi.succ =
        sigmaPrev :=
    hreplacementColorConstant.symm.trans
      (by simpa [replacementLast] using hcorrFinalColor)
  have hbaseFinalColor :
      originalPrefix.series.data.coloring replacementLast =
        ett.series.data.coloring q.castSucc := by
    calc
      originalPrefix.series.data.coloring replacementLast =
          ett.series.data.coloring
            (Fin.castLE (by omega) replacementLast) :=
        (hprefixData replacementLast).1
      _ = ett.series.data.coloring q.castSucc := by
        rw [hlastMap]
  have holdPostOriginal :
      originalPrefix.series.data.coloring oldi.succ =
        ett.series.data.coloring q.castSucc :=
    hbaseColorConstant.symm.trans hbaseFinalColor
  have hnewDeltaSigmaPrev :=
    helper_hnewDeltaSigmaPrev_2577 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@available) (@oldi) (@newChoicePE)
        (@hnewDeltaMissing) (@hnewDeltaAvailable) (@hnewPostSigmaPrev)
  have hnewGammaSigmaPrevNot :=
    helper_hnewGammaSigmaPrevNot_2584 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@available) (@oldi) (@newGamma)
        (@newChoicePE) (@hnewGammaNotMissing) (@hnewGammaAvailable) (@hnewPostSigmaPrev)
  have holdDeltaOriginal :=
    helper_holdDeltaOriginal_2591 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@available) (@oldi) (@oldChoice)
        (@holdDeltaMissing) (@holdDeltaAvailable) (@holdPostOriginal)
  have holdGammaOriginalNot :=
    helper_holdGammaOriginalNot_2599 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
        (@hroundLarge) (@sigmaPrev) (@originalPrefix) (@corr) (@available) (@oldi) (@oldChoice)
        (@oldGamma) (@holdGammaNotMissing) (@holdGammaAvailable) (@holdPostOriginal)
  have hgammaDeltaNe : available.gamma ≠ available.delta := by
    intro heq
    apply hnewColorNe
    rw [hnewGammaAvailable, hnewDeltaAvailable, heq]
  have stepSegment :=
    helper_stepSegment_1041 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge)
        (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@available) (@oldi) (@oldChoice)
        (@oldGamma) (@newGamma) (@newChoicePE) (@hbaseTree)
  have segmentTrans :=
    @helper_segmentTrans_1816 (@V) (@E) (@G) (@e0)
  have treeToFinal :=
    helper_treeToFinal_1111 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge)
        (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@available) (@oldi) (@oldChoice)
        (@oldGamma) (@newGamma) (@newChoicePE) (@hbaseTree) (@stepSegment) (@segmentTrans)
  exact @positivePrefixReturnTransport (@«V») (@«E») inferInstance inferInstance inferInstance
      (@«G») (@«k») (@«e0») (@«input») (@«T») (@«generating») (@«ett») (@«hroundLarge») (@«hlower»)
      (@«sigmaPrev») (@«hsigmaPrevProper») (@«hsigmaPrevOne») (@«previousProper»)
      (@«previousOneUncolored») (@«hsigmaPrevStableQ») (@«originalPrefix») (@«hr») (@«hprefixMP»)
      (@«hprefixTrees») (@«hprefixData») (@«corr») (@«hcorrMP») (@«noRevisiting») (@«hqSucc»)
      (@«hcorrFinalColor») (@«horiginalPositive») (@«hlastMap») (@«hreplacementCurrentTree»)
      (@«horiginalCurrentTree») (@«peRootOnly») (@«available») (@«hearlierPositive»)
      (@«hbaseEarlierKind») (@«oldi») (@«oldChoice») (@«oldGamma») (@«oldGammaRule») (@«oldSecond»)
      (@«oldSecondProper») (@«oldSecondStable») (@«oldCurrentColoring») (@«oldCurrentProper»)
      (@«oldCurrentOne») (@«oldCurrentStored») (@«oldCurrentEdges») (@«oldCurrentKind»)
      (@«oldCurrentVertex») (@«oldCurrentDelta») (@«oldCurrentGamma») (@«hbaseTarget»)
      (@«holdIndex») (@«newGamma») (@«newSecond») (@«newSecondProper») (@«newPreviousProper»)
      (@«newPreviousOne») (@«newPreviousClosed») (@«newPreviousNotStrong») (@«newNoRE»)
      (@«newChoicePE») (@«newAlternativeFails») (@«newGammaRule») (@«newSecondStable») (@«newExit»)
      (@«newCurrentColoring») (@«newCurrentProper») (@«newCurrentOne») (@«newCurrentStored»)
      (@«newCurrentEdges») (@«newCurrentKind») (@«newCurrentVertex») (@«newCurrentOutside»)
      (@«newCurrentDelta») (@«newCurrentGamma») (@«newClosedExtension») (@«newOrderedExtension»)
      (@«newStrictExtension») (@«hnewTarget») (@«hnewIndex») (@«hbaseTree»)
      (@«transportChoiceFields») (@«htransport») (@«holdEdgeCast») (@«holdVertexCast»)
      (@«holdOtherCast») (@«holdColorCast») (@«hedgePairs») (@«hcolorPairs») (@«hedgeIdentity»)
      (@«hends») (@«hvertexIdentity») (@«hotherIdentity») (@«pePostStatus») (@«holdDeltaMissing»)
      (@«holdGammaNotMissing») (@«holdColorNe») (@«hnewDeltaMissing») (@«hnewGammaNotMissing»)
      (@«hnewColorNe») (@«hmissingSameVertex») (@«hmissingForIdentification»)
      (@«holdDeltaForIdentification») (@«holdGammaForIdentification») (@«hidentifiedEdge»)
      (@«hidentifiedVertex») (@«hidentifiedOther») (@«hidentifiedDelta») (@«hidentifiedGamma»)
      (@«hnewDeltaAvailable») (@«hnewGammaAvailable») (@«holdDeltaAvailable»)
      (@«holdGammaAvailable») (@«hnewVertexOld») (@«hnewOtherOld») (@«reStepColoring»)
      (@«reIntervalColoring») (@«hreplacementColorConstant») (@«hbaseColorConstant»)
      (@«hnewPostSigmaPrev») (@«hbaseFinalColor») (@«holdPostOriginal») (@«hnewDeltaSigmaPrev»)
      (@«hnewGammaSigmaPrevNot») (@«holdDeltaOriginal») (@«holdGammaOriginalNot») (@«hgammaDeltaNe»)
      (@«stepSegment») (@«segmentTrans») (@«treeToFinal»)

private theorem helper_branch_377.{u_1, u_2} : positivePrefixContradictionStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge hlower
  set q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ :
            Fin ett.rounds)
  intro sigmaPrev hsigmaPrevProper hsigmaPrevOne previousProper previousOneUncolored
      hsigmaPrevStableQ originalPrefix hr hprefixMP hprefixTrees hprefixData corr hcorrFinalColor
      hcorrMP noRevisiting hqSucc
  set replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds
  intro horiginalPositive hlastMap hreplacementCurrentTree horiginalCurrentTree peRootOnly available
  set earlierPrefix : Fin (originalPrefix.rounds
                                                      + (1 : ℕ)) := available.earlier
  intro hearlierPositive hbaseEarlierKind oldi oldChoice oldGamma oldGammaRule oldSecond
      oldSecondProper oldSecondStable oldCurrentColoring oldCurrentProper oldCurrentOne
      oldCurrentStored oldCurrentEdges oldCurrentKind oldCurrentVertex oldCurrentDelta
      oldCurrentGamma hbaseTarget holdIndex newi newPreviousProper newPreviousOne
      newPreviousClosed newPreviousNotStrong newNoRE newChoicePE newAlternativeFails newGamma
      newGammaRule newSecond newSecondProper newSecondStable newExit newCurrentColoring
      newCurrentProper newCurrentOne newCurrentStored newCurrentEdges newCurrentKind
      newCurrentVertex newCurrentOutside newCurrentDelta newCurrentGamma newClosedExtension
      newOrderedExtension newStrictExtension hnewTarget
  have hnewIndex : newi.succ = earlierPrefix := by
    simpa using hnewTarget.symm
  have hindices :=
    helper_hindices_2256 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hroundLarge)
        (@sigmaPrev) (@originalPrefix) (@hr) (@corr) (@available) (@oldi) (@hbaseTarget)
        (@holdIndex) (@newi) (@hnewTarget) (@hnewIndex)
  subst newi
  have hbaseTree :
      corr.replacementSeries.data.tree oldi.succ.castSucc =
        originalPrefix.series.data.tree oldi.succ.castSucc :=
    corr.ladderTreesAgree oldi
  let oldChoiceOnNew : MaximumDefectiveChoice G e0
      (corr.replacementSeries.data.tree oldi.succ.castSucc)
      (TashkinovStoredColors originalPrefix.series.data
        oldi.castSucc)
      (originalPrefix.series.data.coloring oldi.castSucc) :=
    hbaseTree.symm ▸ oldChoice
  have transportChoiceFields : ∀
      {A B : TreeSequence G e0} (hAB : A = B)
      (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
      (ch : MaximumDefectiveChoice G e0 A C phi),
      (hAB ▸ ch).edge = ch.edge ∧
        (hAB ▸ ch).vertex = ch.vertex ∧
        (hAB ▸ ch).otherEndpoint = ch.otherEndpoint ∧
        (hAB ▸ ch).color = ch.color := by
    intro A B hAB C phi ch
    subst B
    exact ⟨rfl, rfl, rfl, rfl⟩
  have htransport := transportChoiceFields hbaseTree.symm
    (TashkinovStoredColors originalPrefix.series.data
      oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)
    oldChoice
  have holdEdgeCast : oldChoiceOnNew.edge = oldChoice.edge :=
    htransport.1
  have holdVertexCast : oldChoiceOnNew.vertex =
      oldChoice.vertex := htransport.2.1
  have holdOtherCast : oldChoiceOnNew.otherEndpoint =
      oldChoice.otherEndpoint := htransport.2.2.1
  have holdColorCast : oldChoiceOnNew.color =
      oldChoice.color := htransport.2.2.2
  have hedgePairs : ({oldChoiceOnNew.edge} : Finset E) =
      {newChoicePE.edge} := by
    have holdEdges : originalPrefix.series.data.connectingEdges
        earlierPrefix = {oldChoice.edge} := by
      simpa only [holdIndex] using oldCurrentEdges
    have hnewEdges :
        corr.replacementSeries.data.connectingEdges
          earlierPrefix = {newChoicePE.edge} := by
      simpa only [hnewIndex] using newCurrentEdges
    simpa only [holdEdgeCast] using
      holdEdges.symm.trans
        ((corr.connectingEdgesAgree earlierPrefix).symm.trans
          hnewEdges)
  have hcolorPairs :
      ({oldChoiceOnNew.color, oldGamma} : Finset (Fin k)) =
        {newChoicePE.color, newGamma} := by
    have holdStored : originalPrefix.series.data.stored
        earlierPrefix = {oldChoice.color, oldGamma} := by
      simpa only [holdIndex] using oldCurrentStored
    have hnewStored : corr.replacementSeries.data.stored
        earlierPrefix = {newChoicePE.color, newGamma} := by
      simpa only [hnewIndex] using newCurrentStored
    simpa only [holdColorCast] using
      holdStored.symm.trans
        ((corr.storedColorsAgree earlierPrefix).symm.trans
          hnewStored)
  have hedgeIdentity : newChoicePE.edge =
      oldChoiceOnNew.edge := by
    apply Finset.mem_singleton.mp
    rw [hedgePairs]
    exact Finset.mem_singleton_self _
  have hends : s(oldChoiceOnNew.vertex,
        oldChoiceOnNew.otherEndpoint) =
      s(newChoicePE.vertex, newChoicePE.otherEndpoint) := by
    calc
      s(oldChoiceOnNew.vertex,
          oldChoiceOnNew.otherEndpoint) =
          G.ends oldChoiceOnNew.edge :=
        oldChoiceOnNew.edgeEnds.symm
      _ = G.ends newChoicePE.edge :=
        congrArg G.ends hedgeIdentity.symm
      _ = s(newChoicePE.vertex,
          newChoicePE.otherEndpoint) := newChoicePE.edgeEnds
  have hvertexIdentity : newChoicePE.vertex =
      oldChoiceOnNew.vertex := by
    rcases Sym2.eq_iff.mp hends with hstraight | hcross
    · exact hstraight.1.symm
    · exfalso
      exact newChoicePE.otherOutside
        (hcross.1 ▸ oldChoiceOnNew.vertexDefective.1)
  have hotherIdentity : newChoicePE.otherEndpoint =
      oldChoiceOnNew.otherEndpoint := by
    rcases Sym2.eq_iff.mp hends with hstraight | hcross
    · exact hstraight.2.symm
    · exfalso
      exact oldChoiceOnNew.otherOutside
        (hcross.2 ▸ newChoicePE.vertexDefective.1)
  have pePostStatus :=
    helper_pePostStatus_3432 (@G) (@k) (@e0)
  obtain ⟨holdDeltaMissing, holdGammaNotMissing,
      holdColorNe⟩ := pePostStatus
    (originalPrefix.series.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors originalPrefix.series.data
      oldi.castSucc)
    (originalPrefix.series.data.coloring oldi.castSucc)
    oldChoice oldGamma oldSecond oldSecondProper
    oldSecondStable oldGammaRule.1
  obtain ⟨hnewDeltaMissing, hnewGammaNotMissing,
      hnewColorNe⟩ := pePostStatus
    (corr.replacementSeries.data.tree oldi.succ.castSucc)
    (TashkinovStoredColors corr.replacementSeries.data
      oldi.castSucc)
    (corr.replacementSeries.data.coloring oldi.castSucc)
    newChoicePE newGamma newSecond newSecondProper
    newSecondStable newGammaRule.1
  rw [← oldCurrentColoring] at holdDeltaMissing holdGammaNotMissing
  rw [← newCurrentColoring] at hnewDeltaMissing hnewGammaNotMissing
  exact @positivePrefixColorIdentification (@«V») (@«E») inferInstance inferInstance inferInstance
      (@«G») (@«k») (@«e0») (@«input») (@«T») (@«generating») (@«ett») (@«hroundLarge») (@«hlower»)
      (@«sigmaPrev») (@«hsigmaPrevProper») (@«hsigmaPrevOne») (@«previousProper»)
      (@«previousOneUncolored») (@«hsigmaPrevStableQ») (@«originalPrefix») (@«hr») (@«hprefixMP»)
      (@«hprefixTrees») (@«hprefixData») (@«corr») (@«hcorrMP») (@«noRevisiting») (@«hqSucc»)
      (@«hcorrFinalColor») (@«horiginalPositive») (@«hlastMap») (@«hreplacementCurrentTree»)
      (@«horiginalCurrentTree») (@«peRootOnly») (@«available») (@«hearlierPositive»)
      (@«hbaseEarlierKind») (@«oldi») (@«oldChoice») (@«oldGamma») (@«oldGammaRule») (@«oldSecond»)
      (@«oldSecondProper») (@«oldSecondStable») (@«oldCurrentColoring») (@«oldCurrentProper»)
      (@«oldCurrentOne») (@«oldCurrentStored») (@«oldCurrentEdges») (@«oldCurrentKind»)
      (@«oldCurrentVertex») (@«oldCurrentDelta») (@«oldCurrentGamma») (@«hbaseTarget»)
      (@«holdIndex») (@«newGamma») (@«newSecond») (@«newSecondProper») (@«newPreviousProper»)
      (@«newPreviousOne») (@«newPreviousClosed») (@«newPreviousNotStrong») (@«newNoRE»)
      (@«newChoicePE») (@«newAlternativeFails») (@«newGammaRule») (@«newSecondStable») (@«newExit»)
      (@«newCurrentColoring») (@«newCurrentProper») (@«newCurrentOne») (@«newCurrentStored»)
      (@«newCurrentEdges») (@«newCurrentKind») (@«newCurrentVertex») (@«newCurrentOutside»)
      (@«newCurrentDelta») (@«newCurrentGamma») (@«newClosedExtension») (@«newOrderedExtension»)
      (@«newStrictExtension») (@«hnewTarget») (@«hnewIndex») (@«hbaseTree»)
      (@«transportChoiceFields») (@«htransport») (@«holdEdgeCast») (@«holdVertexCast»)
      (@«holdOtherCast») (@«holdColorCast») (@«hedgePairs») (@«hcolorPairs») (@«hedgeIdentity»)
      (@«hends») (@«hvertexIdentity») (@«hotherIdentity») (@«pePostStatus») (@«holdDeltaMissing»)
      (@«holdGammaNotMissing») (@«holdColorNe») (@«hnewDeltaMissing») (@«hnewGammaNotMissing»)
      (@«hnewColorNe»)

private theorem helper_branch_280.{u_1, u_2} :
    helperBranch280Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hroundLarge hlower
  set q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ :
            Fin ett.rounds)
  intro sigmaPrev hsigmaPrevProper hsigmaPrevOne previousProper previousOneUncolored
      hsigmaPrevStableQ originalPrefix hr hprefixMP hprefixTrees hprefixData corr hcorrFinalColor
      hcorrMP noRevisiting hqSucc
  set replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds
  intro horiginalPositive hlastMap hreplacementCurrentTree horiginalCurrentTree peRootOnly available
  set earlierPrefix : Fin (originalPrefix.rounds
                                                      + (1 : ℕ)) := available.earlier
  intro hearlierPositive hbaseEarlierKind oldi oldChoice oldGamma oldGammaRule oldSecond
      oldSecondProper oldSecondStable oldCurrentColoring oldCurrentProper oldCurrentOne
      oldCurrentStored oldCurrentEdges oldCurrentKind oldCurrentVertex oldCurrentDelta
      oldCurrentGamma hbaseTarget
  have holdIndex : oldi.succ = earlierPrefix := by
    simpa using hbaseTarget.symm
  have hnewStep :=
    corr.replacementSeries.certified earlierPrefix
  generalize hnewTarget : earlierPrefix = newTarget at hnewStep
  cases hnewStep with
  | initial tripleNew seedLengthNew initialColoringNew
      initialStoredNew initialEdgesNew initialKindNew
      initialVertexNew initialOutsideNew initialDeltaNew
      initialGammaNew initialClosureNew =>
      have hk : corr.replacementSeries.data.kind 0 =
          some TashkinovExtensionKind.PE := by
        rw [← hnewTarget]
        exact available.earlierPE
      have hbad := initialKindNew.symm.trans
        hk
      simp at hbad
  | SE newi newPreviousProper newPreviousOne newPreviousClosed
      newPreviousNotStrong newNoRE newChoicePE newAlternative
      newCurrentColoring newCurrentStored newCurrentEdges
      newCurrentKind newCurrentVertex newCurrentOutside
      newCurrentDelta newCurrentGamma newAdjoined
      newAdjoinedExactly newClosedExtension newOrderedExtension
      newStrictExtension =>
      have hk : corr.replacementSeries.data.kind newi.succ =
          some TashkinovExtensionKind.PE := by
        rw [← hnewTarget]
        exact available.earlierPE
      have hbad := newCurrentKind.symm.trans
        hk
      cases hbad
  | RE newi newPreviousProper newPreviousOne newPreviousClosed
      newPreviousNotStrong newAvailable newCurrentColoring
      newCurrentStored newCurrentEdges newCurrentKind
      newCurrentVertex newCurrentOutside newCurrentDelta
      newCurrentGamma newAdjoined newAdjoinedExactly
      newClosedExtension newOrderedExtension newStrictExtension =>
      have hk : corr.replacementSeries.data.kind newi.succ =
          some TashkinovExtensionKind.PE := by
        rw [← hnewTarget]
        exact available.earlierPE
      have hbad := newCurrentKind.symm.trans
        hk
      cases hbad
  | PE newi newPreviousProper newPreviousOne newPreviousClosed
      newPreviousNotStrong newNoRE newChoicePE
      newAlternativeFails newGamma newGammaRule newSecond
      newSecondProper newSecondOne newSecondStable newExit
      newCurrentColoring newCurrentProper newCurrentOne
      newCurrentStored newCurrentEdges newCurrentKind
      newCurrentVertex newCurrentOutside newCurrentDelta
      newCurrentGamma newClosedExtension newOrderedExtension
      newStrictExtension =>
          exact @helper_branch_377 V E inferInstance inferInstance inferInstance G k e0 input T
              generating ett hroundLarge hlower sigmaPrev hsigmaPrevProper hsigmaPrevOne
              previousProper previousOneUncolored hsigmaPrevStableQ originalPrefix hr hprefixMP
              hprefixTrees hprefixData corr hcorrFinalColor hcorrMP noRevisiting hqSucc
              horiginalPositive hlastMap hreplacementCurrentTree horiginalCurrentTree peRootOnly
              available hearlierPositive hbaseEarlierKind oldi oldChoice oldGamma oldGammaRule
              oldSecond oldSecondProper oldSecondStable oldCurrentColoring oldCurrentProper
              oldCurrentOne oldCurrentStored oldCurrentEdges oldCurrentKind oldCurrentVertex
              oldCurrentDelta oldCurrentGamma hbaseTarget holdIndex newi newPreviousProper
              newPreviousOne newPreviousClosed newPreviousNotStrong newNoRE newChoicePE
              newAlternativeFails newGamma newGammaRule newSecond newSecondProper newSecondStable
              newExit newCurrentColoring newCurrentProper newCurrentOne newCurrentStored
              newCurrentEdges newCurrentKind newCurrentVertex newCurrentOutside newCurrentDelta
              newCurrentGamma newClosedExtension newOrderedExtension newStrictExtension hnewTarget
theorem P2971_T1_PositivePrefixNoRevisiting {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (_ : MaximumProperty ett) (hroundLarge : 1 < ett.rounds)
    (hlower : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
       let Tnext : TreeSequence G e0 :=
         lower.series.data.tree (Fin.last (lower.rounds + 1))
       ∀ sigma : PartialEdgeColoring E k,
         IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
         StableColoring Tnext
           (TashkinovStoredColors lower.series.data n)
           (lower.series.data.coloring n) sigma →
         ∀ alpha beta : Fin k,
           (alpha ∈ TreeMissingColors sigma Tnext ∨
             beta ∈ TreeMissingColors sigma Tnext) →
           TreeInterchangeable G Tnext sigma alpha beta) ∧
      (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
       let Tn : TreeSequence G e0 := lower.series.data.tree n.castSucc
       ∀ (v : V) (gamma delta : Fin k),
         lower.series.data.kind n = some TashkinovExtensionKind.PE →
         lower.series.data.chosenVertex n = some v →
         lower.series.data.gamma n = some gamma →
         lower.series.data.delta n = some delta →
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ w, w ∈ TreeSequenceVertexSet Tn →
             (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                 (Sum.inl v) ↔ w = v))) :
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  let Tn : TreeSequence G e0 :=
    ett.series.data.tree (Fin.last ett.rounds).castSucc
  ∀ (sigmaPrev : PartialEdgeColoring E k),
  IsProperEdgeColoring G sigmaPrev →
  IsOneEdgeUncolored sigmaPrev e0 →
  IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
  IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 →
  StableColoring (ett.series.data.tree q.succ.castSucc)
    (TashkinovStoredColors ett.series.data q.castSucc)
    (ett.series.data.coloring q.castSucc) sigmaPrev →
  ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input Tn
      (ett.series.data.coloring q.castSucc))
    (hr : originalPrefix.rounds = ett.rounds - 1),
  MaximumProperty originalPrefix →
  (
  ∀ i : Fin (originalPrefix.rounds + 2),
  originalPrefix.series.data.tree i =
    ett.series.data.tree (Fin.castLE (by omega) i)) →
  (
  ∀ i : Fin (originalPrefix.rounds + 1),
  originalPrefix.series.data.coloring i =
      ett.series.data.coloring (Fin.castLE (by omega) i) ∧
  originalPrefix.series.data.stored i =
      ett.series.data.stored (Fin.castLE (by omega) i) ∧
  originalPrefix.series.data.connectingEdges i =
      ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
  originalPrefix.series.data.kind i =
      ett.series.data.kind (Fin.castLE (by omega) i) ∧
  TashkinovStoredColors originalPrefix.series.data i =
      TashkinovStoredColors ett.series.data
        (Fin.castLE (by omega) i)) →
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0
      originalPrefix sigmaPrev Tn),
  corr.replacementSeries.data.tree
      (Fin.last (originalPrefix.rounds + 1)) = Tn →
  corr.replacementSeries.data.coloring
      (Fin.last originalPrefix.rounds) = sigmaPrev →
  MaximumProperty corr.replacementETT →
  (¬ Nonempty (RevisitingExtensionCertificate ett.series.data
    q.castSucc)) →
  ¬ Nonempty (RevisitingExtensionCertificate
    corr.replacementSeries.data (Fin.last originalPrefix.rounds)) := by
  classical
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  change ∀ sigmaPrev, _
  intro sigmaPrev hsigmaPrevProper hsigmaPrevOne previousProper
    previousOneUncolored hsigmaPrevStableQ originalPrefix hr hprefixMP
    hprefixTrees hprefixData corr hcorrFinalTree hcorrFinalColor hcorrMP
    noRevisiting
  have hqSucc : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  let replacementLast : Fin (originalPrefix.rounds + 1) :=
    Fin.last originalPrefix.rounds
  have horiginalPositive : 0 < originalPrefix.rounds := by
    rw [hr]
    omega
  have hlastMap : Fin.castLE (by omega) replacementLast =
      q.castSucc := by
    apply Fin.ext
    simp [replacementLast, q, hr]
  have hreplacementCurrentTree :
      corr.replacementSeries.data.tree replacementLast.succ =
        ett.series.data.tree q.succ.castSucc := by
    have hlastTree : replacementLast.succ =
        Fin.last (originalPrefix.rounds + 1) := by
      apply Fin.ext
      simp [replacementLast]
    rw [hlastTree, hcorrFinalTree, hqSucc]
  have horiginalCurrentTree :
      originalPrefix.series.data.tree replacementLast.castSucc =
        ett.series.data.tree q.castSucc.castSucc := by
    calc
      originalPrefix.series.data.tree replacementLast.castSucc =
          ett.series.data.tree
            (Fin.castLE (by omega) replacementLast.castSucc) :=
        hprefixTrees replacementLast.castSucc
      _ = ett.series.data.tree q.castSucc.castSucc := by
        congr 1
        apply Fin.ext
        simp [replacementLast, q, hr]
  have peRootOnly :=
    @helper_peRootOnly_167 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett hroundLarge hlower originalPrefix hr
  rintro ⟨available⟩
  let earlierPrefix : Fin (originalPrefix.rounds + 1) :=
    available.earlier
  have hearlierPositive : 0 < earlierPrefix.val :=
    available.earlierPositive
  have hbaseEarlierKind : originalPrefix.series.data.kind
      earlierPrefix = some TashkinovExtensionKind.PE := by
    rw [← corr.extensionKindsAgree earlierPrefix]
    exact available.earlierPE
  have hbaseStep := originalPrefix.series.certified earlierPrefix
  generalize hbaseTarget : earlierPrefix = baseTarget at hbaseStep
  cases hbaseStep with
  | initial tripleBase seedLengthBase initialColoringBase
      initialStoredBase initialEdgesBase initialKindBase
      initialVertexBase initialOutsideBase initialDeltaBase
      initialGammaBase initialClosureBase =>
      have hbad := initialKindBase.symm.trans
        (by simpa [hbaseTarget] using hbaseEarlierKind)
      simp at hbad
  | SE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldNoRE oldChoice oldAlternative
      oldCurrentColoring oldCurrentStored oldCurrentEdges
      oldCurrentKind oldCurrentVertex oldCurrentOutside
      oldCurrentDelta oldCurrentGamma oldAdjoined
      oldAdjoinedExactly oldClosedExtension oldOrderedExtension
      oldStrictExtension =>
      have hbad := oldCurrentKind.symm.trans
        (by simpa [hbaseTarget] using hbaseEarlierKind)
      cases hbad
  | RE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldAvailable oldCurrentColoring
      oldCurrentStored oldCurrentEdges oldCurrentKind
      oldCurrentVertex oldCurrentOutside oldCurrentDelta
      oldCurrentGamma oldAdjoined oldAdjoinedExactly
      oldClosedExtension oldOrderedExtension oldStrictExtension =>
      have hbad := oldCurrentKind.symm.trans
        (by simpa [hbaseTarget] using hbaseEarlierKind)
      cases hbad
  | PE oldi oldPreviousProper oldPreviousOne oldPreviousClosed
      oldPreviousNotStrong oldNoRE oldChoice oldAlternativeFails
      oldGamma oldGammaRule oldSecond oldSecondProper oldSecondOne
      oldSecondStable oldExit oldCurrentColoring oldCurrentProper
      oldCurrentOne oldCurrentStored oldCurrentEdges oldCurrentKind
      oldCurrentVertex oldCurrentOutside oldCurrentDelta
      oldCurrentGamma oldClosedExtension oldOrderedExtension
      oldStrictExtension =>
          exact @helper_branch_280 V E inferInstance inferInstance inferInstance G k e0 input T
              generating ett hroundLarge hlower sigmaPrev hsigmaPrevProper hsigmaPrevOne
              previousProper previousOneUncolored hsigmaPrevStableQ originalPrefix hr hprefixMP
              hprefixTrees hprefixData corr hcorrFinalColor hcorrMP noRevisiting hqSucc
              horiginalPositive hlastMap hreplacementCurrentTree horiginalCurrentTree peRootOnly
              available hearlierPositive hbaseEarlierKind oldi oldChoice oldGamma oldGammaRule
              oldSecond oldSecondProper oldSecondStable oldCurrentColoring oldCurrentProper
              oldCurrentOne oldCurrentStored oldCurrentEdges oldCurrentKind oldCurrentVertex
              oldCurrentDelta oldCurrentGamma hbaseTarget
end GoldbergSeymour

end
