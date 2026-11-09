/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeAssembly

public import LeanPool.GoldbergSeymour.TashkinovSeriesStability

public import LeanPool.GoldbergSeymour.SharedFacts.TerminalRebuildTransport

public import LeanPool.GoldbergSeymour.TerminalSeriesRebuildPreparation
public import LeanPool.GoldbergSeymour.TashkinovSeriesAppend
public import LeanPool.GoldbergSeymour.ExtensionBase
public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors
public import LeanPool.GoldbergSeymour.TashkinovSeriesSwapComponentEdgeUnique

/-!
# Transport lemmas for terminal extension reconstruction

Part of Wesley Pegden’s Trellis formalization of the Goldberg–Seymour theorem,
commit 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas support the
reconstruction of terminal series extensions.
-/

@[expose] public section

namespace GoldbergSeymour.TerminalSeriesRebuild

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperRetainedPEFields13584Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (Tstar : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive T
      omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (previousProper : IsProperEdgeColoring G (ett.series.data.coloring
        q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring
        q.castSucc) e0) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (sigmaPrev : PartialEdgeColoring E k)
        (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev) (hsigmaPrevOne : IsOneEdgeUncolored
        sigmaPrev e0) (hsigmaPrevStableQ : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev) (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice4049 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
           have := GoldbergSeymour.TreeSequence.positive T
           omega
    ) i)) → (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
             have := GoldbergSeymour.TreeSequence.positive T
             omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
               have := GoldbergSeymour.TreeSequence.positive T
               omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (horiginalPositive : (0 : ℕ) <
        originalPrefix.rounds), (
    ∀ (j : Fin (originalPrefix.rounds + (1 : ℕ))), corr.replacementSeries.data.kind j =
        ett.series.data.kind (Fin.castLE (
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ) j)) → (
    ∀ (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k) (ch :
        MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
        IsProperEdgeColoring G second → StableColoring X (insert ch.color C : Finset (Fin k))
        ch.selected second → g ∈ MissingColors G ch.selected ch.vertex →
    let post : PartialEdgeColoring E k := TwoColorComponentSwap G second g ch.color (Sum.inl
        ch.vertex); ch.color ∈ MissingColors G post ch.vertex ∧ g ∉ MissingColors G post ch.vertex
        ∧ g ≠ ch.color) →
    ∀ (j : Fin (originalPrefix.rounds + (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) →
        corr.replacementSeries.data.kind j = some TashkinovExtensionKind.PE →
        corr.replacementSeries.data.chosenVertex j = ett.series.data.chosenVertex (Fin.castLE (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) j) ∧ corr.replacementSeries.data.delta j = ett.series.data.delta (Fin.castLE (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   omega
    ) j) ∧ corr.replacementSeries.data.gamma j = ett.series.data.gamma (Fin.castLE (
    by
                   have := GoldbergSeymour.TreeSequence.positive T
                   omega
    ) j)

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch11555Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring (Fin.last ett.rounds))
        sigma →
    ∀ (Tstar : TreeSequence G e0), TreeSequenceInitialSegment (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) Tstar → (ett.series.data.tree (Fin.last ett.rounds).castSucc).length
        < Tstar.length →
    ∀ (closureTree : TreeSequence G e0), TashkinovClosure sigma Tstar closureTree →
        TreeSequenceInitialSegment Tstar closureTree → TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (adjoined : TreeSequence G e0) (previousProper : IsProperEdgeColoring G
        (ett.series.data.coloring q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored
        (ett.series.data.coloring q.castSucc) e0) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), ett.series.data.stored q.succ = ({ choice.color }
        : Finset (Fin k)) → ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E)
        → ett.series.data.kind q.succ = some TashkinovExtensionKind.SE →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev), sigmaPrev = sigma →
    ∀ (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hsigmaPrevSelf : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice2409 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; ColoredVertexSetClosed G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) → (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected pi
        → Disjoint (MissingColors G pi newChoice.otherEndpoint) (TreeMissingColors pi
        (ett.series.data.tree q.succ.castSucc))) → ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput), zeroPrefix.data.tree (Fin.last (1 : ℕ)) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc → zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev →
        ((ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges (Fin.last ett.rounds) =
        ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) f seed ∧ TashkinovAugmentationSequence sigma seed Tstar) → Nonempty
        (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

private abbrev helperContinuation4951Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring (Fin.last ett.rounds))
        sigma →
    ∀ (Tstar : TreeSequence G e0), TreeSequenceInitialSegment (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) Tstar → (ett.series.data.tree (Fin.last ett.rounds).castSucc).length
        < Tstar.length →
    ∀ (closureTree : TreeSequence G e0), TreeSequenceInitialSegment Tstar closureTree →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.stored q.succ = ({ choice.color } : Finset (Fin k)) →
        ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.SE →
    ∀ (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev → IsOneEdgeUncolored
        sigmaPrev e0 → ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree (Fin.last (2 : ℕ)) = closureTree → appendedData.coloring
        (Fin.last (1 : ℕ)) = sigma → appendedData.stored (Fin.last (1 : ℕ)) = newStored →
        appendedData.connectingEdges (Fin.last (1 : ℕ)) = newEdges → appendedData.kind (Fin.last
        (1 : ℕ)) = newKind → appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree
        q.succ.castSucc → appendedData.coloring zeroLast.castSucc = sigmaPrev →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma → (0 : ℕ) + (1 : ℕ) =
        ett.rounds →
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b} (h : a = b) series => series.castRounds h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) → (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)) → Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperHsigmaPrevEnlarged12232Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
    ∀ (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
         have := GoldbergSeymour.TreeSequence.positive T
         omega
    ⟩ : Fin ett.rounds); StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable → IsOneEdgeUncolored secondStable e0 →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ParallelExtensionColor ett.series.data q.castSucc choice.selected choice.vertex gamma →
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) choice.selected
        secondStable → TreeExit (ett.series.data.tree q.succ.castSucc) secondStable gamma
        choice.color choice.vertex → ett.series.data.coloring q.succ = TwoColorComponentSwap G
        secondStable gamma choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G
        (ett.series.data.coloring q.succ) → IsOneEdgeUncolored (ett.series.data.coloring q.succ)
        e0 → ett.series.data.stored q.succ = (insert choice.color ({ gamma } : Finset (Fin k)) :
        Finset (Fin k)) →
    ∀ (sigmaPrev : PartialEdgeColoring E k), choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), Sum.inl w ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔ w = choice.vertex)
        → sigmaPrev = TwoColorComponentSwap G sigma gamma choice.color (Sum.inl choice.vertex) →
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) choice.selected
        sigmaPrev

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch12991Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive T
      omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
           have := GoldbergSeymour.TreeSequence.positive T
           omega
    ) i)) → (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
             have := GoldbergSeymour.TreeSequence.positive T
             omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
               have := GoldbergSeymour.TreeSequence.positive T
               omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : (0 : ℕ) <
        originalPrefix.rounds), (
    ∀ (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k) (ch :
        MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
        IsProperEdgeColoring G second → StableColoring X (insert ch.color C : Finset (Fin k))
        ch.selected second → g ∈ MissingColors G ch.selected ch.vertex →
    let post : PartialEdgeColoring E k := TwoColorComponentSwap G second g ch.color (Sum.inl
        ch.vertex); ch.color ∈ MissingColors G post ch.vertex ∧ g ∉ MissingColors G post ch.vertex
        ∧ g ≠ ch.color) →
    ∀ (j : Fin (originalPrefix.rounds + (1 : ℕ))),
    let fullj : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE (
    by
             have := GoldbergSeymour.TreeSequence.positive T
             omega
    ) j;
    ∀ (fulli : Fin ett.rounds) (fullChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)) (fullGamma : Fin k), ParallelExtensionColor
        ett.series.data fulli.castSucc fullChoice.selected fullChoice.vertex fullGamma →
    ∀ (fullSecond : PartialEdgeColoring E k), IsProperEdgeColoring G fullSecond → StableColoring
        (ett.series.data.tree fulli.succ.castSucc) (insert fullChoice.color (TashkinovStoredColors
        ett.series.data fulli.castSucc) : Finset (Fin k)) fullChoice.selected fullSecond →
        ett.series.data.coloring fulli.succ = TwoColorComponentSwap G fullSecond fullGamma
        fullChoice.color (Sum.inl fullChoice.vertex) → ett.series.data.stored fulli.succ = (insert
        fullChoice.color ({ fullGamma } : Finset (Fin k)) : Finset (Fin k)) →
        ett.series.data.connectingEdges fulli.succ = ({ fullChoice.edge } : Finset E) →
        ett.series.data.chosenVertex fulli.succ = some fullChoice.vertex → ett.series.data.delta
        fulli.succ = some fullChoice.color → ett.series.data.gamma fulli.succ = some fullGamma →
        fullj = fulli.succ → fulli.succ = fullj →
    ∀ (newi : Fin originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (newGamma : Fin k), ParallelExtensionColor corr.replacementSeries.data
        newi.castSucc newChoice.selected newChoice.vertex newGamma →
    ∀ (newSecond : PartialEdgeColoring E k), IsProperEdgeColoring G newSecond → StableColoring
        (corr.replacementSeries.data.tree newi.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc) : Finset (Fin k))
        newChoice.selected newSecond → corr.replacementSeries.data.coloring newi.succ =
        TwoColorComponentSwap G newSecond newGamma newChoice.color (Sum.inl newChoice.vertex) →
        corr.replacementSeries.data.stored newi.succ = (insert newChoice.color ({ newGamma } :
        Finset (Fin k)) : Finset (Fin k)) → corr.replacementSeries.data.connectingEdges newi.succ
        = ({ newChoice.edge } : Finset E) → corr.replacementSeries.data.chosenVertex newi.succ =
        some newChoice.vertex → corr.replacementSeries.data.delta newi.succ = some newChoice.color
        → corr.replacementSeries.data.gamma newi.succ = some newGamma → j = newi.succ →
        corr.replacementSeries.data.chosenVertex newi.succ = ett.series.data.chosenVertex
        (Fin.castLE (
    by
                                        have := GoldbergSeymour.TreeSequence.positive T
                                        omega
    ) newi.succ) ∧ corr.replacementSeries.data.delta newi.succ = ett.series.data.delta (Fin.castLE
        (
    by
                                         have := GoldbergSeymour.TreeSequence.positive T
                                         omega
    ) newi.succ) ∧ corr.replacementSeries.data.gamma newi.succ = ett.series.data.gamma (Fin.castLE
        (
    by
                                         have := GoldbergSeymour.TreeSequence.positive T
                                         omega
    ) newi.succ)

private abbrev helperContinuation7494Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (hsigmaProper : IsProperEdgeColoring G sigma) (hsigmaOne : IsOneEdgeUncolored sigma e0)
        (hsigmaStable : StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma) (Tstar : TreeSequence G e0) (hTnTstar :
        TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tstar)
        (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < Tstar.length)
        (closureTree : TreeSequence G e0) (hTstarClosure : TreeSequenceInitialSegment Tstar
        closureTree),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqSucc : q.succ = Fin.last ett.rounds) (gamma : Fin k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)) (currentStored : ett.series.data.stored
        q.succ = (insert choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)))
        (currentEdges : ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E))
        (currentKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE) (sigmaPrev :
        PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (a b : V ⊕ E) (p_1 : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b) (a_1
        : p_1.IsPath) (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hp : p.IsPath)
        (hroundOne : ett.rounds = (1 : ℕ)) (prefixInput : PartialEdgeColoring E k) (zeroPrefix :
        TashkinovSeries G k (0 : ℕ) e0 prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma;
    ∀ (happendLastTree : appendedData.tree (Fin.last (2 : ℕ)) = closureTree) (happendLastColor :
        appendedData.coloring (Fin.last (1 : ℕ)) = sigma) (happendLastStored : appendedData.stored
        (Fin.last (1 : ℕ)) = newStored) (happendLastEdges : appendedData.connectingEdges (Fin.last
        (1 : ℕ)) = newEdges) (happendLastKind : appendedData.kind (Fin.last (1 : ℕ)) = newKind)
        (happendTree : appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree
        q.succ.castSucc) (happendColor : appendedData.coloring zeroLast.castSucc = sigmaPrev)
        (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput) (hextendedData :
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma) (hroundsEq : (0 : ℕ) +
        (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → (h : a = b) → (S : TashkinovSeries G k a e0 prefixInput) →
        TashkinovSeries G k b e0 prefixInput := fun {a b : ℕ} (h : a = b) (S : TashkinovSeries G k
        a e0 prefixInput) ↦ S.castRounds h;
    ∀ (castSeriesTree :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) (castSeriesColoring :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.coloring i = S.data.coloring (Fin.cast (
    by omega
    ) i)) (castSeriesStored :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.stored i = S.data.stored (Fin.cast (
    by omega
    ) i)) (castSeriesEdges :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (1 : ℕ))),
        (castSeries h S).data.connectingEdges i = S.data.connectingEdges (Fin.cast (
    by omega
    ) i)), Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

/-- Dependent contract shared by the terminal series reconstruction proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch12554Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring (Fin.last ett.rounds))
        sigma →
    ∀ (Tstar : TreeSequence G e0), TreeSequenceInitialSegment (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) Tstar → (ett.series.data.tree (Fin.last ett.rounds).castSucc).length
        < Tstar.length →
    ∀ (closureTree : TreeSequence G e0), TashkinovClosure sigma Tstar closureTree →
        TreeSequenceInitialSegment Tstar closureTree → TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (_ : PartialEdgeColoring E k) (previousProper : IsProperEdgeColoring G
        (ett.series.data.coloring q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored
        (ett.series.data.coloring q.castSucc) e0) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), ett.series.data.stored q.succ = (insert
        choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)) →
        ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev) (hchoiceDefective : DefectiveColor G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice4049 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; ColoredVertexSetClosed G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) → (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected
        rho ∧ ¬Disjoint (MissingColors G rho newChoice.otherEndpoint) (TreeMissingColors rho
        (ett.series.data.tree q.succ.castSucc))) → gamma ∈ MissingColors G sigmaPrev choice.vertex
        → sigma = TwoColorComponentSwap G sigmaPrev gamma choice.color (Sum.inl choice.vertex) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (a b : V ⊕ E) (p_1 : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b),
        p_1.IsPath →
    ∀ (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), p.IsPath → TreeExit
        (ett.series.data.tree q.succ.castSucc) sigmaPrev gamma choice.color choice.vertex →
        ett.rounds = (1 : ℕ) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput), zeroPrefix.data.tree (Fin.last (1 : ℕ)) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc → zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev →
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        Tstar → Nonempty (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar)

theorem helper_hnoRevisitingAppended_4214.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        ¬Nonempty (RevisitingExtensionCertificate corr.replacementSeries.data replacementLast) →
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let appendedData : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
        newKind newVertex newOutside newDelta newGamma; ¬Nonempty (RevisitingExtensionCertificate
        appendedData replacementLast.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q choice
      sigmaPrev originalPrefix corr replacementLast hnoRevisitingReplacement newStored newEdges
      newKind newVertex newOutside newDelta newGamma appendedData
  rintro ⟨cert⟩
  obtain ⟨oldCert, -, -, -, -, -⟩ :=
    (RevisitingExtensionCertificateAppend
      corr.replacementSeries.data closureTree sigma newStored
      newEdges newKind newVertex newOutside newDelta newGamma
      replacementLast).1 cert
  exact hnoRevisitingReplacement ⟨oldCert⟩

theorem helper_hseriesTreeAgree_4578.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix
        : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : (0 : ℕ) <
        originalPrefix.rounds),
    let newStored : Finset (Fin k) := ({ choice.color } : Finset (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.SE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := none;
    let _ : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
        newKind newVertex newOutside newDelta newGamma;
    ∀ (extendedSeries : TashkinovSeries G k (originalPrefix.rounds + (1 : ℕ)) e0
        corr.replacementInput), extendedSeries.data = TashkinovSeriesDataAppend
        corr.replacementSeries.data closureTree sigma newStored newEdges newKind newVertex
        newOutside newDelta newGamma →
    ∀ (hroundsEq : originalPrefix.rounds + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 corr.replacementInput →
        TashkinovSeries G k b e0 corr.replacementInput :=
          fun {a b} (h : a = b) series => series.castRounds h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (2
        : ℕ))), (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries; finalSeries.data.tree (⟨ett.rounds,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc →
    let _ : Fin (ett.rounds + (2 : ℕ)) → Fin (originalPrefix.rounds + (3 : ℕ)) := fun (i : Fin
        (ett.rounds + (2 : ℕ))) ↦ Fin.cast (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) i;
    ∀ (i : Fin ett.rounds), finalSeries.data.tree i.succ.castSucc = ett.series.data.tree
        i.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q choice
      sigmaPrev hroundLarge originalPrefix hr hprefixTrees corr horiginalPositive newStored
      newEdges newKind newVertex newOutside newDelta newGamma appendedData extendedSeries
      hextendedData hroundsEq castSeries castSeriesTree finalSeries hfinalPenultimateTree
      rawTreeIndex i
  by_cases hi : i.val < originalPrefix.rounds
  · let j : Fin originalPrefix.rounds := ⟨i.val, hi⟩
    have hraw : rawTreeIndex i.succ.castSucc =
        j.succ.castSucc.castSucc := by
      apply Fin.ext
      rfl
    have hmap : Fin.castLE (by omega) j.succ.castSucc =
        i.succ.castSucc := by
      apply Fin.ext
      rfl
    calc
      finalSeries.data.tree i.succ.castSucc =
          extendedSeries.data.tree
            (rawTreeIndex i.succ.castSucc) := by
            exact castSeriesTree hroundsEq extendedSeries _
      _ = appendedData.tree
            (rawTreeIndex i.succ.castSucc) := by
            rw [hextendedData]
      _ = corr.replacementSeries.data.tree
            j.succ.castSucc := by
            rw [hraw]
            simp only [appendedData,
              TashkinovSeriesDataAppend]
            convert (Fin.lastCases_castSucc
              j.succ.castSucc) using 1
      _ = originalPrefix.series.data.tree
            j.succ.castSucc := corr.ladderTreesAgree j
      _ = ett.series.data.tree
            (Fin.castLE (by omega) j.succ.castSucc) :=
            hprefixTrees j.succ.castSucc
      _ = ett.series.data.tree i.succ.castSucc := by rw [hmap]
  · let ilast : Fin ett.rounds :=
      ⟨ett.rounds - 1, by omega⟩
    have hilast : i = ilast := by
      apply Fin.ext
      have hiBound := i.isLt
      have hprefixRounds := hr
      simp [ilast]
      omega
    rw [hilast]
    have hindex :
        ilast.succ.castSucc =
          (Fin.last ett.rounds).castSucc := by
      apply Fin.ext
      simp [ilast]
      omega
    rw [hindex]
    exact hfinalPenultimateTree

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_hi_4786.{u_1, u_2} :
    SharedFacts.RevisitingTerminalPreparation.hiStatement.{u_1, u_2} :=
  SharedFacts.RevisitingTerminalPreparation.hi.{u_1, u_2}

theorem helper_hcomponent_4809.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring
        (Fin.last ett.rounds)) sigma →
    ∀ (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.chosenVertex q.succ = some choice.vertex → ett.series.data.delta q.succ =
        some choice.color → ett.series.data.gamma q.succ = some gamma → ett.series.data.kind
        q.succ = some TashkinovExtensionKind.PE →
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), Sum.inl w ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔ w = choice.vertex
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower sigma hsigmaProper hsigmaOne
      hsigmaStable _ q hqSucc gamma choice currentVertex currentDelta currentGamma hpeKind
  have hbase := ExtensionBase G k e0 input T generating ett hMP hpositive
    hlower choice.vertex gamma choice.color
    (by simpa [hqSucc] using hpeKind)
    (by simpa [hqSucc] using currentVertex)
    (by simpa [hqSucc] using currentGamma)
    (by simpa [hqSucc] using currentDelta)
    sigma hsigmaProper hsigmaOne
    (by simpa [hqSucc] using hsigmaStable)
  simpa [hqSucc] using hbase

theorem helper_hpathComponent_4867.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)) (u : V) (path : (TwoColorIncidenceGraph
        G secondStable gamma choice.color).Walk (Sum.inl u) (Sum.inl choice.vertex)), (
    ∀ x ∈ path.support,
    ∀ (y : V ⊕ E), (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj x y → y ∈
        path.support) →
    ∀ y ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex), y ∈
        path.support := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable choice u
      path hclosed y hy
  let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
  have reach : graph.Reachable (Sum.inl choice.vertex) y := by
    change graph.connectedComponentMk y = graph.connectedComponentMk (Sum.inl
        choice.vertex) at hy
    exact SimpleGraph.ConnectedComponent.eq.mp hy |>.symm
  exact reach.mem_subgraphVerts (H := (⊤ : graph.Subgraph).induce {x | x ∈ path.support})
    (fun x hx z hadj => ⟨by simpa using hx, hclosed x (by simpa using hx) z hadj, hadj⟩)
    (by simp)

theorem helper_hcompEdge_4879.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)) (_ : V) (e : E), Sum.inr e ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → secondStable
        e = some gamma ∨ secondStable e = some choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable choice u e he
  exact TwoColorComponent.edge_colors he

theorem helper_hchoiceSecond_4895.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) :
        Finset (Fin k)) choice.selected secondStable → secondStable choice.edge = some
        choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q secondStable choice
      secondStableRelation
  have heq := secondStableRelation.1 choice.edge
    ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
    ⟨choice.color, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
      choice.edgeColor⟩
  exact heq.trans choice.edgeColor

theorem helper_hneq_4901.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)), gamma ∈ MissingColors G secondStable
        choice.vertex → secondStable choice.edge = some choice.color → gamma ≠ choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable choice
      hmissing hchoiceSecond heq
  have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨choice.edge, choice.edgeIncident, heq ▸ hchoiceSecond⟩
  have hpnot : gamma ∉ PresentColors G secondStable choice.vertex := by
    simpa [MissingColors] using hmissing
  exact hpnot hp

theorem helper_hsigmaEdge_4922.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma →
    ∀ (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        ett.series.data.coloring q.succ = TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex) → ett.series.data.stored q.succ = (insert choice.color ({ gamma }
        : Finset (Fin k)) : Finset (Fin k)) → choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), Sum.inl w ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) ↔ w = choice.vertex)
        → gamma ∈ MissingColors G secondStable choice.vertex →
    ∀ (_ : V), (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some gamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color → gamma ≠ choice.color → Sum.inr choice.edge
        ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) →
    ∀ (e : E), TreeIncidentEdge (ett.series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) → e = choice.edge := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper Tstar q
      hsigmaStableQ gamma secondStable secondStableProper choice currentColoring currentStored
      hchoiceVertex hcomponent hmissing u hcompEdge hchoiceSecond hneq hfcomponent
  exact ett.series.stableSwapComponentIncidentEdgeUnique q sigma hsigmaProper hsigmaStableQ
    gamma secondStable choice currentColoring currentStored hcomponent hmissing hchoiceSecond hneq

theorem helper_treeMissingTransport_4940.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (a b : PartialEdgeColoring E k), (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), MissingColors G a w =
        MissingColors G b w) → TreeMissingColors a (ett.series.data.tree q.succ.castSucc) =
        TreeMissingColors b (ett.series.data.tree q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q a b hab
  ext c
  unfold TreeMissingColors
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hw, hc⟩
    exact ⟨w, hw, by rw [hab w hw] at hc; exact hc⟩
  · rintro ⟨w, hw, hc⟩
    exact ⟨w, hw, by rw [hab w hw]; exact hc⟩

theorem helper_sigmaComponentColor_4960.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (_ : V) (e : E), Sum.inr e ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl
        choice.vertex) → sigma e = some gamma ∨ sigma e = some choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q gamma choice u e he
  exact TwoColorComponent.edge_colors he

theorem helper_gammaControl_5005.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)), StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) :
        Finset (Fin k)) choice.selected secondStable → choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → gamma ∈ MissingColors G secondStable
        choice.vertex → gamma ∈ TreeMissingColors choice.selected (ett.series.data.tree
        q.succ.castSucc) ∪ (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc)
        : Finset (Fin k)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable choice
      secondStableRelation hchoiceVertex hmissing
  apply Finset.mem_union.mpr
  left
  unfold TreeMissingColors
  simp only [Finset.mem_biUnion]
  refine ⟨choice.vertex, hchoiceVertex, ?_⟩
  rw [← secondStableRelation.2 choice.vertex
    choice.vertexDefective.1]
  exact hmissing

theorem helper_branch_5026.{u_1, u_2} :
    helperBranch5026Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q hsigmaStableQ gamma
      secondStable secondStableProper secondStableOneUncolored choice secondStableRelation
      currentColoring hdegree u path hdegreeBound hclosed hpathComponent hcompEdge hchoiceSecond
      htreeEdge hsigmaEdge undone treeSecondSelected sigmaComponentColor sigmaColorMissing
      currentControl gammaControl f hf h
  rcases h with ⟨c, hc, hcf⟩
  rw [treeSecondSelected] at hc
  have h' := ((sc1 G e0 (ett.series.data.tree q.succ.castSucc)
    (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
    choice.selected secondStable choice.selectedProper choice.selectedOneUncolored
    secondStableProper secondStableOneUncolored).mp secondStableRelation) f hf
    (Or.inr ⟨c, hc, hcf⟩)
  have hs := hsigmaStableQ.1 f hf
  by_cases hsf : Sum.inr f ∈
      TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
  · have ef := hsigmaEdge f hf hsf
    subst f
    rcases sigmaComponentColor choice.edge hsf with hec | hec
    · simp [undone, TwoColorComponentSwap, hsf, hec, hchoiceSecond]
    · exfalso
      have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
        simpa [MissingColors] using sigmaColorMissing
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨choice.edge, choice.edgeIncident, hec⟩
  · have hu : undone f = sigma f := by
      change (if Sum.inr f ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) then
          (if sigma f = some gamma then some choice.color
          else if sigma f = some choice.color then some gamma else sigma f)
        else sigma f) = sigma f
      exact ite_eq_right hsf
    rw [hu]
    clear hdegree hdegreeBound hclosed hpathComponent hcompEdge
      hsigmaEdge sigmaComponentColor
    by_cases ha : Sum.inr f ∈
        TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex)
    · have he := htreeEdge f hf ha
      subst f
      have hcGamma := currentControl gamma gammaControl
      have hsGamma := hsigmaStableQ.1 choice.edge
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
        ⟨gamma, hcGamma, by
          rw [currentColoring]
          simp [TwoColorComponentSwap, ha, hchoiceSecond]⟩
      have hcurGamma : ett.series.data.coloring q.succ choice.edge =
          some gamma := by
        rw [currentColoring]
        simp [TwoColorComponentSwap, ha, hchoiceSecond]
      have hsigGamma : sigma choice.edge = some gamma :=
        hsGamma.trans hcurGamma
      have hmem : Sum.inr choice.edge ∈
          TwoColorComponent G sigma gamma choice.color
            (Sum.inl choice.vertex) := by
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        simp [TwoColorIncidenceGraph, choice.edgeIncident, hsigGamma]
      exact (hsf hmem).elim
    · have hcur : ett.series.data.coloring q.succ f = some c := by
        rw [currentColoring]
        simp [TwoColorComponentSwap, ha, hcf]
      have hsig := hsigmaStableQ.1 f hf
        ⟨c, currentControl c hc, hcur⟩
      exact hsig.trans (hcur.trans hcf.symm)

theorem helper_branch_5085.{u_1, u_2} :
    helperBranch5085Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne _ q
      hsigmaStableQ gamma secondStable choice currentColoring currentProper currentOneUncolored
      hdegree u path hdegreeBound hclosed hpathComponent hcompEdge hchoiceSecond htreeEdge
      hsigmaEdge undone treeSecondSelected sigmaComponentColor sigmaColorMissing currentControl
      gammaControl f hf h
  rcases h with ⟨c, hc, hcf⟩
  by_cases hsf : Sum.inr f ∈
      TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
  · have ef := hsigmaEdge f hf hsf
    subst f
    rcases sigmaComponentColor choice.edge hsf with hec | hec
    · simp [undone, TwoColorComponentSwap, hsf, hec, hchoiceSecond]
    · exfalso
      have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
        simpa [MissingColors] using sigmaColorMissing
      apply hnot
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨choice.edge, choice.edgeIncident, hec⟩
  · have hu : undone f = sigma f := by
      change (if Sum.inr f ∈
        TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex) then
          (if sigma f = some gamma then some choice.color
          else if sigma f = some choice.color then some gamma else sigma f)
        else sigma f) = sigma f
      exact ite_eq_right hsf
    rw [hu]
    clear hdegree hdegreeBound hclosed hpathComponent hcompEdge
      hsigmaEdge sigmaComponentColor
    rw [treeSecondSelected] at hc
    by_cases ha : Sum.inr f ∈
        TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex)
    · have he := htreeEdge f hf ha
      subst f
      have hcGamma := currentControl gamma gammaControl
      have hsGamma := hsigmaStableQ.1 choice.edge
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
        ⟨gamma, hcGamma, by
          rw [currentColoring]
          simp [TwoColorComponentSwap, ha, hchoiceSecond]⟩
      have hcurGamma : ett.series.data.coloring q.succ choice.edge =
          some gamma := by
        rw [currentColoring]
        simp [TwoColorComponentSwap, ha, hchoiceSecond]
      have hsigGamma : sigma choice.edge = some gamma :=
        hsGamma.trans hcurGamma
      have hmem : Sum.inr choice.edge ∈
          TwoColorComponent G sigma gamma choice.color
            (Sum.inl choice.vertex) := by
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        simp [TwoColorIncidenceGraph, choice.edgeIncident, hsigGamma]
      exact (hsf hmem).elim
    · have hsigmaValue : sigma f = some c := hu.symm.trans hcf
      have hsig := ((sc1 G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ)
        (ett.series.data.coloring q.succ) sigma currentProper currentOneUncolored
        hsigmaProper hsigmaOne).mp hsigmaStableQ) f hf
        (Or.inr ⟨c, currentControl c hc, hsigmaValue⟩)
      have hcur : ett.series.data.coloring q.succ f = some c :=
        (Eq.symm hsig).trans hsigmaValue
      have hsecond : secondStable f = some c := by
        have hcs : ett.series.data.coloring q.succ f = secondStable f := by
          rw [currentColoring]
          simp [TwoColorComponentSwap, ha]
        exact hcs.symm.trans hcur
      exact hsig.trans (hcur.trans hsecond.symm)

theorem helper_stableSelected_5146.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable → IsOneEdgeUncolored secondStable e0 →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) choice.selected
        secondStable →
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma choice.color
        (Sum.inl choice.vertex); IsProperEdgeColoring G undone → IsOneEdgeUncolored undone e0 →
        TreeMissingColors secondStable (ett.series.data.tree q.succ.castSucc) = TreeMissingColors
        choice.selected (ett.series.data.tree q.succ.castSucc) → StableColoring
        (ett.series.data.tree q.succ.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data q.castSucc) : Finset (Fin k)) secondStable undone → StableColoring
        (ett.series.data.tree q.succ.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data q.castSucc) : Finset (Fin k)) choice.selected undone := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar q gamma secondStable
      secondStableProper secondStableOneUncolored choice secondStableRelation undone
      undoneProper undoneOne treeSecondSelected stableSecond
  exact @helper_stableSelected_2405 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@sigma) (@Tstar) (@gamma) (@secondStable) (@secondStableProper)
      (@secondStableOneUncolored) (@choice) (@secondStableRelation) (@undoneProper)
      (@undoneOne) (@treeSecondSelected) (@stableSecond)

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_hchoiceDefective_5167.{u_1, u_2} :
    SharedFacts.TerminalRebuild.hchoiceDefectiveStatement.{u_1, u_2} :=
  SharedFacts.TerminalRebuild.hchoiceDefective.{u_1, u_2}

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_hchoiceEdgeNew_5178.{u_1, u_2} :
    SharedFacts.TerminalRebuild.hchoiceEdgeNewStatement.{u_1, u_2} :=
  SharedFacts.TerminalRebuild.hchoiceEdgeNew.{u_1, u_2}

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_hnotStrongPrev_5207.{u_1, u_2} :
    SharedFacts.TerminalRebuild.hnotStrongPrevStatement.{u_1, u_2} :=
  SharedFacts.TerminalRebuild.hnotStrongPrev.{u_1, u_2}

theorem helper_hnewAlternativeFails_5223.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
        (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
        (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)),
        (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) choice.selected rho ∧
        ¬Disjoint (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho
        (ett.series.data.tree q.succ.castSucc))) →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev), StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) :
        Finset (Fin k)) choice.selected sigmaPrev →
    ∀ (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hsigmaPrevSelf : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice4049 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf;
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected
        rho ∧ ¬Disjoint (MissingColors G rho newChoice.otherEndpoint) (TreeMissingColors rho
        (ett.series.data.tree q.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q previousProper
      previousOneUncolored choice seriesAlternativeFails sigmaPrev hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ hsigmaPrevEnlarged hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice
  rcases seriesAlternativeFails with
    ⟨rho, hrhoProper, hrhoOne, hrhoStable, hrhoIntersection⟩
  have hreverse : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))
      sigmaPrev choice.selected := by
    exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))).symm
        (x := ⟨choice.selected,
          ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
        (y := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
        hsigmaPrevEnlarged
  have hrhoNew : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))
      sigmaPrev rho := by
    exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data q.castSucc))).trans
        (x := ⟨sigmaPrev, ⟨hsigmaPrevProper, hsigmaPrevOne⟩⟩)
        (y := ⟨choice.selected,
          ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
        (z := ⟨rho, ⟨hrhoProper, hrhoOne⟩⟩)
        hreverse hrhoStable
  refine ⟨rho, hrhoProper, hrhoOne, ?_, ?_⟩
  · simpa [newChoice] using hrhoNew
  · simpa [newChoice] using hrhoIntersection

theorem helper_hchoiceSecond_5266.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), StableColoring (ett.series.data.tree
        q.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc) :
        Finset (Fin k)) choice.selected secondStable → secondStable choice.edge = some
        choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q secondStable choice
      secondStableRelation
  have hfix := secondStableRelation.1 choice.edge
    ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
    ⟨choice.color, Finset.mem_union_right _
      (Finset.mem_insert_self _ _), choice.edgeColor⟩
  exact hfix.trans choice.edgeColor

theorem helper_hgammaDeltaNe_5272.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data
        q.castSucc) (ett.series.data.coloring q.castSucc)), gamma ∈ MissingColors G secondStable
        choice.vertex → secondStable choice.edge = some choice.color → gamma ≠ choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma secondStable choice
      hgammaSecond hchoiceSecond heq
  have hpresent : gamma ∈ PresentColors G secondStable choice.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨choice.edge, choice.edgeIncident, heq ▸ hchoiceSecond⟩
  have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
    simpa [MissingColors] using hgammaSecond
  exact hnot hpresent

theorem helper_hsigmaComponentColor_5296.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (f : E), Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color (Sum.inl choice.vertex)
        → sigma f = some gamma ∨ sigma f = some choice.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ q gamma choice f hf
  exact TwoColorComponent.edge_colors hf

theorem helper_hrootLeaf_5339.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev → gamma ≠
        choice.color → gamma ∈ MissingColors G sigmaPrev choice.vertex →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
        (H.neighborSet (Sum.inl choice.vertex)).Subsingleton := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev
      hsigmaPrevProper hgammaDeltaNe hgammaPrevMissing H
  exact TwoColorMissingVertexNeighborsSubsingleton G sigmaPrev hsigmaPrevProper
    gamma choice.color choice.vertex (Or.inl hgammaPrevMissing)

theorem helper_branch_5387.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (a b : V ⊕ E) (p : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b),
        p.IsPath → {x : V ⊕ E | x ∈ p.support} = TwoColorComponent G sigmaPrev gamma choice.color
        (Sum.inl choice.vertex) → Sum.inl choice.vertex ∈ p.support → Sum.inl choice.vertex = b →
    ∃ (b : V ⊕ E) (p : H.Walk (Sum.inl choice.vertex) b), p.IsPath ∧ {z : V ⊕ E | z ∈ p.support} =
        TwoColorComponent G sigmaPrev gamma choice.color (Sum.inl choice.vertex) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H a b p
      hp hps hrootSupport hb
  subst b
  refine ⟨a, p.reverse, hp.reverse, ?_⟩
  ext z
  change z ∈ p.reverse.support ↔ z ∈
    TwoColorComponent G sigmaPrev gamma choice.color
      (Sum.inl choice.vertex)
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  exact Set.ext_iff.mp hps z

theorem helper_hpNotNil_5395.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color; Sum.inr
        choice.edge ∈ TwoColorComponent G sigmaPrev gamma choice.color (Sum.inl choice.vertex) →
    ∀ (b : V ⊕ E) (p : H.Walk (Sum.inl choice.vertex) b), {z : V ⊕ E | z ∈ p.support} =
        TwoColorComponent G sigmaPrev gamma choice.color (Sum.inl choice.vertex) → ¬p.Nil := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H
      hedgeComponent b p hps hnil
  have hedgeSupport : Sum.inr choice.edge ∈ p.support := by
    change Sum.inr choice.edge ∈ {z | z ∈ p.support}
    rw [hps]
    exact hedgeComponent
  rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] at hedgeSupport
  simp at hedgeSupport

theorem helper_hpNotOne_5434.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), (0 : ℕ) < p.length → p.length ≠ (1
        : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H u p
      hpPos hone
  have hadj := p.adj_getVert_succ (i := 0) (by omega)
  have hend := p.getVert_length
  rw [hone] at hend
  rw [p.getVert_zero, hend] at hadj
  simp [H, TwoColorIncidenceGraph] at hadj

theorem helper_happendTree_5509.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput), zeroPrefix.data.tree (Fin.last (1 : ℕ)) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc →
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q hqSucc gamma
      choice prefixInput zeroPrefix hzeroTree zeroLast newStored newEdges newKind newVertex
      newOutside newDelta newGamma appendedData
  calc
    appendedData.tree zeroLast.succ.castSucc =
        zeroPrefix.data.tree (Fin.last 1) := by
          simp only [appendedData, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
          congr 1
    _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := hzeroTree
    _ = ett.series.data.tree q.succ.castSucc := by rw [hqSucc]

theorem helper_happendColor_5519.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 :
        ℕ) e0 prefixInput), zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev →
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.coloring zeroLast.castSucc = sigmaPrev := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q gamma choice
      sigmaPrev prefixInput zeroPrefix hzeroColor zeroLast newStored newEdges newKind newVertex
      newOutside newDelta newGamma appendedData
  calc
    appendedData.coloring zeroLast.castSucc =
        zeroPrefix.data.coloring (Fin.last 0) := by
          simp only [appendedData, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
          congr 1
    _ = sigmaPrev := hzeroColor

theorem helper_hpeNoRevisitingZero_5543.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (prefixInput : PartialEdgeColoring
        E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0 prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; ¬Nonempty (RevisitingExtensionCertificate appendedData zeroLast.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q gamma choice
      sigmaPrev H u p prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex
      newOutside newDelta newGamma appendedData
  rintro ⟨cert⟩
  obtain ⟨oldCert, -, -, -, -, -⟩ :=
    (RevisitingExtensionCertificateAppend zeroPrefix.data
      closureTree sigma newStored newEdges newKind newVertex
      newOutside newDelta newGamma zeroLast).1 cert
  have hle := oldCert.earlierAtMost
  have hpos := oldCert.earlierPositive
  simp [zeroLast] at hle
  omega

theorem helper_hpeAlternativeZero_5555.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (previousProper : IsProperEdgeColoring G (ett.series.data.coloring
        q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring
        q.castSucc) e0) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (sigmaPrev : PartialEdgeColoring E k)
        (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev) (hsigmaPrevOne : IsOneEdgeUncolored
        sigmaPrev e0) (hsigmaPrevStableQ : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev) (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice4049 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected
        rho ∧ ¬Disjoint (MissingColors G rho newChoice.otherEndpoint) (TreeMissingColors rho
        (ett.series.data.tree q.succ.castSucc))) →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma;
    ∀ (happendTree : appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree
        q.succ.castSucc) (happendColor : appendedData.coloring zeroLast.castSucc = sigmaPrev)
        (happendStored : TashkinovStoredColors appendedData zeroLast.castSucc =
        TashkinovStoredColors ett.series.data q.castSucc),
    let appendedChoice : MaximumDefectiveChoice G e0 (appendedData.tree zeroLast.succ.castSucc)
        (TashkinovStoredColors appendedData zeroLast.castSucc) (appendedData.coloring
        zeroLast.castSucc) := helperAppendedChoice4500 G k e0 input T generating ett hpositive
        sigma closureTree gamma previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf prefixInput zeroPrefix happendTree happendColor happendStored;
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (appendedData.tree zeroLast.succ.castSucc) (insert appendedChoice.color
        (TashkinovStoredColors appendedData zeroLast.castSucc) : Finset (Fin k))
        appendedChoice.selected rho ∧ ¬Disjoint (MissingColors G rho appendedChoice.otherEndpoint)
        (TreeMissingColors rho (appendedData.tree zeroLast.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma closureTree q gamma previousProper
      previousOneUncolored choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice hnewAlternativeFails prefixInput
      zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendTree happendColor happendStored appendedChoice
  rcases hnewAlternativeFails with
    ⟨rho, hrhoProper, hrhoOne, hrhoStable, hrhoNotDisjoint⟩
  refine ⟨rho, hrhoProper, hrhoOne, ?_, ?_⟩
  · change StableColoring
      (appendedData.tree zeroLast.succ.castSucc)
      (insert choice.color
        (TashkinovStoredColors appendedData zeroLast.castSucc))
      sigmaPrev rho
    rw [happendTree, happendStored]
    simpa [appendedChoice, newChoice] using hrhoStable
  · change ¬ Disjoint (MissingColors G rho choice.otherEndpoint)
      (TreeMissingColors rho
        (appendedData.tree zeroLast.succ.castSucc))
    rw [happendTree]
    simpa [appendedChoice, newChoice] using hrhoNotDisjoint

theorem helper_hpeGammaRuleZero_5579.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (previousProper : IsProperEdgeColoring G (ett.series.data.coloring
        q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring
        q.castSucc) e0) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (sigmaPrev : PartialEdgeColoring E k)
        (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev) (hsigmaPrevOne : IsOneEdgeUncolored
        sigmaPrev e0) (hsigmaPrevStableQ : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev) (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let _ : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice4049 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; gamma ∈ MissingColors G sigmaPrev choice.vertex →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (prefixInput : PartialEdgeColoring
        E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0 prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma;
    ∀ (happendTree : appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree
        q.succ.castSucc) (happendColor : appendedData.coloring zeroLast.castSucc = sigmaPrev)
        (happendStored : TashkinovStoredColors appendedData zeroLast.castSucc =
        TashkinovStoredColors ett.series.data q.castSucc),
    let appendedChoice : MaximumDefectiveChoice G e0 (appendedData.tree zeroLast.succ.castSucc)
        (TashkinovStoredColors appendedData zeroLast.castSucc) (appendedData.coloring
        zeroLast.castSucc) := helperAppendedChoice4500 G k e0 input T generating ett hpositive
        sigma closureTree gamma previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf prefixInput zeroPrefix happendTree happendColor happendStored;
        ParallelExtensionColor appendedData zeroLast.castSucc appendedChoice.selected
        appendedChoice.vertex gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma closureTree q gamma previousProper
      previousOneUncolored choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice hgammaPrevMissing H u p prefixInput
      zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendTree happendColor happendStored appendedChoice
  rw [ParallelExtensionColorAppend zeroPrefix.data closureTree sigma
    newStored newEdges newKind newVertex newOutside newDelta newGamma
    zeroLast appendedChoice.selected appendedChoice.vertex gamma]
  refine ⟨?_, Or.inr ?_⟩
  · simpa [appendedChoice, newChoice] using hgammaPrevMissing
  · intro h hhPositive hhAtMost hhPE
    simp [zeroLast] at hhAtMost
    omega

theorem helper_lastStep_5593.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
    ∀ (closureTree : TreeSequence G e0), TreeSequenceInitialSegment (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) closureTree →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (_ : PartialEdgeColoring E k) (previousProper : IsProperEdgeColoring G
        (ett.series.data.coloring q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored
        (ett.series.data.coloring q.castSucc) e0) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)) (sigmaPrev : PartialEdgeColoring E k)
        (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev) (hsigmaPrevOne : IsOneEdgeUncolored
        sigmaPrev e0) (hsigmaPrevStableQ : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev) (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
        ColoredVertexSetClosed G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) → sigma = TwoColorComponentSwap G sigmaPrev gamma
        choice.color (Sum.inl choice.vertex) → TreeExit (ett.series.data.tree q.succ.castSucc)
        sigmaPrev gamma choice.color choice.vertex →
    ∀ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput), TashkinovClosure sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        closureTree →
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree (Fin.last (2 : ℕ)) = closureTree → appendedData.coloring
        (Fin.last (1 : ℕ)) = sigma → appendedData.stored (Fin.last (1 : ℕ)) = newStored →
        appendedData.connectingEdges (Fin.last (1 : ℕ)) = newEdges → appendedData.kind (Fin.last
        (1 : ℕ)) = newKind → appendedData.chosenVertex (Fin.last (1 : ℕ)) = newVertex →
        appendedData.outsideVertex (Fin.last (1 : ℕ)) = newOutside → appendedData.delta (Fin.last
        (1 : ℕ)) = newDelta → appendedData.gamma (Fin.last (1 : ℕ)) = newGamma →
    ∀ (happendTree : appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree
        q.succ.castSucc) (happendColor : appendedData.coloring zeroLast.castSucc = sigmaPrev)
        (happendStored : TashkinovStoredColors appendedData zeroLast.castSucc =
        TashkinovStoredColors ett.series.data q.castSucc),
    let appendedChoice : MaximumDefectiveChoice G e0 (appendedData.tree zeroLast.succ.castSucc)
        (TashkinovStoredColors appendedData zeroLast.castSucc) (appendedData.coloring
        zeroLast.castSucc) := helperAppendedChoice4500 G k e0 input T generating ett hpositive
        sigma closureTree gamma previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf prefixInput zeroPrefix happendTree happendColor happendStored; ¬Nonempty
        (RevisitingExtensionCertificate appendedData zeroLast.castSucc) → (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (appendedData.tree zeroLast.succ.castSucc) (insert appendedChoice.color
        (TashkinovStoredColors appendedData zeroLast.castSucc) : Finset (Fin k))
        appendedChoice.selected rho ∧ ¬Disjoint (MissingColors G rho appendedChoice.otherEndpoint)
        (TreeMissingColors rho (appendedData.tree zeroLast.succ.castSucc))) →
        ParallelExtensionColor appendedData zeroLast.castSucc appendedChoice.selected
        appendedChoice.vertex gamma → (ett.series.data.tree (Fin.last ett.rounds).castSucc).length
        < closureTree.length → TashkinovSeriesStep G k (1 : ℕ) e0 prefixInput appendedData
        (Fin.last (1 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne closureTree
      hTnClosure q hqSucc gamma secondStable previousProper previousOneUncolored choice sigmaPrev
      hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
      hsigmaPrevSelf hclosedPrev hnotStrongPrev hsigmaRecovered hnewExit prefixInput zeroPrefix
      hterminalClosure zeroLast newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendLastTree happendLastColor happendLastStored happendLastEdges
      happendLastKind happendLastVertex happendLastOutside happendLastDelta happendLastGamma
      happendTree happendColor happendStored appendedChoice hpeNoRevisitingZero hpeAlternativeZero
      hpeGammaRuleZero hstrictClosure
  have hlast : zeroLast.succ = Fin.last 1 := by
    apply Fin.ext
    rfl
  rw [← hlast]
  apply TashkinovSeriesStep.PE (i := zeroLast)
    (choice := appendedChoice) (gamma := gamma)
    (secondStable := sigmaPrev)
  · rw [happendColor]; exact hsigmaPrevProper
  · rw [happendColor]; exact hsigmaPrevOne
  · rw [happendColor, happendTree]; exact hclosedPrev
  · rw [happendColor, happendTree]; exact hnotStrongPrev
  · exact hpeNoRevisitingZero
  · exact hpeAlternativeZero
  · exact hpeGammaRuleZero
  · exact hsigmaPrevProper
  · exact hsigmaPrevOne
  · exact (sc2 G e0
      (appendedData.tree zeroLast.succ.castSucc)
      (insert appendedChoice.color
        (TashkinovStoredColors appendedData zeroLast.castSucc))).refl
      ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne⟩
  · change TreeExit (appendedData.tree zeroLast.succ.castSucc)
      sigmaPrev gamma choice.color choice.vertex
    rw [happendTree]
    exact hnewExit
  · exact happendLastColor.trans hsigmaRecovered
  · rw [hlast, happendLastColor]
    exact hsigmaProper
  · rw [hlast, happendLastColor]
    exact hsigmaOne
  · exact happendLastStored.trans (by rfl)
  · exact happendLastEdges.trans (by rfl)
  · exact happendLastKind.trans (by rfl)
  · exact happendLastVertex.trans (by rfl)
  · exact happendLastOutside.trans (by rfl)
  · exact happendLastDelta.trans (by rfl)
  · exact happendLastGamma.trans (by rfl)
  · change TashkinovClosure
      (appendedData.coloring (Fin.last 1))
      (appendedData.tree zeroLast.succ.castSucc)
      (appendedData.tree (Fin.last 2))
    rw [happendLastColor, happendTree, happendLastTree]
    simpa [hqSucc] using hterminalClosure
  · change TreeSequenceInitialSegment
      (appendedData.tree zeroLast.succ.castSucc)
      (appendedData.tree (Fin.last 2))
    rw [happendTree]
    rw [happendLastTree]
    simpa [hqSucc] using hTnClosure
  · change (appendedData.tree zeroLast.succ.castSucc).length <
      (appendedData.tree (Fin.last 2)).length
    rw [happendTree]
    rw [happendLastTree]
    simpa [hqSucc] using hstrictClosure

theorem helper_hpenultimateTree_5732.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (prefixInput : PartialEdgeColoring
        E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0 prefixInput),
    let zeroLast : Fin ((0 : ℕ) + (1 : ℕ)) := Fin.last (0 : ℕ);
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k ((0 : ℕ) + (1 : ℕ)) e0 := TashkinovSeriesDataAppend
        zeroPrefix.data closureTree sigma newStored newEdges newKind newVertex newOutside newDelta
        newGamma; appendedData.tree zeroLast.succ.castSucc = ett.series.data.tree q.succ.castSucc
        →
    ∀ (extendedSeries : TashkinovSeries G k ((0 : ℕ) + (1 : ℕ)) e0 prefixInput),
        extendedSeries.data = TashkinovSeriesDataAppend zeroPrefix.data closureTree sigma
        newStored newEdges newKind newVertex newOutside newDelta newGamma →
    ∀ (hroundsEq : (0 : ℕ) + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 prefixInput → TashkinovSeries G
        k b e0 prefixInput := fun {a b} (h : a = b) series => series.castRounds h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + (2 : ℕ))),
        (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput := castSeries hroundsEq
        extendedSeries;
    let rawTreeIndex : Fin (ett.rounds + (2 : ℕ)) → Fin (3 : ℕ) := fun (i : Fin (ett.rounds + (2 :
        ℕ))) ↦ Fin.cast (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) i; rawTreeIndex (⟨ett.rounds,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = zeroLast.succ.castSucc → finalSeries.data.tree (⟨ett.rounds,
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma Tstar closureTree q hqSucc gamma
      choice sigmaPrev H u p prefixInput zeroPrefix zeroLast newStored newEdges newKind newVertex
      newOutside newDelta newGamma appendedData happendTree extendedSeries hextendedData
      hroundsEq castSeries castSeriesTree finalSeries rawTreeIndex hrawPenultimate
  exact @helper_hpenultimateTree_3400 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@sigma) (@Tstar) (@closureTree) (@hqSucc) (@gamma) (@choice) (@sigmaPrev) (@u)
      (@p) (@prefixInput) (@zeroPrefix) (@happendTree) (@extendedSeries)
      (@hextendedData) (@hroundsEq) (@castSeriesTree) (@hrawPenultimate)

alias helper_hseriesTreeAgree_5768 := helper_hseriesTreeAgree_3561

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_branch_5820.{u_1, u_2} :
    SharedFacts.TerminalRebuildTransport.branchStatement.{u_1, u_2} :=
  SharedFacts.TerminalRebuildTransport.branch.{u_1, u_2}

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_hreplacementCurrentTree_5844.{u_1, u_2} :
    SharedFacts.TerminalRebuild.hreplacementCurrentTreeStatement.{u_1, u_2} :=
  SharedFacts.TerminalRebuild.hreplacementCurrentTree.{u_1, u_2}

theorem helper_horiginalCurrentTree_5852.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) →
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        (0 : ℕ) < originalPrefix.rounds → originalPrefix.series.data.tree replacementLast.castSucc
        = ett.series.data.tree q.castSucc.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H u p
      hroundLarge originalPrefix hr hprefixTrees replacementLast horiginalPositive
  calc
    originalPrefix.series.data.tree replacementLast.castSucc =
        ett.series.data.tree
          (Fin.castLE (by omega) replacementLast.castSucc) :=
      hprefixTrees replacementLast.castSucc
    _ = ett.series.data.tree q.castSucc.castSucc := by
      congr 1
      apply Fin.ext
      simp [replacementLast, q, hr]

theorem helper_htreeMissingEq_5864.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (originalPrefix :
        ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (horiginalPositive : (0 : ℕ) < originalPrefix.rounds),
    let previousReplacement : Fin originalPrefix.rounds := (⟨originalPrefix.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin originalPrefix.rounds); previousReplacement.succ = replacementLast → TreeMissingColors
        (corr.replacementSeries.data.coloring replacementLast) (corr.replacementSeries.data.tree
        replacementLast.castSucc) = TreeMissingColors (originalPrefix.series.data.coloring
        replacementLast) (originalPrefix.series.data.tree replacementLast.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H u p
      originalPrefix corr replacementLast horiginalPositive previousReplacement hpreviousSucc
  have hstable := corr.replacementStable previousReplacement
  rw [hpreviousSucc] at hstable
  have htree := corr.ladderTreesAgree previousReplacement
  rw [hpreviousSucc] at htree
  rw [htree]
  ext c
  simp only [TreeMissingColors, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv, hc⟩
    exact ⟨v, hv, (hstable.2 v hv).symm ▸ hc⟩
  · rintro ⟨v, hv, hc⟩
    exact ⟨v, hv, hstable.2 v hv ▸ hc⟩

theorem helper_hreplacementStored_5882.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (_ : (0 : ℕ) < originalPrefix.rounds), Fin.castLE (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) replacementLast = q.castSucc → TreeMissingColors (corr.replacementSeries.data.coloring
        replacementLast) (corr.replacementSeries.data.tree replacementLast.castSucc) =
        TreeMissingColors (originalPrefix.series.data.coloring replacementLast)
        (originalPrefix.series.data.tree replacementLast.castSucc) → TashkinovStoredColors
        corr.replacementSeries.data replacementLast = TashkinovStoredColors ett.series.data
        q.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H u p
      hroundLarge originalPrefix hr hprefixData corr replacementLast horiginalPositive hlastMap
      htreeMissingEq
  have hcorrStored : TashkinovStoredColors
        corr.replacementSeries.data replacementLast =
      TashkinovStoredColors originalPrefix.series.data
        replacementLast := by
    unfold TashkinovStoredColors
    have hnonzero : replacementLast.val ≠ 0 := by
      simp only [Fin.val_last, ne_eq, replacementLast]
      exact Nat.ne_of_gt horiginalPositive
    rw [ite_eq_right hnonzero, ite_eq_right hnonzero]
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨j, hj, hc⟩, hn⟩
      refine ⟨⟨j, hj, ?_⟩, ?_⟩
      · by_cases hle : j.val ≤ replacementLast.val
        · simp only [ite_eq_left hle] at hc ⊢
          simpa [corr.storedColorsAgree j] using hc
        · simp only [ite_eq_right hle] at hc ⊢
          exact hc
      · rw [htreeMissingEq] at hn
        exact hn
    · rintro ⟨⟨j, hj, hc⟩, hn⟩
      refine ⟨⟨j, hj, ?_⟩, ?_⟩
      · by_cases hle : j.val ≤ replacementLast.val
        · simp only [ite_eq_left hle] at hc ⊢
          simpa [corr.storedColorsAgree j] using hc
        · simp only [ite_eq_right hle] at hc ⊢
          exact hc
      · rw [← htreeMissingEq] at hn
        exact hn
  calc
    TashkinovStoredColors corr.replacementSeries.data replacementLast =
        TashkinovStoredColors originalPrefix.series.data
          replacementLast := hcorrStored
    _ = TashkinovStoredColors ett.series.data
          (Fin.castLE (by omega) replacementLast) :=
      (hprefixData replacementLast).2.2.2.2
    _ = TashkinovStoredColors ett.series.data q.castSucc := by
      rw [hlastMap]

theorem helper_hnoRevisitingReplacement_5934.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k), IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) →
        IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 → ¬Nonempty
        (RevisitingExtensionCertificate ett.series.data q.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaPrev →
        IsOneEdgeUncolored sigmaPrev e0 → StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc)
        sigmaPrev →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), p.IsPath → (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)),
        MaximumProperty originalPrefix → (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) → (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)), corr.replacementSeries.data.tree
        (Fin.last (originalPrefix.rounds + (1 : ℕ))) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc → corr.replacementSeries.data.coloring (Fin.last
        originalPrefix.rounds) = sigmaPrev → MaximumProperty corr.replacementETT →
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        ¬Nonempty (RevisitingExtensionCertificate corr.replacementSeries.data replacementLast) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower _ q gamma previousProper
      previousOneUncolored noRevisiting choice sigmaPrev hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ H u p hp hroundLarge originalPrefix hr hprefixMP hprefixTrees hprefixData
      corr hcorrFinalTree hcorrFinalColor hcorrMP replacementLast
  exact P2971_T1_PositivePrefixNoRevisiting G k e0 input T generating
    ett hMP hroundLarge
    (fun lower hp hl hm =>
      ⟨(hlower lower hp hl hm).2.1,
        (hlower lower hp hl hm).2.2.2.1⟩)
    sigmaPrev hsigmaPrevProper hsigmaPrevOne previousProper
    previousOneUncolored hsigmaPrevStableQ originalPrefix hr
    hprefixMP hprefixTrees hprefixData corr hcorrFinalTree
    hcorrFinalColor hcorrMP noRevisiting

theorem helper_hpeAlternativeReplacement_5946.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) ,
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (previousProper : IsProperEdgeColoring G (ett.series.data.coloring q.castSucc))
        (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0)
        (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G
        sigmaPrev) (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ :
        StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc) sigmaPrev)
        (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈
        BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice4049 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected
        rho ∧ ¬Disjoint (MissingColors G rho newChoice.otherEndpoint) (TreeMissingColors rho
        (ett.series.data.tree q.succ.castSucc))) →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc))
        (hcorrFinalColor : corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) =
        sigmaPrev),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (hreplacementCurrentTree : corr.replacementSeries.data.tree replacementLast.succ =
        ett.series.data.tree q.succ.castSucc) (hreplacementStored : TashkinovStoredColors
        corr.replacementSeries.data replacementLast = TashkinovStoredColors ett.series.data
        q.castSucc),
    let replacementChoice : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        replacementLast.succ) (TashkinovStoredColors corr.replacementSeries.data replacementLast)
        (corr.replacementSeries.data.coloring replacementLast) := helperReplacementChoice5196 G k
        e0 input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf originalPrefix corr hcorrFinalColor hreplacementCurrentTree
        hreplacementStored;
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (corr.replacementSeries.data.tree replacementLast.succ) (insert
        replacementChoice.color (TashkinovStoredColors corr.replacementSeries.data
        replacementLast) : Finset (Fin k)) replacementChoice.selected rho ∧ ¬Disjoint
        (MissingColors G rho replacementChoice.otherEndpoint) (TreeMissingColors rho
        (corr.replacementSeries.data.tree replacementLast.succ)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive q previousProper previousOneUncolored
      choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf newChoice hnewAlternativeFails originalPrefix corr
      hcorrFinalColor replacementLast hreplacementCurrentTree hreplacementStored replacementChoice
  rcases hnewAlternativeFails with
    ⟨rho, hrhoProper, hrhoOne, hrhoStable, hrhoNotDisjoint⟩
  refine ⟨rho, hrhoProper, hrhoOne, ?_, ?_⟩
  · change StableColoring
      (corr.replacementSeries.data.tree replacementLast.succ)
      (insert choice.color
        (TashkinovStoredColors corr.replacementSeries.data
          replacementLast)) sigmaPrev rho
    rw [hreplacementCurrentTree, hreplacementStored]
    simpa [replacementChoice, newChoice] using hrhoStable
  · change ¬ Disjoint (MissingColors G rho choice.otherEndpoint)
      (TreeMissingColors rho
        (corr.replacementSeries.data.tree replacementLast.succ))
    rw [hreplacementCurrentTree]
    simpa [replacementChoice, newChoice] using hrhoNotDisjoint

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_hne_6004.{u_1, u_2} :
    SharedFacts.RevisitingTerminalPreparation.hneStatement.{u_1, u_2} :=
  SharedFacts.RevisitingTerminalPreparation.hne.{u_1, u_2}

theorem helper_hindexMap_6123.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (_ :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : (0 : ℕ) < originalPrefix.rounds) (j : Fin
        (originalPrefix.rounds + (1 : ℕ))),
    let fullj : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) j;
    ∀ (fulli : Fin ett.rounds), fulli.succ = fullj →
    ∀ (newi : Fin originalPrefix.rounds), j = newi.succ → newi.succ = j → Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) newi.succ = fulli.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H u p
      hroundLarge originalPrefix hr corr horiginalPositive j fullj fulli hfullIndex newi
      hnewTarget hnewIndex
  apply Fin.ext
  have hf := congrArg Fin.val hfullIndex
  have hn := congrArg Fin.val hnewIndex
  simp [fullj] at hf hn ⊢
  omega

theorem helper_htree_6130.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : (0 : ℕ) <
        originalPrefix.rounds) (j : Fin (originalPrefix.rounds + (1 : ℕ))),
    let fullj : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) j;
    ∀ (fulli : Fin ett.rounds), fulli.succ = fullj →
    ∀ (newi : Fin originalPrefix.rounds), j = newi.succ → newi.succ = j →
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        fulli.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H u p
      hroundLarge originalPrefix hr hprefixTrees corr horiginalPositive j fullj fulli hfullIndex
      newi hnewTarget hnewIndex
  calc
    corr.replacementSeries.data.tree newi.succ.castSucc =
        originalPrefix.series.data.tree
          newi.succ.castSucc := corr.ladderTreesAgree newi
    _ = ett.series.data.tree
          (Fin.castLE (by omega) newi.succ.castSucc) :=
      hprefixTrees newi.succ.castSucc
    _ = ett.series.data.tree fulli.succ.castSucc := by
      congr 1
      apply Fin.ext
      have hf := congrArg Fin.val hfullIndex
      have hn := congrArg Fin.val hnewIndex
      simp [fullj] at hf hn ⊢
      omega

theorem helper_hprefixPostFull_6259.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : (0 : ℕ) <
        originalPrefix.rounds) (j : Fin (originalPrefix.rounds + (1 : ℕ))),
    let fullj : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) j;
    ∀ (fulli : Fin ett.rounds) (_ : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)), fullj = fulli.succ →
    ∀ (newi : Fin originalPrefix.rounds), newi.succ = j → corr.replacementSeries.data.tree
        newi.succ.castSucc = ett.series.data.tree fulli.succ.castSucc →
        originalPrefix.series.data.coloring newi.succ = ett.series.data.coloring fulli.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev H u p
      hroundLarge originalPrefix hr hprefixData corr horiginalPositive j fullj fulli fullChoice
      hfullTarget newi hnewIndex htree
  calc
    originalPrefix.series.data.coloring newi.succ =
        originalPrefix.series.data.coloring j := by
      rw [hnewIndex]
    _ = ett.series.data.coloring
          (Fin.castLE (by omega) j) :=
      (hprefixData j).1
    _ = ett.series.data.coloring fulli.succ := by
      congr 1

theorem helper_branch_6368.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) ,
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (previousProper : IsProperEdgeColoring G (ett.series.data.coloring
        q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring
        q.castSucc) e0) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), ParallelExtensionColor ett.series.data q.castSucc
        choice.selected choice.vertex gamma →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev) (hchoiceDefective : DefectiveColor G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        sigmaPrev sigmaPrev),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (hcorrFinalColor : corr.replacementSeries.data.coloring
        (Fin.last originalPrefix.rounds) = sigmaPrev),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
    ∀ (_ : (0 : ℕ) < originalPrefix.rounds) (hreplacementCurrentTree :
        corr.replacementSeries.data.tree replacementLast.succ = ett.series.data.tree
        q.succ.castSucc) (hreplacementStored : TashkinovStoredColors corr.replacementSeries.data
        replacementLast = TashkinovStoredColors ett.series.data q.castSucc),
    let replacementChoice : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        replacementLast.succ) (TashkinovStoredColors corr.replacementSeries.data replacementLast)
        (corr.replacementSeries.data.coloring replacementLast) := helperReplacementChoice5196 G k
        e0 input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf originalPrefix corr hcorrFinalColor hreplacementCurrentTree
        hreplacementStored; (
    ∀ (j : Fin (originalPrefix.rounds + (1 : ℕ))), corr.replacementSeries.data.kind j =
        ett.series.data.kind (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) j)) → (
    ∀ (j : Fin (originalPrefix.rounds + (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) →
        corr.replacementSeries.data.kind j = some TashkinovExtensionKind.PE →
        corr.replacementSeries.data.chosenVertex j = ett.series.data.chosenVertex (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) j) ∧ corr.replacementSeries.data.delta j = ett.series.data.delta (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) j) ∧ corr.replacementSeries.data.gamma j = ett.series.data.gamma (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) j)) → (
    ∃ (h : Fin (originalPrefix.rounds + (1 : ℕ))), (0 : ℕ) < (↑h : ℕ) ∧ (↑h : ℕ) ≤
        (↑replacementLast : ℕ) ∧ corr.replacementSeries.data.kind h = some
        TashkinovExtensionKind.PE ∧ corr.replacementSeries.data.chosenVertex h = some
        replacementChoice.vertex ∧ corr.replacementSeries.data.delta h = some gamma ∧
    ∀ (j : Fin (originalPrefix.rounds + (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) → (↑j : ℕ) ≤
        (↑replacementLast : ℕ) → corr.replacementSeries.data.kind j = some
        TashkinovExtensionKind.PE → corr.replacementSeries.data.chosenVertex j = some
        replacementChoice.vertex → (↑j : ℕ) ≤ (↑h : ℕ)) ∨
    ∀ (h : Fin (originalPrefix.rounds + (1 : ℕ))), (0 : ℕ) < (↑h : ℕ) → (↑h : ℕ) ≤
        (↑replacementLast : ℕ) → corr.replacementSeries.data.kind h = some
        TashkinovExtensionKind.PE → corr.replacementSeries.data.chosenVertex h ≠ some
        replacementChoice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive q gamma previousProper
      previousOneUncolored choice gammaRule sigmaPrev hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf H u p hroundLarge
      originalPrefix hr corr hcorrFinalColor replacementLast horiginalPositive
      hreplacementCurrentTree hreplacementStored replacementChoice retainedKind retainedPEFields
  rcases gammaRule.2 with history | noHistory
  · rcases history with
      ⟨h, hhPositive, hhAtMost, hhPE, hhVertex, hhDelta, hhMax⟩
    let j : Fin (originalPrefix.rounds + 1) :=
      ⟨h.val, by
        have hb := h.isLt
        simp [hr, q] at hhAtMost ⊢
        omega⟩
    have hjFull : Fin.castLE (by omega) j = h := by
      apply Fin.ext
      rfl
    have hjPE : corr.replacementSeries.data.kind j =
        some TashkinovExtensionKind.PE := by
      rw [retainedKind j, hjFull]
      exact hhPE
    have hfields := retainedPEFields j hhPositive hjPE
    refine Or.inl ⟨j, hhPositive, ?_, hjPE, ?_, ?_, ?_⟩
    · simp [j, replacementLast, q, hr] at hhAtMost ⊢
      omega
    · rw [hfields.1, hjFull]
      exact hhVertex
    · rw [hfields.2.1, hjFull]
      exact hhDelta
    · intro r hrPositive hrAtMost hrPE hrVertex
      let fullr : Fin (ett.rounds + 1) := Fin.castLE (by omega) r
      have hrFields := retainedPEFields r hrPositive hrPE
      apply hhMax fullr
      · exact hrPositive
      · simp [fullr, replacementLast, q, hr] at hrAtMost ⊢
        omega
      · simpa [fullr] using (retainedKind r).symm.trans hrPE
      · simpa [fullr, replacementChoice] using
          hrFields.1.symm.trans hrVertex
  · refine Or.inr ?_
    intro j hjPositive hjAtMost hjPE hjVertex
    let fullj : Fin (ett.rounds + 1) := Fin.castLE (by omega) j
    have hfields := retainedPEFields j hjPositive hjPE
    apply noHistory fullj hjPositive
    · simp [fullj, replacementLast, q, hr] at hjAtMost ⊢
      omega
    · simpa [fullj] using (retainedKind j).symm.trans hjPE
    · simpa [fullj, replacementChoice] using
        hfields.1.symm.trans hjVertex

theorem helper_hnoRevisitingAppended_6477.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        ¬Nonempty (RevisitingExtensionCertificate corr.replacementSeries.data replacementLast) →
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let appendedData : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
        newKind newVertex newOutside newDelta newGamma; ¬Nonempty (RevisitingExtensionCertificate
        appendedData replacementLast.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q gamma choice
      sigmaPrev originalPrefix corr replacementLast hnoRevisitingReplacement newStored newEdges
      newKind newVertex newOutside newDelta newGamma appendedData
  rintro ⟨cert⟩
  obtain ⟨oldCert, -, -, -, -, -⟩ :=
    (RevisitingExtensionCertificateAppend
      corr.replacementSeries.data closureTree sigma newStored
      newEdges newKind newVertex newOutside newDelta newGamma
      replacementLast).1 cert
  exact hnoRevisitingReplacement ⟨oldCert⟩

private theorem helper_branch_5283.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) < ett.rounds) (originalPrefix
        : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (_ :
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
                  omega
    ) i)) (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)),
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let _ : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
        newKind newVertex newOutside newDelta newGamma;
    ∀ (extendedSeries : TashkinovSeries G k (originalPrefix.rounds + (1 : ℕ)) e0
        corr.replacementInput) (_ : extendedSeries.data = TashkinovSeriesDataAppend
        corr.replacementSeries.data closureTree sigma newStored newEdges newKind newVertex
        newOutside newDelta newGamma) (hroundsEq : originalPrefix.rounds + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 corr.replacementInput →
        TashkinovSeries G k b e0 corr.replacementInput := fun {a b : ℕ} (h : a = b) (S :
        TashkinovSeries G k a e0 corr.replacementInput) ↦ S.castRounds h;
    ∀ (_ :
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (2
        : ℕ))), (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by
                  omega
    ) i)),
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries;
    let _ : Fin (ett.rounds + (2 : ℕ)) → Fin (originalPrefix.rounds + (3 : ℕ)) := fun (i : Fin
        (ett.rounds + (2 : ℕ))) ↦ Fin.cast (
    by
          omega
    ) i;
    ∀ (i : Fin ett.rounds) (_ : (↑i : ℕ) < originalPrefix.rounds), finalSeries.data.tree
        i.succ.castSucc = ett.series.data.tree i.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma closureTree q gamma choice
      sigmaPrev hroundLarge originalPrefix hr hprefixTrees corr newStored newEdges newKind
      newVertex newOutside newDelta newGamma appendedData extendedSeries hextendedData hroundsEq
      castSeries castSeriesTree finalSeries rawTreeIndex i hi
  let j : Fin originalPrefix.rounds := ⟨i.val, hi⟩
  have hraw : rawTreeIndex i.succ.castSucc =
      j.succ.castSucc.castSucc := by
    apply Fin.ext
    rfl
  have hmap : Fin.castLE (by omega) j.succ.castSucc =
      i.succ.castSucc := by
    apply Fin.ext
    rfl
  calc
    finalSeries.data.tree i.succ.castSucc =
        extendedSeries.data.tree
          (rawTreeIndex i.succ.castSucc) := by
          exact castSeriesTree hroundsEq extendedSeries _
    _ = appendedData.tree
          (rawTreeIndex i.succ.castSucc) := by
          rw [hextendedData]
    _ = corr.replacementSeries.data.tree
          j.succ.castSucc := by
          rw [hraw]
          simp only [appendedData,
            TashkinovSeriesDataAppend]
          convert (Fin.lastCases_castSucc
            j.succ.castSucc) using 1
    _ = originalPrefix.series.data.tree
          j.succ.castSucc := corr.ladderTreesAgree j
    _ = ett.series.data.tree
          (Fin.castLE (by omega) j.succ.castSucc) :=
          hprefixTrees j.succ.castSucc
    _ = ett.series.data.tree i.succ.castSucc := by rw [hmap]

private theorem helper_branch_5314.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (extendedSeries : TashkinovSeries G k
        (originalPrefix.rounds + (1 : ℕ)) e0 corr.replacementInput) (hroundsEq :
        originalPrefix.rounds + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 corr.replacementInput →
        TashkinovSeries G k b e0 corr.replacementInput := fun {a b : ℕ} (h : a = b) (S :
        TashkinovSeries G k a e0 corr.replacementInput) ↦ S.castRounds h;
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries;
    ∀ (_ : finalSeries.data.tree (⟨ett.rounds,
    by
                omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc) (i :
        Fin ett.rounds) (_ : ¬(↑i : ℕ) < originalPrefix.rounds), finalSeries.data.tree
        i.succ.castSucc = ett.series.data.tree i.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigmaPrev hroundLarge originalPrefix hr corr
      extendedSeries hroundsEq castSeries finalSeries hfinalPenultimateTree i hi
  let ilast : Fin ett.rounds :=
    ⟨ett.rounds - 1, by omega⟩
  have hilast : i = ilast := by
    apply Fin.ext
    have hiBound := i.isLt
    have hprefixRounds := hr
    simp [ilast]
    omega
  rw [hilast]
  have hindex :
      ilast.succ.castSucc =
        (Fin.last ett.rounds).castSucc := by
    apply Fin.ext
    simp [ilast]
    omega
  rw [hindex]
  exact hfinalPenultimateTree

theorem helper_hseriesTreeAgree_6867.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k) (_ closureTree : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (_ : (0 : ℕ) <
        originalPrefix.rounds),
    let newStored : Finset (Fin k) := (insert choice.color ({ gamma } : Finset (Fin k)) : Finset
        (Fin k));
    let newEdges : Finset E := ({ choice.edge } : Finset E);
    let newKind : Option TashkinovExtensionKind := some TashkinovExtensionKind.PE;
    let newVertex : Option V := some choice.vertex;
    let newOutside : Option V := some choice.otherEndpoint;
    let newDelta : Option (Fin k) := some choice.color;
    let newGamma : Option (Fin k) := some gamma;
    let _ : TashkinovSeriesData G k (originalPrefix.rounds + (1 : ℕ)) e0 :=
        TashkinovSeriesDataAppend corr.replacementSeries.data closureTree sigma newStored newEdges
        newKind newVertex newOutside newDelta newGamma;
    ∀ (extendedSeries : TashkinovSeries G k (originalPrefix.rounds + (1 : ℕ)) e0
        corr.replacementInput), extendedSeries.data = TashkinovSeriesDataAppend
        corr.replacementSeries.data closureTree sigma newStored newEdges newKind newVertex
        newOutside newDelta newGamma →
    ∀ (hroundsEq : originalPrefix.rounds + (1 : ℕ) = ett.rounds),
    let castSeries : {a b : ℕ} → a = b → TashkinovSeries G k a e0 corr.replacementInput →
        TashkinovSeries G k b e0 corr.replacementInput :=
          fun {a b} (h : a = b) series => series.castRounds h; (
    ∀ {a b : ℕ} (h : a = b) (S : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (2
        : ℕ))), (castSeries h S).data.tree i = S.data.tree (Fin.cast (
    by omega
    ) i)) →
    let finalSeries : TashkinovSeries G k ett.rounds e0 corr.replacementInput := castSeries
        hroundsEq extendedSeries; finalSeries.data.tree (⟨ett.rounds,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) = ett.series.data.tree (Fin.last ett.rounds).castSucc →
    let _ : Fin (ett.rounds + (2 : ℕ)) → Fin (originalPrefix.rounds + (3 : ℕ)) := fun (i : Fin
        (ett.rounds + (2 : ℕ))) ↦ Fin.cast (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) i;
    ∀ (i : Fin ett.rounds), finalSeries.data.tree i.succ.castSucc = ett.series.data.tree
        i.succ.castSucc := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma _ closureTree q gamma choice
      sigmaPrev H u p hroundLarge originalPrefix hr hprefixTrees corr horiginalPositive newStored
      newEdges newKind newVertex newOutside newDelta newGamma appendedData extendedSeries
      hextendedData hroundsEq castSeries castSeriesTree finalSeries hfinalPenultimateTree
      rawTreeIndex i
  by_cases hi : i.val < originalPrefix.rounds
  · apply helper_branch_5283 <;> assumption
  · apply helper_branch_5314 <;> assumption

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_branch_7068.{u_1, u_2} :
    SharedFacts.TerminalRebuildTransport.branchStatement.{u_1, u_2} :=
  SharedFacts.TerminalRebuildTransport.branch.{u_1, u_2}

private theorem helper_continuation_4951.{u_1, u_2} :
    helperContinuation4951Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hTstarClosure q hqSucc choice currentStored
      currentEdges currentKind sigmaPrev hsigmaPrevProper hsigmaPrevOne hroundOne prefixInput
      zeroPrefix zeroLast newStored newEdges newKind newVertex newOutside newDelta newGamma
      appendedData happendLastTree happendLastColor happendLastStored happendLastEdges
      happendLastKind happendTree happendColor extendedSeries hextendedData hroundsEq castSeries
      castSeriesTree castSeriesColoring castSeriesStored castSeriesEdges
  let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput :=
    castSeries hroundsEq extendedSeries
  have hfinalTree : finalSeries.data.tree (Fin.last (ett.rounds + 1)) = closureTree := by
    change (extendedSeries.castRounds hroundsEq).data.tree (Fin.last (ett.rounds + 1)) = closureTree
    rw [TashkinovSeries.castRounds_finalTree, hextendedData]
    exact happendLastTree
  have hpenultimateTree : finalSeries.data.tree (Fin.last ett.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    change (extendedSeries.castRounds hroundsEq).data.tree (Fin.last ett.rounds).castSucc = _
    rw [TashkinovSeries.castRounds_penultimateTree, hextendedData, ← hqSucc]
    exact happendTree
  have hfinalColor : finalSeries.data.coloring (Fin.last ett.rounds) = sigma := by
    change (extendedSeries.castRounds hroundsEq).data.coloring (Fin.last ett.rounds) = sigma
    rw [TashkinovSeries.castRounds_finalColoring, hextendedData]
    exact happendLastColor
  have hprefixFields := @helper_hprefixFields_744 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@closureTree) (@hroundOne) (@prefixInput) (@zeroPrefix) (@hroundsEq)
  have hseriesDataAgree : ∀ i : Fin (ett.rounds + 1),
      finalSeries.data.stored i = ett.series.data.stored i ∧
        finalSeries.data.connectingEdges i = ett.series.data.connectingEdges i ∧
        finalSeries.data.kind i = ett.series.data.kind i := by
    change ∀ i : Fin (ett.rounds + 1),
        (extendedSeries.castRounds hroundsEq).data.stored i = ett.series.data.stored i ∧
          (extendedSeries.castRounds hroundsEq).data.connectingEdges i =
            ett.series.data.connectingEdges i ∧
          (extendedSeries.castRounds hroundsEq).data.kind i = ett.series.data.kind i
    simpa only [TashkinovSeries.castRounds_data] using
      (TashkinovSeriesData.castMetadataAgreement (r := 0)
        ett.series.data extendedSeries.data hroundsEq
        (by
          intro i
          have hi : i = Fin.last 0 := by
            apply Fin.ext
            have bound := i.isLt
            omega
          subst i
          simpa only [hextendedData, TashkinovSeriesDataAppend, Fin.lastCases_castSucc] using
            hprefixFields (Fin.castLE (by omega) (Fin.last 0))
              (by change 0 < ett.rounds; exact hpositive))
        (by
          simpa only [hextendedData, TashkinovSeriesDataAppend, Fin.lastCases_last, ← hqSucc] using
            And.intro currentStored.symm (And.intro currentEdges.symm currentKind.symm)))
  have hseriesTreeAgree : ∀ i : Fin ett.rounds,
      finalSeries.data.tree i.succ.castSucc = ett.series.data.tree i.succ.castSucc := by
    change ∀ i : Fin ett.rounds,
      (extendedSeries.castRounds hroundsEq).data.tree i.succ.castSucc =
        ett.series.data.tree i.succ.castSucc
    simpa only [TashkinovSeries.castRounds_data] using
      (TashkinovSeriesData.castTreeAgreement (r := 0)
        ett.series.data extendedSeries.data hroundsEq
        (fun i => Fin.elim0 i)
        (by
          simpa only [finalSeries, castSeries, TashkinovSeries.castRounds_data] using
            hpenultimateTree))
  have hseriesStable := TashkinovSeriesData.stabilityOfOneRound
    ett.series.data finalSeries.data.coloring hroundOne
    (by rw [hfinalColor]; exact hsigmaStable)
  have penultimate : finalSeries.data.tree (Fin.last ett.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := hpenultimateTree
  have terminal : finalSeries.data.tree (Fin.last (ett.rounds + 1)) = closureTree := hfinalTree
  exact ⟨CorrespondingExtendedTashkinovTree.ofSeries ett finalSeries
    (by rw [penultimate]; exact hTnTstar) (by rw [penultimate]; exact hstrict)
    (by rw [terminal]; exact hTstarClosure)
    hfinalColor.symm hseriesTreeAgree hseriesDataAgree hseriesStable⟩

theorem helper_branch_11555.{u_1, u_2} :
    helperBranch11555Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hclosure hTstarClosure hTnClosure q hqSucc
      adjoined previousProper previousOneUncolored choice currentStored currentEdges currentKind
      sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hsigmaPrevSigma hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf newChoice hclosedPrev hnotStrongPrev hnewAlternative
      hroundOne prefixInput zeroPrefix hzeroTree hzeroColor hsimple
  rcases hsimple with ⟨hkind, fstar, seed, hfinalEdges,
      hadjoin, hroute⟩
  have hfstar : fstar = choice.edge := by
    apply Finset.mem_singleton.mp
    rw [← currentEdges, hqSucc, hfinalEdges]
    exact Finset.mem_singleton_self fstar
  have hrouteClosure : TashkinovAugmentationSequence sigma seed
      closureTree := hroute.trans hclosure.1
  have hseedClosure : TashkinovClosure sigma seed closureTree :=
    ⟨hrouteClosure, hclosure.2⟩
  let zeroLast : Fin (0 + 1) := Fin.last 0
  let newStored : Finset (Fin k) := {choice.color}
  let newEdges : Finset E := {choice.edge}
  let newKind : Option TashkinovExtensionKind :=
    some TashkinovExtensionKind.SE
  let newVertex : Option V := some choice.vertex
  let newOutside : Option V := some choice.otherEndpoint
  let newDelta : Option (Fin k) := some choice.color
  let newGamma : Option (Fin k) := none
  let appendedData := TashkinovSeriesDataAppend zeroPrefix.data
    closureTree sigma newStored newEdges newKind newVertex newOutside
    newDelta newGamma
  have happendLastTree : appendedData.tree (Fin.last 2) =
      closureTree := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastColor : appendedData.coloring (Fin.last 1) =
      sigma := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastStored : appendedData.stored (Fin.last 1) =
      newStored := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastEdges : appendedData.connectingEdges (Fin.last 1) =
      newEdges := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastKind : appendedData.kind (Fin.last 1) =
      newKind := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastVertex : appendedData.chosenVertex (Fin.last 1) =
      newVertex := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastOutside : appendedData.outsideVertex (Fin.last 1) =
      newOutside := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastDelta : appendedData.delta (Fin.last 1) =
      newDelta := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastGamma : appendedData.gamma (Fin.last 1) =
      newGamma := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have hstoredZero : TashkinovStoredColors appendedData
      zeroLast.castSucc = TashkinovStoredColors zeroPrefix.data
        zeroLast := by
    exact TashkinovStoredColorsAppend zeroPrefix.data closureTree sigma
      newStored newEdges newKind newVertex newOutside newDelta newGamma
      zeroLast
  have happendTree := @helper_happendTree_3707 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
      (@closureTree) (@hqSucc) (@choice) (@prefixInput) (@zeroPrefix) (@hzeroTree)
  have happendColor := @helper_happendColor_3717 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
      (@closureTree) (@choice) (@sigmaPrev) (@prefixInput) (@zeroPrefix) (@hzeroColor)
  have happendStored : TashkinovStoredColors appendedData
        zeroLast.castSucc =
      TashkinovStoredColors ett.series.data q.castSucc := by
    unfold TashkinovStoredColors
    simp [zeroLast, q, hroundOne]
  let appendedChoice := @helperAppendedChoice2713 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
       (@closureTree) (@previousProper) (@previousOneUncolored) (@choice) (@sigmaPrev)
      (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective)
      (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@prefixInput) (@zeroPrefix) (@happendTree)
      (@happendColor) (@happendStored)
  have hnoRevisitingZero := @helper_hnoRevisitingZero_3741 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
      (@Tstar) (@closureTree) (@choice) (@prefixInput) (@zeroPrefix)
  have hnewAlternativeZero := @helper_hnewAlternativeZero_3753 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
       (@closureTree) (@previousProper) (@previousOneUncolored) (@choice) (@sigmaPrev)
      (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective)
      (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hnewAlternative) (@prefixInput) (@zeroPrefix)
      (@happendTree) (@happendColor) (@happendStored)
  have hstrictClosure :
      (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
        closureTree.length := lt_of_lt_of_le hstrict hTstarClosure.1
  have lastStep := @helper_lastStep_3779 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@closureTree)
      (@hTnClosure) (@hqSucc) (@adjoined) (@previousProper) (@previousOneUncolored) (@choice)
      (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hsigmaPrevSigma)
      (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev)
      (@prefixInput) (@zeroPrefix) (@fstar) (@seed) (@hadjoin) (@hfstar) (@hseedClosure)
      (@happendLastTree) (@happendLastColor) (@happendLastStored) (@happendLastEdges)
      (@happendLastKind) (@happendLastVertex) (@happendLastOutside) (@happendLastDelta)
      (@happendLastGamma) (@happendTree) (@happendColor) (@happendStored) (@hnoRevisitingZero)
      (@hnewAlternativeZero) (@hstrictClosure)
  obtain ⟨extendedSeries, hextendedData⟩ :=
    TashkinovSeriesAppend G k 0 e0 prefixInput zeroPrefix closureTree
      sigma newStored newEdges newKind newVertex newOutside newDelta
      newGamma lastStep
  have hroundsEq : 0 + 1 = ett.rounds := by omega
  let castSeries := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) => S.castRounds h
  let castSeriesTree := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + 2)) =>
    S.castRounds_tree h i
  let castSeriesColoring := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + 1)) =>
    S.castRounds_coloring h i
  let castSeriesStored := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + 1)) =>
    S.castRounds_stored h i
  let castSeriesEdges := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + 1)) =>
    S.castRounds_connectingEdges h i
  apply helper_continuation_4951 <;> assumption
theorem helper_hsigmaPrevEnlarged_12232.{u_1, u_2} :
    helperHsigmaPrevEnlarged12232Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne Tstar q
      hsigmaStableQ gamma secondStable secondStableProper secondStableOneUncolored choice
      gammaRule secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored sigmaPrev hchoiceVertex hcomponent hsigmaPrevFormula
  have hmissing : gamma ∈ MissingColors G secondStable choice.vertex := by
    exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
  have hdegree := @helper_hdegree_1837 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@secondStable)
      (@secondStableProper) (@choice)
  rcases exitWitness with ⟨u, path, pathData⟩
  rcases pathData with ⟨pathIs, pathLen, uOut, endTree, endOnly⟩
  have hdegreeBound : ∀ x, @SimpleGraph.degree _
      (TwoColorIncidenceGraph G secondStable gamma choice.color) x
      (Fintype.ofFinite _) ≤ 2 := by
    intro x
    exact TwoColorIncidenceDegreeAtMostTwo G secondStable gamma choice.color
      secondStableProper x
  have huDegree := hdegree u endOnly.1
  have hclosed : ∀ x, x ∈ path.support → ∀ y,
      (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj x y →
      y ∈ path.support := by
    exact @helper_hclosed_1893 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma)
        (@secondStable) (@choice) (@hmissing) (@hdegree) (@u) (@path) (@pathIs) (@pathLen)
        (by
          intro x
          simpa only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using
              hdegreeBound x) (@huDegree)
  have hpathComponent := @helper_hpathComponent_4867 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@gamma) (@secondStable) (@choice) (@u) (@path) (@hclosed)
  have hcompEdge := (fun (edge : E) member => TwoColorComponent.edge_colors
      (G := G) (phi := secondStable) (alpha := gamma) (beta := choice.color)
      (vertex := choice.vertex) (edge := edge) member)
  have hchoiceSecond := @helper_hchoiceSecond_4895 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@secondStable) (@choice) (@secondStableRelation)
  have hneq := @helper_hneq_4901 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@secondStable) (@choice)
      (@hmissing) (@hchoiceSecond)
  have hfcomponent : Sum.inr choice.edge ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
  have htreeEdge := @helper_htreeEdge_2018 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@secondStable)
      (@secondStableProper) (@choice) (@hmissing) (@u) (@path) (@endOnly) (@hpathComponent)
      (@hcompEdge) (@hchoiceSecond)
  have hsigmaEdge := ett.series.stableSwapComponentIncidentEdgeUnique q sigma hsigmaProper
    hsigmaStableQ gamma secondStable choice currentColoring currentStored hcomponent hmissing
    hchoiceSecond hneq
  let undone := TwoColorComponentSwap G sigma gamma choice.color
    (Sum.inl choice.vertex)
  have undoneProper : IsProperEdgeColoring G undone := by
    exact TwoColorComponentSwapProper G sigma gamma choice.color hneq
      hsigmaProper (Sum.inl choice.vertex)
  have undoneOne := @helper_undoneOne_2148 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaOne) (@Tstar)
      (@gamma) (@choice) (@hneq)
  have treeMissingTransport := @helper_treeMissingTransport_4940 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@Tstar)
  have treeSecondSelected :
      TreeMissingColors secondStable (ett.series.data.tree q.succ.castSucc) =
        TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) :=
    treeMissingTransport secondStable choice.selected (by
      intro w hw
      exact secondStableRelation.2 w hw)
  have sigmaComponentColor := (fun (edge : E) member => TwoColorComponent.edge_colors
      (G := G) (phi := sigma) (alpha := gamma) (beta := choice.color)
      (vertex := choice.vertex) (edge := edge) member)
  have currentColorMissing := @helper_currentColorMissing_2202 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@gamma) (@secondStable) (@secondStableProper) (@choice) (@currentColoring) (@hmissing)
      (@hcompEdge) (@hchoiceSecond) (@hneq) (@hfcomponent)
  have sigmaColorMissing : choice.color ∈
      MissingColors G sigma choice.vertex := by
    rw [hsigmaStableQ.2 choice.vertex hchoiceVertex]
    exact currentColorMissing
  have treeSelectedPrevious :
      TreeMissingColors choice.selected (ett.series.data.tree q.succ.castSucc) =
        TreeMissingColors (ett.series.data.coloring q.castSucc)
          (ett.series.data.tree q.succ.castSucc) :=
    treeMissingTransport choice.selected (ett.series.data.coloring q.castSucc) (by
      intro w hw
      exact choice.selectedStable.2 w hw)
  have currentControl := @helper_currentControl_2238 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@gamma) (@choice) (@currentStored) (@treeSelectedPrevious)
  have selectedStableFact := choice.selectedStable
  have sigmaStableFact := hsigmaStableQ
  have relationFact := secondStableRelation
  have gammaControl := @helper_gammaControl_5005 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma)
      (@secondStable) (@choice) (@secondStableRelation) (@hchoiceVertex) (@hmissing)
  have stableSecond : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
      secondStable undone := by
    apply (sc1 G e0 (ett.series.data.tree q.succ.castSucc)
      (insert choice.color (TashkinovStoredColors ett.series.data q.castSucc))
      secondStable undone secondStableProper secondStableOneUncolored
      undoneProper undoneOne).2
    intro f hf h
    rcases h with h | h
    · exact @helper_branch_5026 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@hsigmaStableQ)
        (@gamma) (@secondStable) (@secondStableProper) (@secondStableOneUncolored) (@choice)
        (@secondStableRelation) (@currentColoring) (@hdegree) (@u) (@path) (@hdegreeBound)
        (@hclosed) (@hpathComponent) (@hcompEdge) (@hchoiceSecond) (@htreeEdge) (@hsigmaEdge)
        (@treeSecondSelected) (@sigmaComponentColor) (@sigmaColorMissing) (@currentControl)
        (@gammaControl) (@f) (@hf) (@h)
    · exact @helper_branch_5085 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper)
        (@hsigmaOne) (@Tstar) (@hsigmaStableQ) (@gamma) (@secondStable) (@choice)
        (@currentColoring) (@currentProper) (@currentOneUncolored) (@hdegree) (@u) (@path)
        (@hdegreeBound) (@hclosed) (@hpathComponent) (@hcompEdge) (@hchoiceSecond) (@htreeEdge)
        (@hsigmaEdge) (@treeSecondSelected) (@sigmaComponentColor) (@sigmaColorMissing)
        (@currentControl) (@gammaControl) (@f) (@hf) (@h)
  have stableSelected := @helper_stableSelected_5146 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
      (@Tstar) (@gamma) (@secondStable) (@secondStableProper) (@secondStableOneUncolored) (@choice)
      (@secondStableRelation) (@undoneProper) (@undoneOne) (@treeSecondSelected) (@stableSecond)
  rw [hsigmaPrevFormula]
  exact stableSelected

private theorem helper_continuation_7494.{u_1, u_2} :
    helperContinuation7494Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hTstarClosure q hqSucc gamma choice
      currentStored currentEdges currentKind sigmaPrev hsigmaPrevProper hsigmaPrevOne H
      auxiliaryStart b auxiliaryWalk auxiliaryPath u p hp hroundOne prefixInput zeroPrefix
      zeroLast newStored newEdges newKind newVertex newOutside newDelta newGamma appendedData
      happendLastTree happendLastColor happendLastStored happendLastEdges happendLastKind
      happendTree happendColor extendedSeries hextendedData hroundsEq castSeries castSeriesTree
      castSeriesColoring castSeriesStored castSeriesEdges
  let finalSeries : TashkinovSeries G k ett.rounds e0 prefixInput :=
    castSeries hroundsEq extendedSeries
  have hfinalTree : finalSeries.data.tree (Fin.last (ett.rounds + 1)) = closureTree := by
    change (extendedSeries.castRounds hroundsEq).data.tree (Fin.last (ett.rounds + 1)) = closureTree
    rw [TashkinovSeries.castRounds_finalTree, hextendedData]
    exact happendLastTree
  have hpenultimateTree : finalSeries.data.tree (Fin.last ett.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    change (extendedSeries.castRounds hroundsEq).data.tree (Fin.last ett.rounds).castSucc = _
    rw [TashkinovSeries.castRounds_penultimateTree, hextendedData, ← hqSucc]
    exact happendTree
  have hfinalColor : finalSeries.data.coloring (Fin.last ett.rounds) = sigma := by
    change (extendedSeries.castRounds hroundsEq).data.coloring (Fin.last ett.rounds) = sigma
    rw [TashkinovSeries.castRounds_finalColoring, hextendedData]
    exact happendLastColor
  have hprefixFields :
    ∀ (i : Fin (ett.rounds + 1)), i.val < ett.rounds → zeroPrefix.data.stored zeroLast =
        ett.series.data.stored i ∧ zeroPrefix.data.connectingEdges zeroLast =
        ett.series.data.connectingEdges i ∧ zeroPrefix.data.kind zeroLast = ett.series.data.kind i
  := by
    apply helper_hprefixFields_3431 <;> assumption
  have hseriesDataAgree : ∀ i : Fin (ett.rounds + 1),
      finalSeries.data.stored i = ett.series.data.stored i ∧
        finalSeries.data.connectingEdges i = ett.series.data.connectingEdges i ∧
        finalSeries.data.kind i = ett.series.data.kind i := by
    change ∀ i : Fin (ett.rounds + 1),
        (extendedSeries.castRounds hroundsEq).data.stored i = ett.series.data.stored i ∧
          (extendedSeries.castRounds hroundsEq).data.connectingEdges i =
            ett.series.data.connectingEdges i ∧
          (extendedSeries.castRounds hroundsEq).data.kind i = ett.series.data.kind i
    simpa only [TashkinovSeries.castRounds_data] using
      (TashkinovSeriesData.castMetadataAgreement (r := 0)
        ett.series.data extendedSeries.data hroundsEq
        (by
          intro i
          have hi : i = Fin.last 0 := by
            apply Fin.ext
            have bound := i.isLt
            omega
          subst i
          simpa only [hextendedData, TashkinovSeriesDataAppend, Fin.lastCases_castSucc] using
            hprefixFields (Fin.castLE (by omega) (Fin.last 0))
              (by change 0 < ett.rounds; exact hpositive))
        (by
          simpa only [hextendedData, TashkinovSeriesDataAppend, Fin.lastCases_last, ← hqSucc] using
            And.intro currentStored.symm (And.intro currentEdges.symm currentKind.symm)))
  have hseriesTreeAgree : ∀ i : Fin ett.rounds,
      finalSeries.data.tree i.succ.castSucc = ett.series.data.tree i.succ.castSucc := by
    change ∀ i : Fin ett.rounds,
      (extendedSeries.castRounds hroundsEq).data.tree i.succ.castSucc =
        ett.series.data.tree i.succ.castSucc
    simpa only [TashkinovSeries.castRounds_data] using
      (TashkinovSeriesData.castTreeAgreement (r := 0)
        ett.series.data extendedSeries.data hroundsEq
        (fun i => Fin.elim0 i)
        (by
          simpa only [finalSeries, castSeries, TashkinovSeries.castRounds_data] using
            hpenultimateTree))
  have hseriesStable := TashkinovSeriesData.stabilityOfOneRound
    ett.series.data finalSeries.data.coloring hroundOne
    (by rw [hfinalColor]; exact hsigmaStable)
  have penultimate : finalSeries.data.tree (Fin.last ett.rounds).castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := hpenultimateTree
  have terminal : finalSeries.data.tree (Fin.last (ett.rounds + 1)) = closureTree := hfinalTree
  exact ⟨CorrespondingExtendedTashkinovTree.ofSeries ett finalSeries
    (by rw [penultimate]; exact hTnTstar) (by rw [penultimate]; exact hstrict)
    (by rw [terminal]; exact hTstarClosure)
    hfinalColor.symm hseriesTreeAgree hseriesDataAgree hseriesStable⟩

theorem helper_branch_12554.{u_1, u_2} :
    helperBranch12554Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict closureTree hclosure hTstarClosure hTnClosure q hqSucc
      gamma secondStable previousProper previousOneUncolored choice currentStored currentEdges
      currentKind sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective
      hchoiceEdgeNew hsigmaPrevSelf newChoice hclosedPrev hnotStrongPrev hnewAlternativeFails
      hgammaPrevMissing hsigmaRecovered H auxiliaryStart b auxiliaryWalk auxiliaryPath u p hp
          hnewExit hroundOne prefixInput
      zeroPrefix hzeroTree hzeroColor hparallel
  have hrouteClosure : TashkinovAugmentationSequence sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      closureTree := hparallel.2.trans hclosure.1
  have hterminalClosure : TashkinovClosure sigma
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      closureTree := ⟨hrouteClosure, hclosure.2⟩
  let zeroLast : Fin (0 + 1) := Fin.last 0
  let newStored : Finset (Fin k) := {choice.color, gamma}
  let newEdges : Finset E := {choice.edge}
  let newKind : Option TashkinovExtensionKind :=
    some TashkinovExtensionKind.PE
  let newVertex : Option V := some choice.vertex
  let newOutside : Option V := some choice.otherEndpoint
  let newDelta : Option (Fin k) := some choice.color
  let newGamma : Option (Fin k) := some gamma
  let appendedData := TashkinovSeriesDataAppend zeroPrefix.data
    closureTree sigma newStored newEdges newKind newVertex newOutside
    newDelta newGamma
  have happendLastTree : appendedData.tree (Fin.last 2) =
      closureTree := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastColor : appendedData.coloring (Fin.last 1) =
      sigma := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastStored : appendedData.stored (Fin.last 1) =
      newStored := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastEdges : appendedData.connectingEdges (Fin.last 1) =
      newEdges := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastKind : appendedData.kind (Fin.last 1) =
      newKind := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastVertex : appendedData.chosenVertex (Fin.last 1) =
      newVertex := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastOutside : appendedData.outsideVertex (Fin.last 1) =
      newOutside := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastDelta : appendedData.delta (Fin.last 1) =
      newDelta := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have happendLastGamma : appendedData.gamma (Fin.last 1) =
      newGamma := by
    simp only [appendedData, TashkinovSeriesDataAppend,
      Fin.lastCases_last]
  have hstoredZero : TashkinovStoredColors appendedData
      zeroLast.castSucc = TashkinovStoredColors zeroPrefix.data
        zeroLast := by
    exact TashkinovStoredColorsAppend zeroPrefix.data closureTree sigma
      newStored newEdges newKind newVertex newOutside newDelta newGamma
      zeroLast
  have happendTree := @helper_happendTree_5509 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
      (@closureTree) (@hqSucc) (@gamma) (@choice) (@prefixInput) (@zeroPrefix) (@hzeroTree)
  have happendColor := @helper_happendColor_5519 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar)
      (@closureTree) (@gamma) (@choice) (@sigmaPrev) (@prefixInput) (@zeroPrefix) (@hzeroColor)
  have happendStored : TashkinovStoredColors appendedData
        zeroLast.castSucc =
      TashkinovStoredColors ett.series.data q.castSucc := by
    unfold TashkinovStoredColors
    simp [zeroLast, q, hroundOne]
  let appendedChoice := @helperAppendedChoice4500 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
       (@closureTree) (@gamma) (@previousProper) (@previousOneUncolored) (@choice)
      (@sigmaPrev) (@hsigmaPrevProper) (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective)
      (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@prefixInput) (@zeroPrefix) (@happendTree)
      (@happendColor) (@happendStored)
  have hpeNoRevisitingZero := @helper_hpeNoRevisitingZero_5543 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
      (@Tstar) (@closureTree) (@gamma) (@choice) (@sigmaPrev) (@u) (@p) (@prefixInput) (@zeroPrefix)
  have hpeAlternativeZero : ∃ rho : PartialEdgeColoring E k,
      IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (appendedData.tree zeroLast.succ.castSucc)
          (insert appendedChoice.color
            (TashkinovStoredColors appendedData zeroLast.castSucc))
          appendedChoice.selected rho ∧
        ¬ Disjoint (MissingColors G rho appendedChoice.otherEndpoint)
          (TreeMissingColors rho
            (appendedData.tree zeroLast.succ.castSucc)) := by
    apply helper_hpeAlternativeZero_5555; assumption
  have hpeGammaRuleZero : ParallelExtensionColor appendedData
      zeroLast.castSucc appendedChoice.selected appendedChoice.vertex
      gamma := by
    apply helper_hpeGammaRuleZero_5579 <;> assumption
  have hstrictClosure :
      (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
        closureTree.length := lt_of_lt_of_le hstrict hTstarClosure.1
  have lastStep : TashkinovSeriesStep G k 1 e0 prefixInput
      appendedData (Fin.last 1) := by
    apply helper_lastStep_5593 <;> assumption
  obtain ⟨extendedSeries, hextendedData⟩ :=
    TashkinovSeriesAppend G k 0 e0 prefixInput zeroPrefix closureTree
      sigma newStored newEdges newKind newVertex newOutside newDelta
      newGamma lastStep
  have hroundsEq : 0 + 1 = ett.rounds := by omega
  let castSeries := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) => S.castRounds h
  let castSeriesTree := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + 2)) =>
    S.castRounds_tree h i
  let castSeriesColoring := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + 1)) =>
    S.castRounds_coloring h i
  let castSeriesStored := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + 1)) =>
    S.castRounds_stored h i
  let castSeriesEdges := fun {a b : ℕ} (h : a = b)
      (S : TashkinovSeries G k a e0 prefixInput) (i : Fin (b + 1)) =>
    S.castRounds_connectingEdges h i
  exact @helper_continuation_7494 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne)
      (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree) (@hTstarClosure) (@hqSucc)
      (@gamma) (@choice) (@currentStored) (@currentEdges) (@currentKind) (@sigmaPrev)
      (@hsigmaPrevProper) (@hsigmaPrevOne) _ (@b) _ (by
    assumption) (@u) (@p) (@hp) (@hroundOne) (@prefixInput) (@zeroPrefix) (@happendLastTree)
        (@happendLastColor) (@happendLastStored) (@happendLastEdges) (@happendLastKind)
        (@happendTree) (@happendColor) (@extendedSeries) (@hextendedData) (@hroundsEq)
        (@castSeriesTree) (@castSeriesColoring) (@castSeriesStored) (@castSeriesEdges)
theorem helper_pePostStatus_12865.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring q.castSucc))
        (sigmaPrev : PartialEdgeColoring E k), Sum.inr choice.edge ∈ TwoColorComponent G sigmaPrev
        gamma choice.color (Sum.inl choice.vertex) →
    ∀ (X : TreeSequence G e0) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k) (ch :
        MaximumDefectiveChoice G e0 X C phi) (g : Fin k) (second : PartialEdgeColoring E k),
        IsProperEdgeColoring G second → StableColoring X (insert ch.color C : Finset (Fin k))
        ch.selected second → g ∈ MissingColors G ch.selected ch.vertex →
    let post : PartialEdgeColoring E k := TwoColorComponentSwap G second g ch.color (Sum.inl
        ch.vertex); ch.color ∈ MissingColors G post ch.vertex ∧ g ∉ MissingColors G post ch.vertex
        ∧ g ≠ ch.color := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive _ q gamma choice sigmaPrev
      hedgeComponent X C phi ch g second hsecondProper hsecondStable hgSelected
  dsimp
  have hgSecond : g ∈ MissingColors G second ch.vertex := by
    rw [hsecondStable.2 ch.vertex ch.vertexDefective.1]
    exact hgSelected
  have hedgeSecond : second ch.edge = some ch.color := by
    exact (hsecondStable.1 ch.edge
      ⟨ch.vertex, ch.vertexDefective.1, ch.edgeIncident⟩
      ⟨ch.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), ch.edgeColor⟩).trans ch.edgeColor
  have hne := @helper_hne_6004 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@X) (@C)
      (@phi) (@ch) (@g) (@second) (@hgSecond) (@hedgeSecond)
  have hedgeComponent : Sum.inr ch.edge ∈
      TwoColorComponent G second g ch.color
        (Sum.inl ch.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph,
      ch.edgeIncident, hedgeSecond]
  have hmissingDelta : ch.color ∈ MissingColors G
      (TwoColorComponentSwap G second g ch.color
        (Sum.inl ch.vertex)) ch.vertex := by
    exact (TwoColorComponentSwapMissingBehavior G second g ch.color
      hne hsecondProper (Sum.inl ch.vertex)).2.1 ch.vertex rfl hgSecond
  have hedgePost : TwoColorComponentSwap G second g ch.color
      (Sum.inl ch.vertex) ch.edge = some g := by
    simp [TwoColorComponentSwap, hedgeComponent, hedgeSecond,
      hne.symm]
  have hgammaPresent : g ∈ PresentColors G
      (TwoColorComponentSwap G second g ch.color
        (Sum.inl ch.vertex)) ch.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨ch.edge, ch.edgeIncident, hedgePost⟩
  exact ⟨hmissingDelta,
    by simpa [MissingColors] using hgammaPresent, hne⟩

private theorem helper_continuation_6083.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : Fin k) (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1
        : ℕ) < ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (ett.series.data.coloring
        (⟨ett.rounds - (1 : ℕ),
    by
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (corr :
        CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev (ett.series.data.tree
        (Fin.last ett.rounds).castSucc)) (_ : Fin (originalPrefix.rounds + (1 : ℕ))) (fulli : Fin
        ett.rounds) (fullChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)) (fullGamma : Fin k) (_ :
        ett.series.data.chosenVertex fulli.succ = some fullChoice.vertex) (_ :
        ett.series.data.delta fulli.succ = some fullChoice.color) (_ : ett.series.data.gamma
        fulli.succ = some fullGamma) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (newGamma : Fin k) (_ :
        corr.replacementSeries.data.chosenVertex newi.succ = some newChoice.vertex) (_ :
        corr.replacementSeries.data.delta newi.succ = some newChoice.color) (_ :
        corr.replacementSeries.data.gamma newi.succ = some newGamma) (_ : Fin.castLE (
    by
              omega
    ) newi.succ = fulli.succ) (htree : corr.replacementSeries.data.tree newi.succ.castSucc =
        ett.series.data.tree fulli.succ.castSucc),
    let fullChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc) := (Eq.symm htree ▸ fullChoice);
    ∀ (_ : fullChoiceOnNew.vertex = fullChoice.vertex) (_ : fullChoiceOnNew.color =
        fullChoice.color) (_ : ({ fullChoiceOnNew.edge } : Finset E) = ({ newChoice.edge } :
        Finset E)) (_ : (insert fullChoiceOnNew.color ({ fullGamma } : Finset (Fin k)) : Finset
        (Fin k)) = (insert newChoice.color ({ newGamma } : Finset (Fin k)) : Finset (Fin k))) (_ :
        fullChoice.color ∈ MissingColors G (ett.series.data.coloring fulli.succ)
        fullChoice.vertex) (_ : fullGamma ∉ MissingColors G (ett.series.data.coloring fulli.succ)
        fullChoice.vertex) (_ : newChoice.color ∈ MissingColors G
        (corr.replacementSeries.data.coloring newi.succ) newChoice.vertex) (_ : newGamma ∉
        MissingColors G (corr.replacementSeries.data.coloring newi.succ) newChoice.vertex) (_ :
        MissingColors G (ett.series.data.coloring fulli.succ) fullChoiceOnNew.vertex =
        MissingColors G (corr.replacementSeries.data.coloring newi.succ) newChoice.vertex),
        corr.replacementSeries.data.chosenVertex newi.succ = ett.series.data.chosenVertex
        (Fin.castLE (
    by
              omega
    ) newi.succ) ∧ corr.replacementSeries.data.delta newi.succ = ett.series.data.delta (Fin.castLE
        (
    by
                omega
    ) newi.succ) ∧ corr.replacementSeries.data.gamma newi.succ = ett.series.data.gamma (Fin.castLE
        (
    by
                omega
    ) newi.succ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett gamma sigmaPrev hroundLarge originalPrefix hr
      corr j fulli fullChoice fullGamma fullCurrentVertex fullCurrentDelta fullCurrentGamma newi
      newChoice newGamma newCurrentVertex newCurrentDelta newCurrentGamma hindexMap htree
      fullChoiceOnNew hfullVertexCast hfullColorCast hedgePairs hcolorPairs hfullDeltaMissing
      hfullGammaNotMissing hnewDeltaMissing hnewGammaNotMissing hmissing
  have hfullDeltaForIdentification :
      fullChoiceOnNew.color ∈ MissingColors G
        (ett.series.data.coloring fulli.succ)
        fullChoiceOnNew.vertex := by
    simpa only [hfullColorCast, hfullVertexCast] using
      hfullDeltaMissing
  have hfullGammaForIdentification : fullGamma ∉
      MissingColors G
        (ett.series.data.coloring fulli.succ)
        fullChoiceOnNew.vertex := by
    simpa only [hfullVertexCast] using hfullGammaNotMissing
  have hidentified := TdEarlierPEWitnessIdentification G k e0
    (corr.replacementSeries.data.tree newi.succ.castSucc)
    (TashkinovStoredColors ett.series.data fulli.castSucc)
    (TashkinovStoredColors corr.replacementSeries.data
      newi.castSucc)
    (ett.series.data.coloring fulli.castSucc)
    (corr.replacementSeries.data.coloring newi.castSucc)
    fullChoiceOnNew newChoice fullGamma newGamma
    (ett.series.data.coloring fulli.succ)
    (corr.replacementSeries.data.coloring newi.succ)
    hedgePairs hcolorPairs hmissing
    hfullDeltaForIdentification hfullGammaForIdentification
    hnewDeltaMissing hnewGammaNotMissing
  rcases hidentified with ⟨-, hidentifiedVertex, -,
    hidentifiedDelta, hidentifiedGamma⟩
  constructor
  · calc
      corr.replacementSeries.data.chosenVertex newi.succ =
          some newChoice.vertex := newCurrentVertex
      _ = some fullChoiceOnNew.vertex :=
        congrArg some hidentifiedVertex
      _ = some fullChoice.vertex :=
        congrArg some hfullVertexCast
      _ = ett.series.data.chosenVertex fulli.succ :=
        fullCurrentVertex.symm
      _ = ett.series.data.chosenVertex
          (Fin.castLE (by omega) newi.succ) :=
        congrArg _ hindexMap.symm
  · constructor
    · calc
        corr.replacementSeries.data.delta newi.succ =
            some newChoice.color := newCurrentDelta
        _ = some fullChoiceOnNew.color :=
          congrArg some hidentifiedDelta
        _ = some fullChoice.color :=
          congrArg some hfullColorCast
        _ = ett.series.data.delta fulli.succ :=
          fullCurrentDelta.symm
        _ = ett.series.data.delta
            (Fin.castLE (by omega) newi.succ) :=
          congrArg _ hindexMap.symm
    · calc
        corr.replacementSeries.data.gamma newi.succ =
            some newGamma := newCurrentGamma
        _ = some fullGamma := congrArg some hidentifiedGamma
        _ = ett.series.data.gamma fulli.succ :=
          fullCurrentGamma.symm
        _ = ett.series.data.gamma
            (Fin.castLE (by omega) newi.succ) :=
          congrArg _ hindexMap.symm

private theorem helper_hedgePairs_6811.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (_ :
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
                    omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
                      omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
                        omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                          omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                          omega
    ) i)) (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (j : Fin (originalPrefix.rounds +
        (1 : ℕ))),
    let fullj : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE (
    by
          omega
    ) j;
    ∀ (fulli : Fin ett.rounds) (fullChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)) (_ : ett.series.data.connectingEdges fulli.succ
        = ({ fullChoice.edge } : Finset E)) (_ : fulli.succ = fullj) (newi : Fin
        originalPrefix.rounds) (newChoice : MaximumDefectiveChoice G e0
        (corr.replacementSeries.data.tree newi.succ.castSucc) (TashkinovStoredColors
        corr.replacementSeries.data newi.castSucc) (corr.replacementSeries.data.coloring
        newi.castSucc)) (_ : corr.replacementSeries.data.connectingEdges newi.succ =
        ({ newChoice.edge } : Finset E)) (_ : newi.succ = j) (htree :
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        fulli.succ.castSucc),
    let fullChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc) := (Eq.symm htree ▸ fullChoice);
    ∀ (_ : fullChoiceOnNew.edge = fullChoice.edge), ({ fullChoiceOnNew.edge } : Finset E) =
        ({ newChoice.edge } : Finset E) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigmaPrev hroundLarge originalPrefix hr
      hprefixData corr j fullj fulli fullChoice fullCurrentEdges hfullIndex newi newChoice
      newCurrentEdges hnewIndex htree fullChoiceOnNew hfullEdgeCast
  have hfullEdges : ett.series.data.connectingEdges fullj =
      {fullChoice.edge} := by
    simpa [hfullIndex] using fullCurrentEdges
  have hnewEdges :
      corr.replacementSeries.data.connectingEdges j =
        {newChoice.edge} := by
    simpa [hnewIndex] using newCurrentEdges
  calc
    {fullChoiceOnNew.edge} = {fullChoice.edge} := by
      rw [hfullEdgeCast]
    _ = ett.series.data.connectingEdges fullj :=
      hfullEdges.symm
    _ = originalPrefix.series.data.connectingEdges j :=
      (hprefixData j).2.2.1.symm
    _ = corr.replacementSeries.data.connectingEdges j :=
      (corr.connectingEdgesAgree j).symm
    _ = {newChoice.edge} := hnewEdges

private theorem helper_hcolorPairs_6830.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)) (_ :
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
                    omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
                      omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
                        omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                          omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                          omega
    ) i)) (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (j : Fin (originalPrefix.rounds +
        (1 : ℕ))),
    let fullj : Fin (ett.rounds + (1 : ℕ)) := Fin.castLE (
    by
          omega
    ) j;
    ∀ (fulli : Fin ett.rounds) (fullChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)) (fullGamma : Fin k) (_ : ett.series.data.stored
        fulli.succ = (insert fullChoice.color ({ fullGamma } : Finset (Fin k)) : Finset (Fin k)))
        (_ : fulli.succ = fullj) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (newGamma : Fin k) (_ :
        corr.replacementSeries.data.stored newi.succ = (insert newChoice.color ({ newGamma } :
        Finset (Fin k)) : Finset (Fin k))) (_ : newi.succ = j) (htree :
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        fulli.succ.castSucc),
    let fullChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc) := (Eq.symm htree ▸ fullChoice);
    ∀ (_ : fullChoiceOnNew.color = fullChoice.color), (insert fullChoiceOnNew.color ({ fullGamma }
        : Finset (Fin k)) : Finset (Fin k)) = (insert newChoice.color ({ newGamma } : Finset (Fin
        k)) : Finset (Fin k)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigmaPrev hroundLarge originalPrefix hr
      hprefixData corr j fullj fulli fullChoice fullGamma fullCurrentStored hfullIndex newi
      newChoice newGamma newCurrentStored hnewIndex htree fullChoiceOnNew hfullColorCast
  have hfullStored : ett.series.data.stored fullj =
      {fullChoice.color, fullGamma} := by
    simpa [hfullIndex] using fullCurrentStored
  have hnewStored : corr.replacementSeries.data.stored j =
      {newChoice.color, newGamma} := by
    simpa [hnewIndex] using newCurrentStored
  calc
    {fullChoiceOnNew.color, fullGamma} =
        {fullChoice.color, fullGamma} := by rw [hfullColorCast]
    _ = ett.series.data.stored fullj := hfullStored.symm
    _ = originalPrefix.series.data.stored j :=
      (hprefixData j).2.1.symm
    _ = corr.replacementSeries.data.stored j :=
      (corr.storedColorsAgree j).symm
    _ = {newChoice.color, newGamma} := hnewStored

private theorem helper_hends_6853.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (fulli :
        Fin ett.rounds) (fullChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (htree :
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        fulli.succ.castSucc),
    let fullChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc) := (Eq.symm htree ▸ fullChoice);
    ∀ (_ : newChoice.edge = fullChoiceOnNew.edge), s(fullChoiceOnNew.vertex,
        fullChoiceOnNew.otherEndpoint) = s(newChoice.vertex, newChoice.otherEndpoint) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigmaPrev hroundLarge originalPrefix corr fulli
      fullChoice newi newChoice htree fullChoiceOnNew hedgeIdentity
  calc
    s(fullChoiceOnNew.vertex,
        fullChoiceOnNew.otherEndpoint) =
        G.ends fullChoiceOnNew.edge :=
      fullChoiceOnNew.edgeEnds.symm
    _ = G.ends newChoice.edge :=
      congrArg G.ends hedgeIdentity.symm
    _ = s(newChoice.vertex, newChoice.otherEndpoint) :=
      newChoice.edgeEnds

private theorem helper_hvertexIdentity_6865.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (fulli :
        Fin ett.rounds) (fullChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (htree :
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        fulli.succ.castSucc),
    let fullChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc) := (Eq.symm htree ▸ fullChoice);
    ∀ (_ : s(fullChoiceOnNew.vertex, fullChoiceOnNew.otherEndpoint) = s(newChoice.vertex,
        newChoice.otherEndpoint)), newChoice.vertex = fullChoiceOnNew.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigmaPrev hroundLarge originalPrefix corr fulli
      fullChoice newi newChoice htree fullChoiceOnNew hends
  rcases Sym2.eq_iff.mp hends with hstraight | hcross
  · exact hstraight.1.symm
  · exfalso
    exact newChoice.otherOutside
      (hcross.1 ▸ fullChoiceOnNew.vertexDefective.1)

private theorem helper_hmissing_6909.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (sigmaPrev : PartialEdgeColoring E k) (hroundLarge : (1 : ℕ) <
        ett.rounds) (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (corr : CorrespondingExtendedTashkinovTree G k e0
        originalPrefix sigmaPrev (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (fulli :
        Fin ett.rounds) (fullChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        fulli.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc)) (newi : Fin originalPrefix.rounds) (newChoice :
        MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree newi.succ.castSucc)
        (TashkinovStoredColors corr.replacementSeries.data newi.castSucc)
        (corr.replacementSeries.data.coloring newi.castSucc)) (htree :
        corr.replacementSeries.data.tree newi.succ.castSucc = ett.series.data.tree
        fulli.succ.castSucc),
    let fullChoiceOnNew : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        newi.succ.castSucc) (TashkinovStoredColors ett.series.data fulli.castSucc)
        (ett.series.data.coloring fulli.castSucc) := (Eq.symm htree ▸ fullChoice);
    ∀ (_ : fullChoiceOnNew.vertex = fullChoice.vertex) (_ : newChoice.vertex =
        fullChoiceOnNew.vertex) (_ : originalPrefix.series.data.coloring newi.succ =
        ett.series.data.coloring fulli.succ) (_ : MissingColors G
        (corr.replacementSeries.data.coloring newi.succ) fullChoice.vertex = MissingColors G
        (originalPrefix.series.data.coloring newi.succ) fullChoice.vertex), MissingColors G
        (ett.series.data.coloring fulli.succ) fullChoiceOnNew.vertex = MissingColors G
        (corr.replacementSeries.data.coloring newi.succ) newChoice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T generating ett sigmaPrev hroundLarge originalPrefix corr fulli
      fullChoice newi newChoice htree fullChoiceOnNew hfullVertexCast hvertexIdentity
      hprefixPostFull hstableMissing
  calc
    MissingColors G
        (ett.series.data.coloring fulli.succ)
        fullChoiceOnNew.vertex =
        MissingColors G
          (ett.series.data.coloring fulli.succ)
          fullChoice.vertex := congrArg _ hfullVertexCast
    _ = MissingColors G
          (originalPrefix.series.data.coloring newi.succ)
          fullChoice.vertex := congrArg
            (fun phi => MissingColors G phi fullChoice.vertex)
            hprefixPostFull.symm
    _ = MissingColors G
          (corr.replacementSeries.data.coloring newi.succ)
          fullChoice.vertex := hstableMissing.symm
    _ = MissingColors G
          (corr.replacementSeries.data.coloring newi.succ)
          newChoice.vertex := congrArg _
            (hvertexIdentity.trans hfullVertexCast).symm

theorem helper_branch_12991.{u_1, u_2} :
    helperBranch12991Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive Tstar q gamma choice sigmaPrev H u p
      hroundLarge originalPrefix hr hprefixTrees hprefixData corr horiginalPositive pePostStatus
      j fullj fulli fullChoice fullGamma fullGammaRule fullSecond fullSecondProper
      fullSecondStable fullCurrentColoring fullCurrentStored fullCurrentEdges fullCurrentVertex
      fullCurrentDelta fullCurrentGamma hfullTarget hfullIndex newi newChoice newGamma
      newGammaRule newSecond newSecondProper newSecondStable newCurrentColoring newCurrentStored
      newCurrentEdges newCurrentVertex newCurrentDelta newCurrentGamma hnewTarget
  have hnewIndex : newi.succ = j := by
    simpa using hnewTarget.symm
  have hindexMap := @helper_hindexMap_6123 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice)
      (@sigmaPrev) (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@horiginalPositive)
      (@j) (@fulli) (@hfullIndex) (@newi) (@hnewTarget) (@hnewIndex)
  have htree := @helper_htree_6130 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma) (@choice) (@sigmaPrev)
      (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@corr) (@horiginalPositive)
      (@j) (@fulli) (@hfullIndex) (@newi) (@hnewTarget) (@hnewIndex)
  let fullChoiceOnNew : MaximumDefectiveChoice G e0
      (corr.replacementSeries.data.tree newi.succ.castSucc)
      (TashkinovStoredColors ett.series.data fulli.castSucc)
      (ett.series.data.coloring fulli.castSucc) :=
    htree.symm ▸ fullChoice
  have transportChoiceFields :
    ∀ {A B : TreeSequence G e0} (hAB : A = B) (C : Finset (Fin k)) (phi : PartialEdgeColoring E k)
        (ch : MaximumDefectiveChoice G e0 A C phi), (hAB ▸ ch).edge = ch.edge ∧ (hAB ▸ ch).vertex
        = ch.vertex ∧ (hAB ▸ ch).otherEndpoint = ch.otherEndpoint ∧ (hAB ▸ ch).color = ch.color
  := by
    intro A B hAB C phi ch
    subst B
    exact ⟨rfl, rfl, rfl, rfl⟩
  have htransport := transportChoiceFields htree.symm
    (TashkinovStoredColors ett.series.data fulli.castSucc)
    (ett.series.data.coloring fulli.castSucc) fullChoice
  have hfullEdgeCast : fullChoiceOnNew.edge =
      fullChoice.edge := htransport.1
  have hfullVertexCast : fullChoiceOnNew.vertex =
      fullChoice.vertex := htransport.2.1
  have hfullOtherCast : fullChoiceOnNew.otherEndpoint =
      fullChoice.otherEndpoint := htransport.2.2.1
  have hfullColorCast : fullChoiceOnNew.color =
      fullChoice.color := htransport.2.2.2
  have hedgePairs : ({fullChoiceOnNew.edge} : Finset E) =
      {newChoice.edge} := by
    apply helper_hedgePairs_6811 <;> assumption
  have hcolorPairs :
      ({fullChoiceOnNew.color, fullGamma} : Finset (Fin k)) =
        {newChoice.color, newGamma} := by
    apply helper_hcolorPairs_6830 <;> assumption
  have hedgeIdentity : newChoice.edge =
      fullChoiceOnNew.edge := by
    apply Finset.mem_singleton.mp
    rw [hedgePairs]
    exact Finset.mem_singleton_self _
  have hends : s(fullChoiceOnNew.vertex,
        fullChoiceOnNew.otherEndpoint) =
      s(newChoice.vertex, newChoice.otherEndpoint) := by
    apply helper_hends_6853 <;> assumption
  have hvertexIdentity : newChoice.vertex =
      fullChoiceOnNew.vertex := by
    apply helper_hvertexIdentity_6865 <;> assumption
  obtain ⟨hfullDeltaMissing, hfullGammaNotMissing, -⟩ :=
    pePostStatus
      (ett.series.data.tree fulli.succ.castSucc)
      (TashkinovStoredColors ett.series.data fulli.castSucc)
      (ett.series.data.coloring fulli.castSucc) fullChoice
      fullGamma fullSecond fullSecondProper fullSecondStable
      fullGammaRule.1
  obtain ⟨hnewDeltaMissing, hnewGammaNotMissing, -⟩ :=
    pePostStatus
      (corr.replacementSeries.data.tree newi.succ.castSucc)
      (TashkinovStoredColors corr.replacementSeries.data
        newi.castSucc)
      (corr.replacementSeries.data.coloring newi.castSucc)
      newChoice newGamma newSecond newSecondProper
      newSecondStable newGammaRule.1
  rw [← fullCurrentColoring] at hfullDeltaMissing hfullGammaNotMissing
  rw [← newCurrentColoring] at hnewDeltaMissing hnewGammaNotMissing
  have hprefixPostFull := @helper_hprefixPostFull_6259 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@gamma) (@choice) (@sigmaPrev) (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr)
      (@hprefixData) (@corr) (@horiginalPositive) (@j) (@fulli) (@fullChoice) (@hfullTarget) (@newi)
      (@hnewIndex) (@htree)
  have hvPrefix : fullChoice.vertex ∈
      TreeSequenceVertexSet
        (originalPrefix.series.data.tree
          newi.succ.castSucc) := by
    rw [← corr.ladderTreesAgree newi]
    simpa [hfullVertexCast] using
      fullChoiceOnNew.vertexDefective.1
  have hstableMissing :=
    (corr.replacementStable newi).2 fullChoice.vertex hvPrefix
  have hmissing : MissingColors G
        (ett.series.data.coloring fulli.succ)
        fullChoiceOnNew.vertex =
      MissingColors G
        (corr.replacementSeries.data.coloring newi.succ)
        newChoice.vertex := by
    apply helper_hmissing_6909 <;> assumption
  exact helper_continuation_6083 (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@gamma)
      (@sigmaPrev) (@hroundLarge) (@originalPrefix) (@hr) (@corr) (@j) (@fulli) (@fullChoice)
      (@fullGamma) (@fullCurrentVertex) (@fullCurrentDelta) (@fullCurrentGamma) (@newi)
      (@newChoice) (@newGamma) (@newCurrentVertex) (@newCurrentDelta) (@newCurrentGamma)
      (@hindexMap) (@htree) (@hfullVertexCast) (@hfullColorCast) (@hedgePairs) (@hcolorPairs)
      (@hfullDeltaMissing) (@hfullGammaNotMissing) (@hnewDeltaMissing) (@hnewGammaNotMissing)
      (@hmissing)
theorem helper_branch_12854.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring (Fin.last ett.rounds))
        sigma →
    ∀ (Tstar : TreeSequence G e0), TreeSequenceInitialSegment (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) Tstar → (ett.series.data.tree (Fin.last ett.rounds).castSucc).length
        < Tstar.length → (ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) Tstar ∨ (ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges (Fin.last ett.rounds) =
        ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) f seed ∧ TashkinovAugmentationSequence sigma seed Tstar) →
    ∀ (closureTree : TreeSequence G e0), TashkinovClosure sigma Tstar closureTree →
        TreeSequenceInitialSegment Tstar closureTree → TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (_ : TreeSequence G e0) (previousProper : IsProperEdgeColoring G (ett.series.data.coloring
        q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring
        q.castSucc) e0) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), ett.series.data.stored q.succ = ({ choice.color }
        : Finset (Fin k)) → ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E)
        → ett.series.data.kind q.succ = some TashkinovExtensionKind.SE → ett.series.data.kind
        q.succ = some TashkinovExtensionKind.SE →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev), sigmaPrev = sigma →
    ∀ (hchoiceDefective : DefectiveColor G sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) choice.color) (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hsigmaPrevSelf : StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice2409 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; ColoredVertexSetClosed G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) → (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected pi
        → Disjoint (MissingColors G pi newChoice.otherEndpoint) (TreeMissingColors pi
        (ett.series.data.tree q.succ.castSucc))) → (ett.rounds = (1 : ℕ) ∧
    ∃ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput), zeroPrefix.data.tree (Fin.last (1 : ℕ)) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc ∧ zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev) → Nonempty
        (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict heligible closureTree hclosure hTstarClosure hTnClosure
      q hqSucc adjoined previousProper previousOneUncolored choice currentStored currentEdges
      currentKind hseKind sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hsigmaPrevSigma hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice hclosedPrev
      hnotStrongPrev hnewAlternative hzero
  rcases hzero with ⟨hroundOne, prefixInput, zeroPrefix,
      hzeroTree, hzeroColor⟩
  rcases heligible with hparallel | hsimple
  · have hbad := hparallel.1.symm.trans
      (by simpa [hqSucc] using hseKind)
    cases hbad
  · exact @helper_branch_11555 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne)
      (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree) (@hclosure) (@hTstarClosure)
      (@hTnClosure) (@hqSucc) (@adjoined) (@previousProper) (@previousOneUncolored) (@choice)
      (@currentStored) (@currentEdges) (@currentKind) (@sigmaPrev) (@hsigmaPrevProper)
      (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hsigmaPrevSigma) (@hchoiceDefective)
      (@hchoiceEdgeNew) (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev) (@hnewAlternative)
      (@hroundOne) (@prefixInput) (@zeroPrefix) (@hzeroTree) (@hzeroColor) (@hsimple)

theorem helper_branch_13492.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) (ett.series.data.coloring (Fin.last ett.rounds))
        sigma →
    ∀ (Tstar : TreeSequence G e0), TreeSequenceInitialSegment (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) Tstar → (ett.series.data.tree (Fin.last ett.rounds).castSucc).length
        < Tstar.length → (ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) Tstar ∨ (ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges (Fin.last ett.rounds) =
        ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) f seed ∧ TashkinovAugmentationSequence sigma seed Tstar) →
    ∀ (closureTree : TreeSequence G e0), TashkinovClosure sigma Tstar closureTree →
        TreeSequenceInitialSegment Tstar closureTree → TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) closureTree →
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); q.succ = Fin.last ett.rounds →
    ∀ (gamma : Fin k) (_ : PartialEdgeColoring E k) (previousProper : IsProperEdgeColoring G
        (ett.series.data.coloring q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored
        (ett.series.data.coloring q.castSucc) e0) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), ett.series.data.stored q.succ = (insert
        choice.color ({ gamma } : Finset (Fin k)) : Finset (Fin k)) →
        ett.series.data.connectingEdges q.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE → ett.series.data.kind q.succ
        = some TashkinovExtensionKind.PE →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev) (hchoiceDefective : DefectiveColor G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        sigmaPrev sigmaPrev),
    let newChoice : MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc) sigmaPrev := helperNewChoice4049 G k e0
        input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf; ColoredVertexSetClosed G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G sigmaPrev
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) → (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree q.succ.castSucc) (insert newChoice.color
        (TashkinovStoredColors ett.series.data q.castSucc) : Finset (Fin k)) newChoice.selected
        rho ∧ ¬Disjoint (MissingColors G rho newChoice.otherEndpoint) (TreeMissingColors rho
        (ett.series.data.tree q.succ.castSucc))) → gamma ∈ MissingColors G sigmaPrev choice.vertex
        → sigma = TwoColorComponentSwap G sigmaPrev gamma choice.color (Sum.inl choice.vertex) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color;
    ∀ (a b : V ⊕ E) (p_1 : (TwoColorIncidenceGraph G sigmaPrev gamma choice.color).Walk a b),
        p_1.IsPath →
    ∀ (u : V) (p : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), p.IsPath → TreeExit
        (ett.series.data.tree q.succ.castSucc) sigmaPrev gamma choice.color choice.vertex →
        (ett.rounds = (1 : ℕ) ∧
    ∃ (prefixInput : PartialEdgeColoring E k) (zeroPrefix : TashkinovSeries G k (0 : ℕ) e0
        prefixInput), zeroPrefix.data.tree (Fin.last (1 : ℕ)) = ett.series.data.tree (Fin.last
        ett.rounds).castSucc ∧ zeroPrefix.data.coloring (Fin.last (0 : ℕ)) = sigmaPrev) → Nonempty
        (CorrespondingExtendedTashkinovTree G k e0 ett sigma Tstar) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma hsigmaProper hsigmaOne
      hsigmaStable Tstar hTnTstar hstrict heligible closureTree hclosure hTstarClosure hTnClosure
      q hqSucc gamma secondStable previousProper previousOneUncolored choice currentStored
      currentEdges currentKind hpeKind sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice hclosedPrev hnotStrongPrev
      hnewAlternativeFails hgammaPrevMissing hsigmaRecovered H auxiliaryStart b auxiliaryWalk
          auxiliaryPath u p hp hnewExit hzero
  rcases hzero with ⟨hroundOne, prefixInput, zeroPrefix,
      hzeroTree, hzeroColor⟩
  rcases heligible with hparallel | hsimple
  · exact @helper_branch_12554 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@hsigmaProper) (@hsigmaOne)
      (@hsigmaStable) (@Tstar) (@hTnTstar) (@hstrict) (@closureTree) (@hclosure) (@hTstarClosure)
      (@hTnClosure) (@hqSucc) (@gamma) (@secondStable) (@previousProper) (@previousOneUncolored)
      (@choice) (@currentStored) (@currentEdges) (@currentKind) (@sigmaPrev) (@hsigmaPrevProper)
      (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective) (@hchoiceEdgeNew)
      (@hsigmaPrevSelf) (@hclosedPrev) (@hnotStrongPrev) (@hnewAlternativeFails)
      (@hgammaPrevMissing) (@hsigmaRecovered) (@auxiliaryStart) (@b) (@auxiliaryWalk)
          (@auxiliaryPath) (@u) (@p) (@hp)
      (@hnewExit) (@hroundOne) (@prefixInput) (@zeroPrefix) (@hzeroTree) (@hzeroColor) (@hparallel)
  · exact @helper_branch_5820 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma) (@Tstar) (@hqSucc) (@hpeKind)
      (@hsimple)

theorem helper_retainedPEFields_13584.{u_1, u_2} :
    helperRetainedPEFields13584Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive Tstar q gamma previousProper
      previousOneUncolored choice sigmaPrev hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ
      hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf newChoice H u p hroundLarge originalPrefix
      hr hprefixTrees hprefixData corr horiginalPositive retainedKind pePostStatus j hjPositive hjPE
  let fullj : Fin (ett.rounds + 1) := Fin.castLE (by omega) j
  have hfullPE : ett.series.data.kind fullj =
      some TashkinovExtensionKind.PE := by
    simpa [fullj] using (retainedKind j).symm.trans hjPE
  have hfullStep := ett.series.certified fullj
  generalize hfullTarget : fullj = fullTarget at hfullStep
  cases hfullStep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have hbad := initialKind.symm.trans
        (by simpa [hfullTarget] using hfullPE)
      simp at hbad
  | SE fulli fullPreviousProper fullPreviousOne fullPreviousClosed
      fullPreviousNotStrong fullNoRE fullChoice fullAlternative
      fullCurrentColoring fullCurrentStored fullCurrentEdges
      fullCurrentKind fullCurrentVertex fullCurrentOutside
      fullCurrentDelta fullCurrentGamma fullAdjoined
      fullAdjoinedExactly fullClosed fullOrdered fullStrict =>
      have hbad := fullCurrentKind.symm.trans
        (by simpa [hfullTarget] using hfullPE)
      cases hbad
  | RE fulli fullPreviousProper fullPreviousOne fullPreviousClosed
      fullPreviousNotStrong fullAvailable fullCurrentColoring
      fullCurrentStored fullCurrentEdges fullCurrentKind
      fullCurrentVertex fullCurrentOutside fullCurrentDelta
      fullCurrentGamma fullAdjoined fullAdjoinedExactly fullClosed
      fullOrdered fullStrict =>
      have hbad := fullCurrentKind.symm.trans
        (by simpa [hfullTarget] using hfullPE)
      cases hbad
  | PE fulli fullPreviousProper fullPreviousOne fullPreviousClosed
      fullPreviousNotStrong fullNoRE fullChoice fullAlternativeFails
      fullGamma fullGammaRule fullSecond fullSecondProper fullSecondOne
      fullSecondStable fullExit fullCurrentColoring fullCurrentProper
      fullCurrentOne fullCurrentStored fullCurrentEdges fullCurrentKind
      fullCurrentVertex fullCurrentOutside fullCurrentDelta
      fullCurrentGamma fullClosed fullOrdered fullStrict =>
      have hfullIndex : fulli.succ = fullj := by
        simpa using hfullTarget.symm
      have hnewStep := corr.replacementSeries.certified j
      generalize hnewTarget : j = newTarget at hnewStep
      cases hnewStep with
      | initial triple seedLength initialColoring initialStored
          initialEdges initialKind initialVertex initialOutside
          initialDelta initialGamma initialClosure =>
          have hbad := initialKind.symm.trans
            (by simpa [hnewTarget] using hjPE)
          simp at hbad
      | SE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newNoRE newChoice newAlternative
          newCurrentColoring newCurrentStored newCurrentEdges
          newCurrentKind newCurrentVertex newCurrentOutside
          newCurrentDelta newCurrentGamma newAdjoined
          newAdjoinedExactly newClosed newOrdered newStrict =>
          have hbad := newCurrentKind.symm.trans
            (by simpa [hnewTarget] using hjPE)
          cases hbad
      | RE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newAvailable newCurrentColoring
          newCurrentStored newCurrentEdges newCurrentKind
          newCurrentVertex newCurrentOutside newCurrentDelta
          newCurrentGamma newAdjoined newAdjoinedExactly newClosed
          newOrdered newStrict =>
          have hbad := newCurrentKind.symm.trans
            (by simpa [hnewTarget] using hjPE)
          cases hbad
      | PE newi newPreviousProper newPreviousOne newPreviousClosed
          newPreviousNotStrong newNoRE newChoice newAlternativeFails
          newGamma newGammaRule newSecond newSecondProper newSecondOne
          newSecondStable newExit newCurrentColoring newCurrentProper
          newCurrentOne newCurrentStored newCurrentEdges newCurrentKind
          newCurrentVertex newCurrentOutside newCurrentDelta
          newCurrentGamma newClosed newOrdered newStrict =>
              exact @helper_branch_12991 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                  (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar) (@gamma)
                  (@choice) (@sigmaPrev) (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr)
                  (@hprefixTrees) (@hprefixData) (@corr) (@horiginalPositive) (@pePostStatus)
                  (@j) (@fulli) (@fullChoice) (@fullGamma) (@fullGammaRule) (@fullSecond)
                  (@fullSecondProper) (@fullSecondStable) (@fullCurrentColoring)
                  (@fullCurrentStored) (@fullCurrentEdges) (@fullCurrentVertex)
                  (@fullCurrentDelta) (@fullCurrentGamma) (@hfullTarget) (@hfullIndex) (@newi)
                  (@newChoice) (@newGamma) (@newGammaRule) (@newSecond) (@newSecondProper)
                  (@newSecondStable) (@newCurrentColoring) (@newCurrentStored) (@newCurrentEdges)
                  (@newCurrentVertex) (@newCurrentDelta) (@newCurrentGamma) (@hnewTarget)

theorem helper_hpeGammaRuleReplacement_13982.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (_ : TreeSequence G e0),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (previousProper : IsProperEdgeColoring G (ett.series.data.coloring
        q.castSucc)) (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring
        q.castSucc) e0) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc)), ParallelExtensionColor ett.series.data q.castSucc
        choice.selected choice.vertex gamma →
    ∀ (sigmaPrev : PartialEdgeColoring E k) (hsigmaPrevProper : IsProperEdgeColoring G sigmaPrev)
        (hsigmaPrevOne : IsOneEdgeUncolored sigmaPrev e0) (hsigmaPrevStableQ : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev) (hchoiceDefective : DefectiveColor G
        sigmaPrev (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color)
        (hchoiceEdgeNew : choice.edge ∈ BoundaryColorEdges G sigmaPrev (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) choice.color) (hsigmaPrevSelf : StableColoring
        (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors ett.series.data q.castSucc)
        sigmaPrev sigmaPrev), gamma ∈ MissingColors G sigmaPrev choice.vertex →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigmaPrev gamma choice.color; Sum.inr
        choice.edge ∈ TwoColorComponent G sigmaPrev gamma choice.color (Sum.inl choice.vertex) →
    ∀ (u : V) (_ : H.Walk (Sum.inl choice.vertex) (Sum.inl u)), (1 : ℕ) < ett.rounds →
    ∀ (originalPrefix : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (hr : originalPrefix.rounds = ett.rounds - (1 : ℕ)), (
    ∀ (i : Fin (originalPrefix.rounds + (2 : ℕ))), originalPrefix.series.data.tree i =
        ett.series.data.tree (Fin.castLE (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) → (
    ∀ (i : Fin (originalPrefix.rounds + (1 : ℕ))), originalPrefix.series.data.coloring i =
        ett.series.data.coloring (Fin.castLE (
    by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega
    ) i) ∧ originalPrefix.series.data.stored i = ett.series.data.stored (Fin.castLE (
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ) i) ∧ originalPrefix.series.data.connectingEdges i = ett.series.data.connectingEdges
        (Fin.castLE (
    by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega
    ) i) ∧ originalPrefix.series.data.kind i = ett.series.data.kind (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) i) ∧ TashkinovStoredColors originalPrefix.series.data i = TashkinovStoredColors
        ett.series.data (Fin.castLE (
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ) i)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 originalPrefix sigmaPrev
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (hcorrFinalColor :
        corr.replacementSeries.data.coloring (Fin.last originalPrefix.rounds) = sigmaPrev),
    let replacementLast : Fin (originalPrefix.rounds + (1 : ℕ)) := Fin.last originalPrefix.rounds;
        (0 : ℕ) < originalPrefix.rounds →
    ∀ (hreplacementCurrentTree : corr.replacementSeries.data.tree replacementLast.succ =
        ett.series.data.tree q.succ.castSucc) (hreplacementStored : TashkinovStoredColors
        corr.replacementSeries.data replacementLast = TashkinovStoredColors ett.series.data
        q.castSucc),
    let replacementChoice : MaximumDefectiveChoice G e0 (corr.replacementSeries.data.tree
        replacementLast.succ) (TashkinovStoredColors corr.replacementSeries.data replacementLast)
        (corr.replacementSeries.data.coloring replacementLast) := helperReplacementChoice5196 G k
        e0 input T generating ett hpositive previousProper previousOneUncolored choice sigmaPrev
        hsigmaPrevProper hsigmaPrevOne hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew
        hsigmaPrevSelf originalPrefix corr hcorrFinalColor hreplacementCurrentTree
        hreplacementStored; ParallelExtensionColor corr.replacementSeries.data replacementLast
        replacementChoice.selected replacementChoice.vertex gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive Tstar q gamma previousProper
      previousOneUncolored choice gammaRule sigmaPrev hsigmaPrevProper hsigmaPrevOne
      hsigmaPrevStableQ hchoiceDefective hchoiceEdgeNew hsigmaPrevSelf hgammaPrevMissing H
      hedgeComponent u p hroundLarge originalPrefix hr hprefixTrees hprefixData corr
      hcorrFinalColor replacementLast horiginalPositive hreplacementCurrentTree
      hreplacementStored replacementChoice
  have retainedKind : ∀ j : Fin (originalPrefix.rounds + 1),
      corr.replacementSeries.data.kind j =
        ett.series.data.kind (Fin.castLE (by omega) j) := by
    intro j
    exact (corr.extensionKindsAgree j).trans
      (hprefixData j).2.2.2.1
  have pePostStatus := @helper_pePostStatus_12865 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@gamma) (@choice) (@sigmaPrev) (@hedgeComponent)
  have retainedPEFields := @helper_retainedPEFields_13584 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@Tstar)
      (@gamma) (@previousProper) (@previousOneUncolored) (@choice) (@sigmaPrev) (@hsigmaPrevProper)
      (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective) (@hchoiceEdgeNew) (@hsigmaPrevSelf)
      (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr) (@hprefixTrees) (@hprefixData) (@corr)
      (@horiginalPositive) (@retainedKind) (@pePostStatus)
  refine ⟨?_, ?_⟩
  · simpa [replacementChoice] using hgammaPrevMissing
  · exact @helper_branch_6368 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hpositive) (@gamma) (@previousProper)
      (@previousOneUncolored) (@choice) (@gammaRule) (@sigmaPrev) (@hsigmaPrevProper)
      (@hsigmaPrevOne) (@hsigmaPrevStableQ) (@hchoiceDefective) (@hchoiceEdgeNew)
      (@hsigmaPrevSelf) (@u) (@p) (@hroundLarge) (@originalPrefix) (@hr) (@corr)
      (@hcorrFinalColor) (@horiginalPositive) (@hreplacementCurrentTree) (@hreplacementStored)
      (@retainedKind) (@retainedPEFields)

end GoldbergSeymour.TerminalSeriesRebuild

end
