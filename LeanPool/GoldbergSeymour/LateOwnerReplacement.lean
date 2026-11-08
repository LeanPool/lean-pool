/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceFirstMissingPositionInvariant


public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwoSplitTail
public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.HierarchyTailMissingColorExclusion
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentationTrans
public import LeanPool.GoldbergSeymour.ElementaryTerminalComponent
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# P2905_T2_Late Owner Replacement

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation769Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
    ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount), alpha ∈
        C.good.gamma (Fin.last C.hierarchy.dividerCount) eta →
    ∀ (t : ℕ), (1 : ℕ) ≤ t → (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) =
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + t →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C t; (
    ∀ (i : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C i) T) →
        TreeSequenceInitialSegment A X → TreeSequenceInitialSegment X B → alpha ≠ eta → X.length =
        A.length + t → eta ∈ MissingColors G phi (X.vertex (Fin.last X.length)) → alpha ∈
        TreeMissingColors phi B ∧ eta ∈ TreeMissingColors phi B → (↑(HierarchyFirstMissingPosition
        phi T eta) : ℕ) = A.length + t → (0 : ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors phi
        (H.stage (⟨H.dividerCount,
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∨ alpha ∈ TreeMissingColors phi
        A ∧ alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) ∧ eta ∉
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) → X.vertex (Fin.last
        X.length) ∈ TreeSequenceVertexSet B → T.vertex (Fin.last T.length) ≠ X.vertex (Fin.last
        X.length) → Disjoint (TwoColorComponent G phi alpha eta (Sum.inl (T.vertex (Fin.last
        T.length)))) (TwoColorComponent G phi alpha eta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition phi T alpha)))) → TwoColorPathComponent G phi alpha eta
        (Sum.inl (T.vertex (Fin.last T.length))) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi alpha eta (Sum.inl
        (T.vertex (Fin.last T.length)))) x = MissingColors G phi x) →
    let w : V := T.vertex (Fin.last T.length);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha eta (Sum.inl w);
        alpha ∈ TreeMissingColors sigma X ∧ eta ∈ TreeMissingColors sigma X →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (
    ∀ (r : Fin T.length), A.length ≤ (↑r : ℕ) → (↑r : ℕ) < X.length → sigma (T.edge r) = phi
        (T.edge r)) → (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X ∨ (ett.series.data.kind n = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) →
        TashkinovAugmentationSequence phi X T → (
    ∀ rho ∈ HierarchyStoredColorsAt H q, HierarchyFirstMissingPosition sigma T rho =
        HierarchyFirstMissingPosition phi T rho) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), eta ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ eta ∈ MissingColors G
        P.coloring ((HierarchyFullTailPrefix C t).vertex (Fin.last (HierarchyFullTailPrefix C
        t).length))

private abbrev helperContinuation681Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)),
    ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount), alpha ∈
        C.good.gamma (Fin.last C.hierarchy.dividerCount) eta →
    ∀ (t : ℕ), (1 : ℕ) ≤ t → t < HierarchyFullTailLength C → (↑(HierarchyFirstMissingPosition phi
        T eta) : ℕ) = (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length + t →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C t; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U Z → TreeSequenceInitialSegment W Z
        → U.length ≤ W.length → TreeSequenceInitialSegment U W) → ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T → ell = T.length - A.length →
        A.length + ell = T.length → (
    ∀ (i : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C i) T) →
        TreeSequenceInitialSegment A X → TreeSequenceInitialSegment X B → alpha ≠ eta → X.length =
        A.length + t → B.length = T.length - (1 : ℕ) → eta ∈ MissingColors G phi (X.vertex
        (Fin.last X.length)) → alpha ∈ TreeMissingColors phi B ∧ eta ∈ TreeMissingColors phi B →
        (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) = A.length + t → alpha ∉
        HierarchySegmentColors H q eta → (
    let H : TashkinovHierarchy ett base := C.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
                              have := GoldbergSeymour.TreeSequence.positive T
                              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    have vb : V := T.vertex (HierarchyFirstMissingPosition phi T eta);
    have sameComponent : Prop := TwoColorComponent G phi alpha eta (Sum.inl va) =
        TwoColorComponent G phi alpha eta (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (alpha ∈
        TreeMissingColors phi Tnq ∨ Disjoint (insert alpha ({ eta } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi Tn ∨ Disjoint (insert alpha ({ eta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (alpha ∈ TreeMissingColors phi A ∧ TreeColorSetClosed G phi A ({ alpha }
        : Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A phi alpha eta)) →
        (H.dividerCount = (0 : ℕ) → alpha ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last
        ett.rounds).castSucc)) → (H.dividerCount ≠ (0 : ℕ) → alpha ∈ TreeMissingColors phi
        (H.stage (⟨H.dividerCount,
    by
                                  have := GoldbergSeymour.TreeSequence.positive T
                                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))))) → (0 : ℕ) < H.dividerCount ∧ alpha ∈ TreeMissingColors
        phi (H.stage (⟨H.dividerCount,
    by
                                    have := GoldbergSeymour.TreeSequence.positive T
                                    omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∨ alpha ∈ TreeMissingColors phi
        A ∧ alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) ∧ eta ∉
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) → X.vertex (Fin.last
        X.length) ∈ TreeSequenceVertexSet B → T.vertex (Fin.last T.length) ≠ X.vertex (Fin.last
        X.length) → Disjoint (TwoColorComponent G phi alpha eta (Sum.inl (T.vertex (Fin.last
        T.length)))) (TwoColorComponent G phi alpha eta (Sum.inl (T.vertex
        (HierarchyFirstMissingPosition phi T alpha)))) → TwoColorPathComponent G phi alpha eta
        (Sum.inl (T.vertex (Fin.last T.length))) → (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi alpha eta (Sum.inl
        (T.vertex (Fin.last T.length)))) x = MissingColors G phi x) →
    let w : V := T.vertex (Fin.last T.length);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha eta (Sum.inl w);
        alpha ∈ TreeMissingColors sigma X ∧ eta ∈ TreeMissingColors sigma X →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), eta ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ eta ∈ MissingColors G
        P.coloring ((HierarchyFullTailPrefix C t).vertex (Fin.last (HierarchyFullTailPrefix C
        t).length))

private abbrev helperContinuation649Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
    ∀ alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)), alpha ∈ TreeMissingColors phi
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) →
    ∀ eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount), alpha ∈
        C.good.gamma (Fin.last C.hierarchy.dividerCount) eta →
    ∀ (t : ℕ), (1 : ℕ) ≤ t → t < HierarchyFullTailLength C → (↑(HierarchyFirstMissingPosition phi
        T eta) : ℕ) = (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)).length + t →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C t; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U Z → TreeSequenceInitialSegment W Z
        → U.length ≤ W.length → TreeSequenceInitialSegment U W) → ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T → (3 : ℕ) ≤ ell → ell =
        T.length - A.length → A.length + ell = T.length → (
    ∀ (i : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C i) T) →
        TreeSequenceInitialSegment A B → TreeSequenceInitialSegment A X →
        TreeSequenceInitialSegment X B → alpha ≠ eta → X.length = A.length + t → B.length =
        T.length - (1 : ℕ) → eta ∈ MissingColors G phi (X.vertex (Fin.last X.length)) → alpha ∈
        TreeMissingColors phi B ∧ eta ∈ TreeMissingColors phi B → (↑(HierarchyFirstMissingPosition
        phi T alpha) : ℕ) ≤ A.length → (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) = A.length
        + t → alpha ∉ HierarchySegmentColors H q eta → (alpha ∉ TreeMissingColors phi A ∨ eta ∉
        TreeMissingColors phi A → TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T
        alpha)) (T.vertex (HierarchyFirstMissingPosition phi T eta)) ∧ alpha ∉ ({c : Fin k |
    ∃ (r : Fin T.length), A.length ≤ (↑r : ℕ) ∧ (↑r : ℕ) < (↑(HierarchyFirstMissingPosition phi T
        eta) : ℕ) ∧ phi (T.edge r) = some c} : Finset (Fin k))) →
    ∃ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), eta ∈
        MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧ eta ∈ MissingColors G
        P.coloring ((HierarchyFullTailPrefix C t).vertex (Fin.last (HierarchyFullTailPrefix C
        t).length))

private theorem helper_sourceRoute_458.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ eta :
        Fin k) (t : ℕ) (_ : (1 : ℕ) ≤ t) (_ : (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) =
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + t),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C t;
    ∀ (_ : (
    ∀ {U W Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment U Z) (_ :
        TreeSequenceInitialSegment W Z) (_ : U.length ≤ W.length), TreeSequenceInitialSegment U
        W)) (_ : (
    ∀ (i : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C i) T)) (_ :
        TreeSequenceInitialSegment A X) (_ : X.length = A.length + t) (_ : (
    ∀ {U W Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment U W) (_ :
        TreeSequenceInitialSegment W Z), TreeSequenceInitialSegment U Z)) (_ : (
    ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)), TreeSequenceInitialSegment (H.stage
        (⟨a, Decidable.byContradiction fun (a_1 : ¬a < H.dividerCount + (2 : ℕ)) ↦
    by
                    omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) (H.stage (⟨a + d, Decidable.byContradiction fun (a_1 : ¬a
        + d < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))))),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : TreeSequenceInitialSegment Tn (HierarchyFullTailPrefix C t)) (_ : (ett.series.data.kind
        (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) T ∨ (ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last ett.rounds)
        = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges (Fin.last ett.rounds) =
        { f } ∧ TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f
        seed ∧ TreeIncidentEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f ∧ (
    ∃ c ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∪
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds), phi f = some c) ∧
        TashkinovAugmentationSequence phi seed T)), ett.series.data.kind n = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence phi Tn T ∧
        TreeSequenceInitialSegment Tn X ∨ (ett.series.data.kind n = some TashkinovExtensionKind.SE
        ∨ ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges n = { f } ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed T ∧
        TreeSequenceInitialSegment seed X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha eta t htpos hfirst H q A X commonPrefix
      hprefixT hAX hXlen segTrans stageSegment n Tn TnToX terminalRoute
  rcases terminalRoute with ⟨hp, hroute⟩ | ⟨hk, f, seed, hedges, hadjoin,
      hincident, hcolor, hroute⟩
  · exact Or.inl ⟨hp, hroute, TnToX⟩
  · have hseedT := TashkinovAugmentationSequenceInitialSegment phi seed T hroute
    by_cases hz : H.dividerCount = 0
    · have hA : A = Tn := by
        have hpPE : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
          intro hp
          rcases hk with hk | hk
          · rw [hk] at hp
            cases hp
          · rw [hk] at hp
            cases hp
        have hAcore : A = base.core := by
          change HierarchyStarredStage H q = base.core
          have hq : q = 0 := by
            apply Fin.ext
            simp [q, hz]
          rw [hq]
          rfl
        exact hAcore.trans (base.nonparallel hpPE)
      have hlen := hadjoin.1
      change seed.length = Tn.length + 1 at hlen
      have hSXlen : seed.length ≤ X.length := by
        have heq : Tn.length = A.length := congrArg TreeSequence.length hA.symm
        rw [heq] at hlen
        rw [hlen, hXlen]
        omega
      exact Or.inr ⟨hk, f, seed, hedges, hadjoin, hroute,
        commonPrefix hseedT (hprefixT t) hSXlen⟩
    · obtain ⟨r, hr⟩ := by
        have hqsucc : ∃ r : Fin H.dividerCount, q = r.succ := by
          refine ⟨⟨H.dividerCount - 1, by omega⟩, ?_⟩
          apply Fin.ext
          simp [q]
          omega
        exact hqsucc
      have hfirstEdge := HierarchyNonparallelFirstEdge H f hk hedges
      obtain ⟨edgePos, heval, hedge⟩ := hfirstEdge
      have hstage1T : TreeSequenceInitialSegment
          (H.stage ⟨1, by omega⟩) T := by
        have hst := stageSegment 1 H.dividerCount (by omega)
        have hidx : (⟨1 + H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
            Fin.last (H.dividerCount + 1) := by
          apply Fin.ext
          simp
          omega
        rw [hidx] at hst
        simpa [H.terminalStage] using hst
      have hseedLen := hadjoin.1
      change seed.length = Tn.length + 1 at hseedLen
      have hstrict : Tn.length < (H.stage ⟨1, by omega⟩).length := by
        have hh := edgePos.isLt
        change edgePos.val < (H.stage ⟨1, by omega⟩).length at hh
        rw [heval] at hh
        exact hh
      have hseedStage : TreeSequenceInitialSegment seed (H.stage ⟨1, by omega⟩) :=
        commonPrefix hseedT hstage1T (by rw [hseedLen]; omega)
      have hstageA : TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩) A := by
        have hstage := stageSegment 1 (H.dividerCount - 1) (by omega)
        have hsum : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
        have hstage' : TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩)
            (H.stage ⟨H.dividerCount, by omega⟩) := by
          simpa [hsum] using hstage
        have hidx : r.succ.castSucc =
            (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := by
          apply Fin.ext
          have hh := congrArg Fin.val hr
          simp [q] at hh ⊢
          omega
        have hA : A = H.stage ⟨H.dividerCount, by omega⟩ := by
          calc
            A = HierarchyStarredStage H q := rfl
            _ = HierarchyStarredStage H r.succ := by rw [hr]
            _ = H.stage r.succ.castSucc := rfl
            _ = H.stage ⟨H.dividerCount, by omega⟩ := congrArg H.stage hidx
        simpa [hA] using hstage'
      have hseedA := segTrans hseedStage hstageA
      exact Or.inr ⟨hk, f, seed, hedges, hadjoin, hroute,
        segTrans hseedA hAX⟩

private theorem helper_hfixedPrefix_551.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha eta
        : Fin k) (t : ℕ) (_ : (1 : ℕ) ≤ t) (_ : t < HierarchyFullTailLength C),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C t;
    ∀ (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B)) (_ : (
    ∀ (i : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C i) T)) (_ : X.length =
        A.length + t) (_ : eta ∈ MissingColors G phi (X.vertex (Fin.last X.length))) (_ :
        (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) = A.length + t) (_ : alpha ∉
        HierarchySegmentColors H q eta),
    let w : V := T.vertex (Fin.last T.length);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha eta (Sum.inl w);
    ∀ (_ : (if ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE then
        CombinedStableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc) base.closure
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma else
        StableColoring (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma)),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ (_ : (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) T
        ∨ (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges (Fin.last ett.rounds) =
        { f } ∧ TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f
        seed ∧ TreeIncidentEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f ∧ (
    ∃ c ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∪
        TashkinovStoredColors ett.series.data (Fin.last ett.rounds), phi f = some c) ∧
        TashkinovAugmentationSequence phi seed T)) (_ : H.stage q.succ = T) (r : Fin T.length) (_
        : A.length ≤ (↑r : ℕ)) (_ : (↑r : ℕ) < X.length), sigma (T.edge r) = phi (T.edge r) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha eta t htpos htupper H q A ell B X hB
      hprefixT hXlen hXmissingEta hposEta hnotSegment w sigma hbase n Tn terminalRoute
      hstageTerminal r hrA hrX
  have halphaNot : phi (T.edge r) ≠ some alpha := by
    intro hc
    apply hnotSegment
    have hseg : alpha ∈ HierarchySegmentColors H q eta := by
      rw [HierarchySegmentColors, hstageTerminal]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨r, hrA, ?_, hc⟩
      have hrFirst : r.val < (HierarchyFirstMissingPosition phi T eta).val := by
        rw [hposEta]
        rw [hXlen] at hrX
        exact lt_of_lt_of_le hrX (by omega)
      exact lt_min hrFirst r.isLt
    exact hseg
  by_cases hetaColor : phi (T.edge r) = some eta
  · let rX : Fin X.length := ⟨r.val, hrX⟩
    have hrCast : Fin.castLE (hprefixT t).1 rX = r := Fin.ext rfl
    have hEdge : X.edge rX = T.edge r := by
      rw [← hrCast]
      exact (hprefixT t).2.2 rX |>.symm
    have hEtaColorX : phi (X.edge rX) = some eta := by rw [hEdge]; exact hetaColor
    have exception := HierarchyTailMissingColorExclusion G k e0 input T phi ett
      base H hB t htpos htupper eta hXmissingEta rX hrA (by
        have hx : r.val < A.length + t := by
          rw [← hXlen]
          exact hrX
        simpa [rX] using hx) hEtaColorX
    obtain ⟨hz, hcore, hindex, fTail, hstep, hkind, hconn, hedgeTail,
      hcolorTail, hstoredTail⟩ := exception
    have hnotPE : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
      intro hp
      rcases hkind with hse | hre
      · rw [hp] at hse
        cases hse
      · rw [hp] at hre
        cases hre
    have hstableTn : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) phi sigma := by
      change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure
          (TashkinovStoredColors ett.series.data n) phi sigma
      else StableColoring Tn (TashkinovStoredColors ett.series.data n) phi sigma)
        at hbase
      simpa [hnotPE] using hbase
    rcases terminalRoute with ⟨hp, _⟩ | ⟨_, fRoute, _, hconnRoute, _, hincident, _, _⟩
    · exact (hnotPE hp).elim
    · have hfEq : fTail = fRoute :=
        Finset.singleton_inj.mp (hconn.symm.trans hconnRoute)
      have hincidentTail : TreeIncidentEdge Tn fTail := by
        rw [hfEq]
        exact hincident
      have hfix := hstableTn.1 fTail hincidentTail
        ⟨eta, Finset.mem_union_right _ hstoredTail, hcolorTail⟩
      have hTedge : T.edge r = fTail := hEdge.symm.trans hedgeTail
      rw [hTedge]
      exact hfix
  · simp [sigma, TwoColorComponentSwap, halphaNot, hetaColor]

private theorem helper_hrouteTransport_610.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha eta
        : Fin k) (t : ℕ) (_ : (1 : ℕ) ≤ t) (_ : (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) =
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + t),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength C;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
    let X : TreeSequence G e0 := HierarchyFullTailPrefix C t;
    ∀ (_ : TreeSequenceInitialSegment A T) (_ : (
    ∀ (i : ℕ), TreeSequenceInitialSegment (HierarchyFullTailPrefix C i) T)) (_ :
        TreeSequenceInitialSegment X B) (_ : X.length = A.length + t) (_ :
        (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) = A.length + t) (_ : (
    ∀ x ∈ TreeSequenceVertexSet B, MissingColors G (TwoColorComponentSwap G phi alpha eta (Sum.inl
        (T.vertex (Fin.last T.length)))) x = MissingColors G phi x)),
    let w : V := T.vertex (Fin.last T.length);
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha eta (Sum.inl w);
    ∀ (_ : (
    have A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    ∀ (t : Fin A.length), sigma (A.edge t) = phi (A.edge t))) (_ : (
    ∀ (r : Fin T.length) (_ : A.length ≤ (↑r : ℕ)) (_ : (↑r : ℕ) < X.length), sigma (T.edge r) =
        phi (T.edge r))) (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence phi S T) (_ :
        TreeSequenceInitialSegment S X), TashkinovAugmentationSequence sigma S X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha eta t htpos hfirst H q A ell B X hAT
      hprefixT hXB hXlen hposEta hpenultimateMissing w sigma hfixedA hfixedPrefix S hroute hSX
  let Xminus := TreeSequencePrefix X (X.length - 1)
    (by have := A.positive; rw [hXlen]; omega)
    (by omega)
  have hminusX : TreeSequenceInitialSegment Xminus X := by
    refine ⟨by dsimp [Xminus, TreeSequencePrefix]; omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hminusLen : X.length = Xminus.length + 1 := by
    dsimp [Xminus, TreeSequencePrefix]
    omega
  have hfixedX : ∀ i : Fin X.length,
      sigma (X.edge i) = phi (X.edge i) := by
    intro i
    let r : Fin T.length := Fin.castLE (hprefixT t).1 i
    have hr : r.val = i.val := rfl
    have hedge : T.edge r = X.edge i := (hprefixT t).2.2 i
    rw [← hedge]
    by_cases hiA : i.val < A.length
    · let j : Fin A.length := ⟨i.val, hiA⟩
      have hAj : Fin.castLE hAT.1 j = r := Fin.ext rfl
      rw [← hAj, hAT.2.2 j]
      exact hfixedA j
    · have hrA : A.length ≤ r.val := by rw [hr]; omega
      have hrX : r.val < X.length := by rw [hr]; exact i.isLt
      exact hfixedPrefix r hrA hrX
  have hmissingXminus : ∀ v, v ∈ TreeSequenceVertexSet Xminus →
      MissingColors G sigma v = MissingColors G phi v := by
    intro v hv
    exact hpenultimateMissing v
      (TreeSequenceInitialSegmentVertexSetSubset hXB
        (TreeSequenceInitialSegmentVertexSetSubset hminusX hv))
  have hrouteSX := TashkinovAugmentationSequenceRestrict phi S X T hroute
    hSX (hprefixT t)
  exact TashkinovAugmentationSequenceColoringTransport phi sigma S Xminus X
    hrouteSX hminusX hminusLen (by
      intro i _
      exact hfixedX i) hmissingXminus

private theorem helper_continuation_769.{u_1, u_2} :
    helperContinuation769Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha hterminal eta heta hgamma t htpos
      hfirst H q A ell B X hprefixT hAX hXB hne hXlen hXmissingEta hmissingB hposEta hcase vB
      htermNeV hdisjoint hpath hpenultimateMissing w sigma hsplitMissing n Tn hfixedPrefix
      hrouteX hsuffix hstoredFirst
  have hgammaCutoff : ∀ rho, rho ∈ HierarchyStoredColorsAt H q →
      (alpha ∈ C.good.gamma q rho ∨ eta ∈ C.good.gamma q rho) →
        (HierarchyFirstMissingPosition phi T rho).val ≤ X.length := by
    have hreserved := GoodHierarchyReservedDisjoint C.good q
    intro rho hrho haffected
    rcases haffected with ha | hetaGamma
    · by_cases heq : rho = eta
      · subst rho
        rw [hposEta, hXlen]
      · have hdisj := C.good.disjointPairs q rho eta hrho heta heq
        exact False.elim (Finset.disjoint_left.mp hdisj ha hgamma)
    · have hm : eta ∈
          (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) :=
        Finset.mem_biUnion.mpr ⟨rho, hrho, hetaGamma⟩
      exact False.elim (Finset.disjoint_left.mp hreserved.2 hm heta)
  have splitTail := StableChangeCasesOneTwoSplitTail G k e0 input T phi ett
    base C ctx alpha eta hne hmissingB (Sum.inl w) hpath sigma rfl hcase
    hdisjoint X hAX (by rw [hXlen]; have := A.positive; omega) hXB
    hfixedPrefix hrouteX hsuffix hsplitMissing hpenultimateMissing
    hstoredFirst hgammaCutoff
  obtain ⟨hweakFinal, hmodFinal, corrT, hmaximumT, baseT, K, goodT,
    hsameGood⟩ := splitTail
  have seriesProper : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) := by
    intro j
    exact (ett.series.coloringProperties j).1
  have seriesOne : ∀ j : Fin (ett.rounds + 1),
      IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    intro j
    exact (ett.series.coloringProperties j).2
  let selfCorr : CorrespondingExtendedTashkinovTree G k e0 ett phi T := {
    replacementInput := input
    replacementSeries := ett.series
    replacementETT := ett
    rungAgreement := rfl
    seriesPresentation := HEq.rfl
    finalGeneratingColoring := ett.generatingColoring
    ladderTreesAgree := fun _ => rfl
    storedColorsAgree := fun _ => rfl
    connectingEdgesAgree := fun _ => rfl
    extensionKindsAgree := fun _ => rfl
    replacementProper := seriesProper
    replacementOneUncolored := seriesOne
    replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  let P0 : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx := {
    coloring := phi
    corresponding := selfCorr
    maximum := C.maximum
    replacementBase := base
    counterexample := C
    sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
      rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
    minimumContext := ctx }
  have hterminalEta : eta ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) := by
    have hbehavior := TwoColorComponentSwapMissingBehavior G phi alpha eta hne
      ctx.proper (Sum.inl (T.vertex (Fin.last T.length)))
    have hroot : Sum.inl (T.vertex (Fin.last T.length)) ∈
        TwoColorComponent G phi alpha eta (Sum.inl (T.vertex (Fin.last T.length))) := by
      change Sum.inl (T.vertex (Fin.last T.length)) ∈
        (TwoColorIncidenceGraph G phi alpha eta).connectedComponentMk
          (Sum.inl (T.vertex (Fin.last T.length)))
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    have h := hbehavior.2.1 (T.vertex (Fin.last T.length)) hroot hterminal
    simpa [sigma] using h
  have hXetaSigma : eta ∈ MissingColors G sigma (X.vertex (Fin.last X.length)) := by
    rw [hpenultimateMissing _ vB]
    exact hXmissingEta
  let CSecond : HierarchyCounterexample baseT := {
    positive := by rw [corrT.rungAgreement]; exact C.positive
    hierarchy := K
    good := goodT
    maximum := hmaximumT
    notElementary := by
      intro helem
      have hw : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet T := by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨Fin.last T.length, rfl⟩
      have hx : X.vertex (Fin.last X.length) ∈ TreeSequenceVertexSet T :=
        TreeSequenceInitialSegmentVertexSetSubset (hprefixT t) (by
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
            true_and]
          exact ⟨Fin.last X.length, rfl⟩)
      exact (Finset.disjoint_left.mp (helem hw hx htermNeV)
        hterminalEta hXetaSigma) }
  obtain ⟨P, hPcolor⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx P0 sigma corrT baseT CSecond (by
      dsimp only [P0, CSecond]
      exact hsameGood)
  refine ⟨P, ?_, ?_⟩
  · rw [hPcolor]
    exact hterminalEta
  · rw [hPcolor]
    exact hXetaSigma

private theorem helper_continuation_681.{u_1, u_2} :
    helperContinuation681Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha hterminal eta heta hgamma t htpos
      htupper hfirst H q A ell B X commonPrefix hB hAT hEll hEllAdd hprefixT hAX hXB hne hXlen
      hBlen hXmissingEta hmissingB hposEta hnotSegment hchange hAlphaTn hAlphaTnq hcase vB
      htermNeV hdisjoint hpath hpenultimateMissing w sigma hsplitMissing
  have hchangeCases := StableChangeCasesOneTwo G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hB ctx.largeMissingSet alpha eta hne hmissingB
    (Sum.inl w) hpath sigma rfl hcase hdisjoint
  obtain ⟨hweak, hmod, _, _⟩ := hchangeCases
  have controls := P2813_T1_BaseControl G k e0 input T phi ett base C ctx
    hB alpha eta hne hmissingB (Sum.inl w) hpath sigma rfl hcase hdisjoint
  obtain ⟨hbase, _, hsproper, hsone, houtside⟩ := controls
  have preStepElementary :
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by
        have := C.positive
        omega⟩
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
    dsimp only
    by_cases hn : ett.rounds = 1
    · have hi : (⟨ett.rounds - 1, by omega⟩ : Fin ett.rounds).castSucc = 0 :=
        Fin.ext (by simp [hn])
      have ht : (Fin.last ett.rounds).castSucc =
          (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := Fin.ext (by simp [hn])
      rw [hi, ht]
      exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    · have hm : 1 < ett.rounds := by have := C.positive; omega
      obtain ⟨pred, hpred, hmax, _, _⟩ :=
        CertifiedETTPredecessor G k e0 input T phi ett C.maximum hm
      have ht : (Fin.last ett.rounds).castSucc =
          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := Fin.ext rfl
      rw [ht]
      exact (ctx.lowerRung pred (by omega) (by omega) hmax).1
  have hfixedA := P2813_T1_DisplayedEdges G k e0 input T phi ett base H C.good
    ctx.proper ctx.oneEdgeUncolored preStepElementary hB alpha eta (Sum.inl w)
    sigma rfl hsone hbase houtside
  have segTrans {U W Z : TreeSequence G e0}
      (hUW : TreeSequenceInitialSegment U W)
      (hWZ : TreeSequenceInitialSegment W Z) : TreeSequenceInitialSegment U Z := by
    exact hUW.trans hWZ
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    exact H.stageInitialSegmentOfLE _ _ (by change a ≤ a + d; exact Nat.le_add_right _ _)
  have coreToA := H.coreInitialSegmentOfStarredStage (Fin.last H.dividerCount)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    exact base.lastRoundInitialSegmentCore
  have TnToA := segTrans TnToCore coreToA
  have TnToX := commonPrefix (segTrans TnToA hAT) (hprefixT t)
    (TnToA.1.trans hAX.1)
  have terminalRoute := P2813_T1_TerminalRoute G k e0 input T phi ett
  dsimp only at terminalRoute
  have sourceRoute := @helper_sourceRoute_458 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C alpha eta t htpos hfirst commonPrefix hprefixT hAX
      hXlen segTrans stageSegment TnToX terminalRoute
  have hstageTerminal : H.stage q.succ = T := by
    have hidx : q.succ = Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      rfl
    rw [hidx, H.terminalStage]
  have hfixedPrefix := @helper_hfixedPrefix_551 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C alpha eta t htpos htupper hB hprefixT hXlen
      hXmissingEta hposEta hnotSegment hbase terminalRoute hstageTerminal
  have hrouteTransport := @helper_hrouteTransport_610 V E inferInstance inferInstance inferInstance
      inferInstance G k e0 input T phi ett base C alpha eta t htpos hfirst hAT hprefixT hXB hXlen
      hposEta hpenultimateMissing hfixedA hfixedPrefix
  have hrouteX :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ett.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) := by
    rcases sourceRoute with ⟨hp, hroute, hSX⟩ | ⟨hk, f, seed, hconn, hadjoin,
        hroute, hSX⟩
    · exact Or.inl ⟨hp, hrouteTransport Tn hroute hSX⟩
    · exact Or.inr ⟨hk, f, seed, hconn, hadjoin, hrouteTransport seed hroute hSX⟩
  have hsuffix : TashkinovAugmentationSequence phi X T := by
    rcases sourceRoute with ⟨hp, hroute, hSX⟩ | ⟨hk, f, seed, hconn, hadjoin,
        hroute, hSX⟩
    · exact TashkinovAugmentationSequenceSuffix phi Tn X T hroute hSX (hprefixT t)
    · exact TashkinovAugmentationSequenceSuffix phi seed X T hroute hSX (hprefixT t)
  have hstoredFirst : ∀ rho, rho ∈ HierarchyStoredColorsAt H q →
      HierarchyFirstMissingPosition sigma T rho =
        HierarchyFirstMissingPosition phi T rho := by
    intro rho _
    exact T.firstMissingPosition_eq_of_prefix_agreement
      (show TreeSequenceInitialSegment B T from hprefixT (ell - 1))
      (by rw [hBlen]; exact (Nat.sub_add_cancel T.positive).ge) hpenultimateMissing rho
  exact @helper_continuation_769 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@alpha)
      (@hterminal) (@eta) (@heta) (@hgamma) (@t) (@htpos) (@hfirst) (@hprefixT) (@hAX) (@hXB)
      (@hne) (@hXlen) (@hXmissingEta) (@hmissingB) (@hposEta) (@hcase) (@vB) (@htermNeV)
      (@hdisjoint) (@hpath) (@hpenultimateMissing) (@hsplitMissing) (@hfixedPrefix) (@hrouteX)
      (@hsuffix) (@hstoredFirst)
private theorem helper_continuation_649.{u_1, u_2} :
    helperContinuation649Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx alpha hterminal hstar eta heta hgamma t
      htpos htupper hfirst H q A ell B X commonPrefix hB hAT htail hEll hEllAdd hprefixT hAB hAX
      hXB hne hXlen hBlen hXmissingEta hmissingB alphaFirstBound hposEta hnotSegment horderedUnused
  have hchange := ChangeLemma G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hB ctx.largeMissingSet alpha eta hne hmissingB
    horderedUnused
  have hGammaStage : alpha ∈ HierarchyStageMissingColors H q := by
    have hav := C.good.avoidance q eta heta
    exact (Finset.mem_sdiff.mp (hav hgamma)).1
  have hAlphaTn : H.dividerCount = 0 → alpha ∈ TreeMissingColors phi
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
    intro hz
    have hq : q = 0 := by
      apply Fin.ext
      simp [q, hz]
    rw [hq] at hGammaStage
    simp only [HierarchyStageMissingColors, Fin.cases] at hGammaStage
    exact hGammaStage
  have hAlphaTnq : ∀ (_ : H.dividerCount ≠ 0),
      alpha ∈ TreeMissingColors phi
        (H.stage ⟨H.dividerCount, by omega⟩) := by
    intro hz
    have hqsucc : ∃ r : Fin H.dividerCount, q = r.succ := by
      refine ⟨⟨H.dividerCount - 1, by omega⟩, ?_⟩
      apply Fin.ext
      simp [q]
      omega
    obtain ⟨r, hr⟩ := hqsucc
    rw [hr] at hGammaStage
    change alpha ∈ TreeMissingColors phi (H.stage r.succ.castSucc) at hGammaStage
    have hidx : r.succ.castSucc = (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := by
      apply Fin.ext
      have := congrArg Fin.val hr
      simp [q] at this ⊢
      omega
    simpa [hidx] using hGammaStage
  have hcase :
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors phi
          (H.stage ⟨H.dividerCount, by omega⟩)) ∨
        (H.dividerCount = 0 ∧
          (alpha ∈ TreeMissingColors phi (ett.series.data.tree
              (Fin.last ett.rounds).castSucc) ∨
            (alpha ∈ TreeMissingColors phi A ∧
              alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) ∧
              eta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)))) := by
    by_cases hz : H.dividerCount = 0
    · right
      refine ⟨hz, ?_⟩
      exact Or.inl (hAlphaTn hz)
    · exact Or.inl ⟨Nat.pos_of_ne_zero hz, hAlphaTnq hz⟩
  have hsame : TwoColorComponent G phi alpha eta
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T alpha))) =
      TwoColorComponent G phi alpha eta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T eta))) := by
    dsimp only at hchange
    by_cases hz : H.dividerCount = 0
    · exact hchange.2.1 ⟨hz, Or.inl (hAlphaTn hz)⟩
    · exact hchange.1 ⟨Nat.pos_of_ne_zero hz, Or.inl (hAlphaTnq hz)⟩
  have hfirstAlpha : alpha ∈ MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T alpha)) := by
    have positive : 0 < ell := (by decide : 0 < 3).trans_le htail
    have strict : A.length < T.length := by
      simpa only [Nat.add_zero, hEllAdd] using Nat.add_lt_add_left positive A.length
    exact TreeSequenceFirstMissingPositionMem (alphaFirstBound.trans_lt strict)
  have uB : T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
      TreeSequenceVertexSet B := by
    have hi : (HierarchyFirstMissingPosition phi T alpha).val ≤ A.length := alphaFirstBound
    have hlt : (HierarchyFirstMissingPosition phi T alpha).val < B.length + 1 := by
      rw [hBlen]
      omega
    have ht : TreeSequenceInitialSegment A B := hAB
    have hvertex : T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
        TreeSequenceVertexSet A := by
      obtain ⟨i, hiEq⟩ : ∃ i : Fin (A.length + 1),
          T.vertex (HierarchyFirstMissingPosition phi T alpha) = A.vertex i := by
        refine ⟨⟨(HierarchyFirstMissingPosition phi T alpha).val, Nat.lt_succ_of_le hi⟩, ?_⟩
        have hidx : Fin.castLE (Nat.succ_le_succ hAT.1)
            ⟨(HierarchyFirstMissingPosition phi T alpha).val,
              Nat.lt_succ_of_le hi⟩ = HierarchyFirstMissingPosition phi T alpha := Fin.ext rfl
        rw [← hAT.2.1 ⟨(HierarchyFirstMissingPosition phi T alpha).val,
          Nat.lt_succ_of_le hi⟩, hidx]
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, hiEq.symm⟩
    exact TreeSequenceInitialSegmentVertexSetSubset hAB hvertex
  have vB : X.vertex (Fin.last X.length) ∈ TreeSequenceVertexSet B :=
    TreeSequenceInitialSegmentVertexSetSubset hXB (by simp [TreeSequenceVertexSet])
  have hterminalNotB : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet B := by
    intro hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    have hidx := T.vertex_injective ((hprefixT (ell - 1)).2.1 i |>.symm.trans hi)
    have hvindex : i.val = T.length := by
      have hh := congrArg Fin.val hidx
      change i.val = T.length at hh
      exact hh
    have hi' : i.val < B.length + 1 := i.isLt
    have hlen : B.length + 1 = T.length := by omega
    omega
  have htermNeU : T.vertex (Fin.last T.length) ≠
      T.vertex (HierarchyFirstMissingPosition phi T alpha) := by
    intro heq
    exact hterminalNotB (heq ▸ uB)
  have htermNeV : T.vertex (Fin.last T.length) ≠ X.vertex (Fin.last X.length) := by
    intro heq
    exact hterminalNotB (heq ▸ vB)
  have hVeqFirst : X.vertex (Fin.last X.length) =
      T.vertex (HierarchyFirstMissingPosition phi T eta) := by
    have hvertex := (hprefixT t).2.1 (Fin.last X.length)
    have hidx : Fin.castLE (Nat.succ_le_succ (hprefixT t).1) (Fin.last X.length) =
        HierarchyFirstMissingPosition phi T eta := by
      apply Fin.ext
      simp only [Fin.val_castLE, Fin.val_last]
      rw [hposEta, hXlen]
    rw [hidx] at hvertex
    exact hvertex.symm
  have terminalComponent := P2905_T2_ElementaryTerminalComponent G phi alpha eta hne
    ctx.proper (TreeSequenceVertexSet B) hB
    (T.vertex (HierarchyFirstMissingPosition phi T alpha))
    (X.vertex (Fin.last X.length)) (T.vertex (Fin.last T.length))
    uB vB htermNeU htermNeV hfirstAlpha hXmissingEta (Or.inl hterminal)
    (by simpa only [hVeqFirst] using hsame)
  obtain ⟨hdisjoint, hpath, hpenultimateMissing⟩ := terminalComponent
  let w := T.vertex (Fin.last T.length)
  let sigma := TwoColorComponentSwap G phi alpha eta (Sum.inl w)
  have hsplitMissing : alpha ∈ TreeMissingColors sigma X ∧
      eta ∈ TreeMissingColors sigma X := by
    constructor
    · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hstar
      have hvA : v ∈ TreeSequenceVertexSet A := hv
      have hvB : v ∈ TreeSequenceVertexSet B := TreeSequenceInitialSegmentVertexSetSubset hAB hvA
      have hmNew : alpha ∈ MissingColors G sigma v := by
        rw [hpenultimateMissing v hvB]
        exact hm
      exact Finset.mem_biUnion.mpr ⟨v,
        TreeSequenceInitialSegmentVertexSetSubset hAX hvA, hmNew⟩
    · exact Finset.mem_biUnion.mpr ⟨X.vertex (Fin.last X.length),
        by simp [TreeSequenceVertexSet], by
          rw [hpenultimateMissing (X.vertex (Fin.last X.length)) vB]
          exact hXmissingEta⟩
  exact @helper_continuation_681 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@alpha)
      (@hterminal) (@eta) (@heta) (@hgamma) (@t) (@htpos) (@htupper) (@hfirst) (@commonPrefix)
      (@hB) (@hAT) (@hEll) (@hEllAdd) (@hprefixT) (@hAX) (@hXB) (@hne) (@hXlen) (@hBlen)
      (@hXmissingEta) (@hmissingB) (@hposEta) (@hnotSegment) (@hchange) (@hAlphaTn) (@hAlphaTnq)
      (@hcase) (@vB) (@htermNeV) (@hdisjoint) (@hpath) (@hpenultimateMissing) (@hsplitMissing)
theorem P2905_T2_LateOwnerReplacement {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (alpha : Fin k)
    (hterminal : alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hstar : alpha ∈ TreeMissingColors phi (HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount)))
    (eta : Fin k) (heta : eta ∈ HierarchyStoredColorsAt C.hierarchy (Fin.last
        C.hierarchy.dividerCount))
    (hgamma : alpha ∈ C.good.gamma (Fin.last C.hierarchy.dividerCount) eta)
    (t : ℕ) (htpos : 1 ≤ t) (htupper : t < HierarchyFullTailLength C)
    (_ : HierarchyPathNumber C.hierarchy - 1 ≤ t)
    (hfirst : (HierarchyFirstMissingPosition phi T eta).val =
      (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length + t)
    (hmissing : eta ∈ MissingColors G phi
      ((HierarchyFullTailPrefix C t).vertex
        (Fin.last (HierarchyFullTailPrefix C t).length))) :
    ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      eta ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) ∧
      eta ∈ MissingColors G P.coloring
        ((HierarchyFullTailPrefix C t).vertex
          (Fin.last (HierarchyFullTailPrefix C t).length)) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 1)
  let X := HierarchyFullTailPrefix C t
  have commonPrefix {U W Z : TreeSequence G e0}
      (hUZ : TreeSequenceInitialSegment U Z)
      (hWZ : TreeSequenceInitialSegment W Z) (hUW : U.length ≤ W.length) :
      TreeSequenceInitialSegment U W := by
    rcases hUZ with ⟨hu, huv, hue⟩
    rcases hWZ with ⟨hw, hwv, hwe⟩
    refine ⟨hUW, ?_, ?_⟩
    · intro i
      exact (hwv (Fin.castLE (Nat.succ_le_succ hUW) i)).symm.trans (huv i)
    · intro i
      exact (hwe (Fin.castLE hUW i)).symm.trans (hue i)
  have hB : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi
      ett base C ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have hAT : TreeSequenceInitialSegment A T := by
    have hnext (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ) :=
      Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) i
    simpa [A, q, Fin.succ_last, H.terminalStage] using hnext q
  have htail : 3 ≤ ell := by
    change 2 ≤ HierarchyPathNumber H at hpathLower
    change HierarchyPathNumber H < ell at hpathUpper
    omega
  have hEll : ell = T.length - A.length := by
    rfl
  have hEllAdd : A.length + ell = T.length := by
    change A.length + (T.length - A.length) = T.length
    exact Nat.add_sub_of_le hAT.1
  have hprefixLen (i : ℕ) (hi : i ≤ ell) :
      (HierarchyFullTailPrefix C i).length = A.length + i := by
    change min (A.length + i) T.length = A.length + i
    apply Nat.min_eq_left
    rw [← hEllAdd]
    omega
  have hprefixT (i : ℕ) :
      TreeSequenceInitialSegment (HierarchyFullTailPrefix C i) T := by
    change TreeSequenceInitialSegment (TreeSequencePrefix T _ _ _) T
    exact ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hAB : TreeSequenceInitialSegment A B := by
    have hlen := hprefixLen (ell - 1) (by omega)
    exact commonPrefix hAT (hprefixT _) (by rw [hlen]; omega)
  have hAX : TreeSequenceInitialSegment A X := by
    have hlen := hprefixLen t (by omega)
    exact commonPrefix hAT (hprefixT _) (by rw [hlen]; omega)
  have hXB : TreeSequenceInitialSegment X B := by
    have htlen := hprefixLen t (by omega)
    have hblen := hprefixLen (ell - 1) (by omega)
    exact commonPrefix (hprefixT t) (hprefixT (ell - 1)) (by rw [htlen, hblen]; omega)
  have hne : alpha ≠ eta := by
    intro he
    have hmissA : alpha ∈ TreeMissingColors phi A := by
      simpa [A, q, H] using hstar
    have hnotA : eta ∉ TreeMissingColors phi A := by
      have hstored : eta ∈ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) \
          TreeMissingColors phi A := by
        simpa [HierarchyStoredColorsAt, A, q, H] using heta
      exact (Finset.mem_sdiff.mp hstored).2
    subst alpha
    exact hnotA hmissA
  have hXlen : X.length = A.length + t := by
    change (HierarchyFullTailPrefix C t).length = A.length + t
    exact hprefixLen t (by omega)
  have hBlen : B.length = T.length - 1 := by
    have hp := hprefixLen (ell - 1) (by omega)
    change B.length = A.length + (ell - 1) at hp
    rw [hEll] at hp
    omega
  have hXmissingEta : eta ∈ MissingColors G phi
      (X.vertex (Fin.last X.length)) := by
    change eta ∈ MissingColors G phi
      ((HierarchyFullTailPrefix C t).vertex
        (Fin.last (HierarchyFullTailPrefix C t).length))
    exact hmissing
  have hmissingB : alpha ∈ TreeMissingColors phi B ∧ eta ∈ TreeMissingColors phi B := by
    constructor
    · obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hstar
      exact Finset.mem_biUnion.mpr ⟨v,
        TreeSequenceInitialSegmentVertexSetSubset hAB hv, hm⟩
    · exact Finset.mem_biUnion.mpr ⟨X.vertex (Fin.last X.length),
        TreeSequenceInitialSegmentVertexSetSubset hXB
          (by simp [TreeSequenceVertexSet]), hXmissingEta⟩
  have alphaFirstBound :
      (HierarchyFirstMissingPosition phi T alpha).val ≤ A.length := by
    exact TreeSequenceFirstMissingPositionLePrefix hAT hstar
  have hposEta : (HierarchyFirstMissingPosition phi T eta).val = A.length + t := by
    simpa [A, q, H] using hfirst
  have hfirstOrder : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition phi T alpha))
      (T.vertex (HierarchyFirstMissingPosition phi T eta)) := by
    exact ⟨_, _, rfl, rfl, by rw [hposEta]; omega⟩
  have hnotSegment : alpha ∉ HierarchySegmentColors H q eta := by
    intro hs
    have hav := C.good.avoidance q eta heta
    exact (Finset.mem_sdiff.mp (hav hgamma)).2 hs
  have horderedUnused :
      (alpha ∉ TreeMissingColors phi A ∨ eta ∉ TreeMissingColors phi A) →
      TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T alpha))
          (T.vertex (HierarchyFirstMissingPosition phi T eta)) ∧
        alpha ∉ Finset.univ.filter (fun c => ∃ r : Fin T.length,
          A.length ≤ r.val ∧ r.val < (HierarchyFirstMissingPosition phi T eta).val ∧
            phi (T.edge r) = some c) := by
    intro _
    refine ⟨hfirstOrder, ?_⟩
    intro hmem
    obtain ⟨_, r, hrA, hrpos, hcolor⟩ := Finset.mem_filter.mp hmem
    have hstage : H.stage q.succ = T := by
      rw [show q.succ = Fin.last (H.dividerCount + 1) by
        apply Fin.ext
        rfl, H.terminalStage]
    have hsegment : alpha ∈ HierarchySegmentColors H q eta := by
      rw [HierarchySegmentColors]
      rw [hstage]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨r, hrA, ?_, ?_⟩
      · rw [hposEta]
        have hcut : A.length + t < T.length := by
          rw [← hEllAdd]
          omega
        have hrfirst : r.val < A.length + t := by
          rw [← hposEta]
          exact hrpos
        exact lt_min hrfirst (lt_trans hrfirst hcut)
      · exact hcolor
    exact hnotSegment hsegment
  exact @helper_continuation_649 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@alpha)
      (@hterminal) (@hstar) (@eta) (@heta) (@hgamma) (@t) (@htpos) (@htupper) (@hfirst)
      (@commonPrefix) (@hB) (@hAT) (@htail) (@hEll) (@hEllAdd) (@hprefixT) (@hAB) (@hAX) (@hXB)
      (@hne) (@hXlen) (@hBlen) (@hXmissingEta) (@hmissingB) (@alphaFirstBound) (@hposEta)
      (@hnotSegment) (@horderedUnused)
end GoldbergSeymour

end
