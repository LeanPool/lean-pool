/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.HierarchyClaimNineFirstUseAfterSeed
public import LeanPool.GoldbergSeymour.HierarchyClaimNineUnusedTailColor
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors
public import LeanPool.GoldbergSeymour.TashkinovSeriesNonParallelClosed

/-!
# Hierarchy Claim Nine First Use Seed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable abbrev helperCs1237.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          [Fintype V] →
            [Fintype E] →
              [DecidableEq V] →
                [DecidableEq E] →
                  (G : LooplessMultigraph V E) →
                    (k : ℕ) →
                      (e0 : E) →
                        (input : PartialEdgeColoring E k) →
                          (T : TreeSequence G e0) →
                            (phi : PartialEdgeColoring E k) →
                              (ett : ExtendedTashkinovTree G k e0 input T phi) →
                                (base : HierarchyBase ett phi) →
                                  (C : HierarchyCounterexample base) →
                                    (ctx :
                                        HierarchyMinimumCounterexampleContext G k e0 input T phi ett
                                          base C) →
                                      (P :
                                          HierarchyReplacementPresentation G k e0 input T phi ett
                                            base C ctx) →
                                        (alpha : Fin k) →
                                          let mu : PartialEdgeColoring E k := P.coloring;
                                          let em :
                                            ExtendedTashkinovTree G k e0
                                              P.corresponding.replacementInput T P.coloring :=
                                            P.corresponding.replacementETT;
                                          let Cm : HierarchyCounterexample P.replacementBase :=
                                            P.counterexample;
                                          let H :
                                            TashkinovHierarchy P.corresponding.replacementETT
                                              P.replacementBase :=
                                            Cm.hierarchy;
                                          let q : Fin (H.dividerCount + (1 : ℕ)) :=
                                            Fin.last H.dividerCount;
                                          let A : TreeSequence G e0 := HierarchyStarredStage H q;
                                          let y : V := T.vertex (Fin.last T.length);
                                          TreeSequenceInitialSegment A T →
                                            (gamma : Fin k) →
                                              y ∉ TreeSequenceVertexSet A →
                                                let sigma : PartialEdgeColoring E k :=
                                                  TwoColorComponentSwap G mu gamma alpha
                                                    (Sum.inl y);
                                                gamma ∈ MissingColors G sigma y →
                                                  (corr :
                                                      CorrespondingExtendedTashkinovTree G k e0 em
                                                        sigma T) →
                                                    MaximumProperty corr.replacementETT →
                                                      (bs :
                                                          HierarchyBase corr.replacementETT sigma) →
                                                        (K :
                                                            TashkinovHierarchy corr.replacementETT
                                                              bs) →
                                                          GoodHierarchy K →
                                                            gamma ∈ TreeMissingColors sigma A →
                                                              y ∈ TreeSequenceVertexSet T →
                                                                HierarchyCounterexample bs := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu em Cm H q A y hAT gamma hyNotA
      sigma hgammaNewY corr hmax bs K good hgammaSigmaA hvTerminal
  exact {
    positive := by rw [corr.rungAgreement]; exact Cm.positive
    hierarchy := K
    good := good
    maximum := hmax
    notElementary := by
      intro he
      obtain ⟨v, hvA, hmv⟩ := Finset.mem_biUnion.mp hgammaSigmaA
      have hvT := TreeSequenceInitialSegmentVertexSetSubset hAT hvA
      have hneq : v ≠ y := by
        intro h
        exact hyNotA (h ▸ hvA)
      exact Finset.disjoint_left.mp (he hvT hvTerminal hneq) hmv hgammaNewY }

private abbrev helperContinuation2476Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyPathNumber P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) (e1 : Fin T.length), (↑e1 : ℕ) = (HierarchyStarredStage
        P.counterexample.hierarchy (Fin.last P.counterexample.hierarchy.dividerCount)).length →
        P.coloring (T.edge e1) = some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell →
    ∀ (htwo : (2 : ℕ) ≤ ell) (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1
        : ℕ)),
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    ∀ (gamma : Fin k), gamma ≠ alpha →
    ∀ (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive;
    have this_3 : (1 : ℕ) ≤ A.length := A.positive;
    by
                have := GoldbergSeymour.TreeSequence.positive T
                have := GoldbergSeymour.TreeSequence.positive A
                omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬min
        (A.length + (T.length - A.length - (1 : ℕ))) T.length ≤ T.length) ↦
    by omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length) (hAshort : A.length + (1 : ℕ) < T.length), ((0 : ℕ) < H.dividerCount → A =
        H.stage (⟨H.dividerCount,
    have this : (1 : ℕ) ≤ T.length := T.positive;
    by
                     have := GoldbergSeymour.TreeSequence.positive T
                     omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → (0 : ℕ) < H.dividerCount ∧ gamma ∈ TreeMissingColors mu
        (H.stage (⟨H.dividerCount,
    have this : (1 : ℕ) ≤ T.length := T.positive;
    by
                        have := GoldbergSeymour.TreeSequence.positive T
                        omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
        mu Tn ∨ gamma ∈ TreeMissingColors mu A ∧ gamma ∉ TashkinovStoredColors em.series.data n ∧
        alpha ∉ TashkinovStoredColors em.series.data n) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y);
        gamma ∈ MissingColors G sigma y → sigma (T.edge e1) = mu (T.edge e1) →
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive;
    have this_2 : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (1 : ℕ)) ↦
    by omega
    ) (
    have this : A.length + (1 : ℕ) < T.length := hAshort;
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬A.length +
        (1 : ℕ) ≤ T.length) ↦
    by omega
    ); X.length = A.length + (1 : ℕ) → ModColoring em sigma →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 em sigma T) (bs : HierarchyBase
        corr.replacementETT sigma) (K : TashkinovHierarchy corr.replacementETT bs) (good :
        GoodHierarchy K), SameGoodHierarchy Cm.good good → gamma ∈ TreeMissingColors sigma A →
    ∀ (Pnew : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Pnew.coloring =
        sigma → (
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)), Disjoint (MissingColors G
        Pnew.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C
        i).length))) (MissingColors G Pnew.coloring y)) → HierarchyStarredStage H (Fin.last
        H.dividerCount) = HierarchyStarredStage K (Fin.last K.dividerCount) ∧ HierarchyPathNumber
        H = HierarchyPathNumber K ∧ H.stage (⟨H.dividerCount,
    by
                                  have := GoldbergSeymour.TreeSequence.positive T
                                  omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) = K.stage (⟨K.dividerCount,
    by
                                  have := CorrespondingExtendedTashkinovTree.rungAgreement corr
                                  have := GoldbergSeymour.TreeSequence.positive T
                                  omega
    ⟩ : Fin (K.dividerCount + (2 : ℕ))) → HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount) = HierarchyStarredStage Pnew.counterexample.hierarchy (Fin.last
        Pnew.counterexample.hierarchy.dividerCount) ∧ HierarchyPathNumber C.hierarchy =
        HierarchyPathNumber Pnew.counterexample.hierarchy ∧ C.hierarchy.stage
        (⟨C.hierarchy.dividerCount,
    by
                                   have := GoldbergSeymour.TreeSequence.positive T
                                   omega
    ⟩ : Fin (C.hierarchy.dividerCount + (2 : ℕ))) = Pnew.counterexample.hierarchy.stage
        (⟨Pnew.counterexample.hierarchy.dividerCount,
    by
                                   have := GoldbergSeymour.TreeSequence.positive T
                                   omega
    ⟩ : Fin (Pnew.counterexample.hierarchy.dividerCount + (2 : ℕ))) → HierarchyStarredStage
        C.hierarchy (Fin.last C.hierarchy.dividerCount) = HierarchyStarredStage H (Fin.last
        H.dividerCount) ∧ HierarchyPathNumber C.hierarchy = HierarchyPathNumber H ∧
        C.hierarchy.stage (⟨C.hierarchy.dividerCount,
    by
                                    have := GoldbergSeymour.TreeSequence.positive T
                                    omega
    ⟩ : Fin (C.hierarchy.dividerCount + (2 : ℕ))) = H.stage (⟨H.dividerCount,
    by
                                    have := GoldbergSeymour.TreeSequence.positive T
                                    omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) → HierarchyPathNumber Pnew.counterexample.hierarchy = (1 :
        ℕ) → HierarchyStarredStage H q = HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount) → (HierarchyStarredStage K (Fin.last
        K.dividerCount)).length = A.length → gamma ∈ TreeMissingColors sigma
        (HierarchyStarredStage K (Fin.last K.dividerCount)) → gamma ∈ TreeMissingColors sigma Tn →
        (
    ∀ (coloring : PartialEdgeColoring E k) (c : CorrespondingExtendedTashkinovTree G k e0 ett
        coloring T), c.replacementETT.series.data.tree (Fin.last c.replacementETT.rounds).castSucc
        = ett.series.data.tree (Fin.last ett.rounds).castSucc) →
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty

private abbrev helperContinuation2461Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyPathNumber P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) (e1 : Fin T.length), (↑e1 : ℕ) = (HierarchyStarredStage
        P.counterexample.hierarchy (Fin.last P.counterexample.hierarchy.dividerCount)).length →
        P.coloring (T.edge e1) = some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let cm : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell →
    ∀ (htwo : (2 : ℕ) ≤ ell), TreeSequenceInitialSegment A T →
    ∀ (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1 : ℕ)),
        TreeSequenceInitialSegment A B →
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    ∀ gamma ∈ TreeMissingColors mu A, gamma ≠ alpha → gamma ∈ TreeMissingColors mu Tn → gamma ∈
        TreeMissingColors mu B → alpha ∈ TreeMissingColors mu B → gamma ≠ alpha →
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T gamma;
    let vg : V := T.vertex ig;
    ∀ (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive;
    have this_2 : (1 : ℕ) ≤ T.length := T.positive;
    have this_3 : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    by
                       have := GoldbergSeymour.TreeSequence.positive T
                       have := GoldbergSeymour.TreeSequence.positive A
                       omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length),
    let Q : Set (V ⊕ E) := TwoColorComponent G mu gamma alpha (Sum.inl y);
    ∀ (hAshort : A.length + (1 : ℕ) < T.length), y ∉ TreeSequenceVertexSet A → Disjoint Q
        (TwoColorComponent G mu gamma alpha (Sum.inl vg)) → TwoColorPathComponent G mu gamma alpha
        (Sum.inl y) → ((0 : ℕ) < H.dividerCount → A = H.stage (⟨H.dividerCount,
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → (0 : ℕ) < H.dividerCount ∧ gamma ∈ TreeMissingColors mu
        (H.stage (⟨H.dividerCount,
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
    by
                                    omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
        mu Tn ∨ gamma ∈ TreeMissingColors mu A ∧ gamma ∉ TashkinovStoredColors em.series.data n ∧
        alpha ∉ TashkinovStoredColors em.series.data n) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y); (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v) → gamma ∈
        MissingColors G sigma y → sigma (T.edge e1) = mu (T.edge e1) →
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    by
                                 have := GoldbergSeymour.TreeSequence.positive T
                                 have := GoldbergSeymour.TreeSequence.positive A
                                 omega
    ) (
    have this : A.length + (1 : ℕ) < T.length := hAshort;
    by
                                 have := GoldbergSeymour.TreeSequence.positive T
                                 have := GoldbergSeymour.TreeSequence.positive A
                                 omega
    ); X.length = A.length + (1 : ℕ) → TreeSequenceInitialSegment A X → A.length < X.length →
        TreeSequenceInitialSegment X B → (
    ∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → sigma (T.edge t) = mu
        (T.edge t)) → (
    ∀ eta ∈ HierarchyStoredColorsAt H q, HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition mu T eta) → (
    ∀ eta ∈ HierarchyStoredColorsAt H q, gamma ∈ Cm.good.gamma q eta ∨ alpha ∈ Cm.good.gamma q eta
        → (↑(HierarchyFirstMissingPosition mu T eta) : ℕ) ≤ X.length) → TreeSequenceInitialSegment
        Tn A → (em.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X ∨ (em.series.data.kind n = some
        TashkinovExtensionKind.SE ∨ em.series.data.kind n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), em.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) ∧
        TashkinovAugmentationSequence mu X T → gamma ∈ TreeMissingColors sigma X ∧ alpha ∈
        TreeMissingColors sigma X → (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett
        base C ctx).Nonempty

private abbrev helperContinuation2492Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyPathNumber P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k), (
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)), Disjoint (MissingColors G
        P.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C
        i).length))) (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) →
    ∀ (e1 : Fin T.length), (↑e1 : ℕ) = (HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).length → P.coloring (T.edge e1) = some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let cm : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell →
    ∀ (htwo : (2 : ℕ) ≤ ell), TreeSequenceInitialSegment A T →
    ∀ (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1 : ℕ)),
        TreeSequenceInitialSegment A B → alpha ∈ TreeMissingColors mu A →
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q); (H.dividerCount = (0 : ℕ) → A =
        bm.core) →
    ∀ gamma ∈ TreeMissingColors mu A, gamma ∉ R → gamma ≠ alpha → gamma ∈ TreeMissingColors mu Tn
        → gamma ∈ TreeMissingColors mu B → alpha ∈ TreeMissingColors mu B → gamma ≠ alpha →
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T gamma;
    let vg : V := T.vertex ig;
    ∀ (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive;
    by
                            have := GoldbergSeymour.TreeSequence.positive T
                            have := GoldbergSeymour.TreeSequence.positive A
                            omega
    ) (
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬min
        (A.length + (T.length - A.length - (1 : ℕ))) T.length ≤ T.length) ↦
    by omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length),
    let Q : Set (V ⊕ E) := TwoColorComponent G mu gamma alpha (Sum.inl y);
    ∀ (hAshort : A.length + (1 : ℕ) < T.length), y ∉ TreeSequenceVertexSet A → Disjoint Q
        (TwoColorComponent G mu gamma alpha (Sum.inl vg)) → TwoColorPathComponent G mu gamma alpha
        (Sum.inl y) → ((0 : ℕ) < H.dividerCount → A = H.stage (⟨H.dividerCount,
    by
                                     have := GoldbergSeymour.TreeSequence.positive T
                                     omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) → (0 : ℕ) < H.dividerCount ∧ gamma ∈ TreeMissingColors mu
        (H.stage (⟨H.dividerCount,
    by
                                        have := GoldbergSeymour.TreeSequence.positive T
                                        omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨ H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors
        mu Tn ∨ gamma ∈ TreeMissingColors mu A ∧ gamma ∉ TashkinovStoredColors em.series.data n ∧
        alpha ∉ TashkinovStoredColors em.series.data n) → (
    ∀ w ∈ TreeSequenceVertexSet A, Sum.inl w ∉ Q) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y); (
    ∀ (v : V) (c : Fin k), c ≠ gamma → c ≠ alpha → (c ∈ MissingColors G (TwoColorComponentSwap G
        mu gamma alpha (Sum.inl y)) v ↔ c ∈ MissingColors G mu v)) → (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v) → gamma ∈
        MissingColors G sigma y → sigma (T.edge e1) = mu (T.edge e1) →
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (1 : ℕ)) ↦
    by omega
    ) (
    have this : A.length + (1 : ℕ) < T.length := hAshort; Decidable.byContradiction fun (a :
        ¬A.length + (1 : ℕ) ≤ T.length) ↦
    by omega
    ); X.length = A.length + (1 : ℕ) → TreeSequenceInitialSegment X T → (
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S T → TreeSequenceInitialSegment U T →
        S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment A X →
        A.length < X.length → TreeSequenceInitialSegment X B →
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty

private abbrev helperContinuation2398Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyPathNumber P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k), (0 : ℕ) < P.counterexample.hierarchy.dividerCount ∧ alpha ∈
        TreeMissingColors P.coloring (P.counterexample.hierarchy.stage
        (⟨P.counterexample.hierarchy.dividerCount,
    have this : (1 : ℕ) ≤ T.length := T.positive;
    by
               have := GoldbergSeymour.TreeSequence.positive T
               omega
    ⟩ : Fin (P.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        P.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ alpha ∈ TreeMissingColors P.coloring
        (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc) → (
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)), Disjoint (MissingColors G
        P.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C
        i).length))) (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) →
    ∀ (e1 : Fin T.length), (↑e1 : ℕ) = (HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).length → P.coloring (T.edge e1) = some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let cm : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell → (2 : ℕ) ≤ ell →
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T
        →
    ∀ (hsum : A.length + ell = T.length), B.length = T.length - (1 : ℕ) →
        TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B → alpha ∈
        TreeMissingColors mu A → alpha ∈ MissingColors G mu y →
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q); (H.dividerCount = (0 : ℕ) → A =
        bm.core) →
    ∀ gamma ∈ TreeMissingColors mu A, gamma ∉ R → gamma ≠ alpha → gamma ∈ TreeMissingColors mu Tn
        → gamma ∈ TreeMissingColors mu B → alpha ∈ TreeMissingColors mu B → gamma ≠ alpha →
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T gamma;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let vg : V := T.vertex ig; gamma ∈ MissingColors G mu vg → vg ∈ TreeSequenceVertexSet A →
        alpha ∈ MissingColors G mu (T.vertex ia) → T.vertex ia ∈ TreeSequenceVertexSet A →
    ∀ (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by
                                      have := GoldbergSeymour.TreeSequence.positive T
                                      have := GoldbergSeymour.TreeSequence.positive A
                                      omega
    ); A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ) → Ty.length = B.length → (
    let H : TashkinovHierarchy em bm := Cm.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
                                          have := GoldbergSeymour.TreeSequence.positive T
                                          omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    have Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    have Dn : Finset (Fin k) := TashkinovStoredColors em.series.data n;
    have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
    have va : V := T.vertex (HierarchyFirstMissingPosition mu T gamma);
    have vb : V := T.vertex (HierarchyFirstMissingPosition mu T alpha);
    have sameComponent : Prop := TwoColorComponent G mu gamma alpha (Sum.inl va) =
        TwoColorComponent G mu gamma alpha (Sum.inl vb); ((0 : ℕ) < H.dividerCount ∧ (gamma ∈
        TreeMissingColors mu Tnq ∨ Disjoint (insert gamma ({ alpha } : Finset (Fin k)) : Finset
        (Fin k)) Dnq) → sameComponent) ∧ (H.dividerCount = (0 : ℕ) ∧ (gamma ∈ TreeMissingColors mu
        Tn ∨ Disjoint (insert gamma ({ alpha } : Finset (Fin k)) : Finset (Fin k)) Dn) →
        sameComponent) ∧ (gamma ∈ TreeMissingColors mu A ∧ TreeColorSetClosed G mu A ({ gamma } :
        Finset (Fin k)) → sameComponent ∧ TreeInterchangeable G A mu gamma alpha)) →
        TwoColorComponent G mu gamma alpha (Sum.inl vg) = TwoColorComponent G mu gamma alpha
        (Sum.inl (T.vertex ia)) → TreeInterchangeable G A mu gamma alpha →
    let J : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu gamma alpha;
    let Q : Set (V ⊕ E) := TwoColorComponent G mu gamma alpha (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu gamma alpha (Sum.inl v)) →
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty

private theorem helper_hAB_259.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (_ : Fin T.length),
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ)); (2 : ℕ) ≤ ell →
        TreeSequenceInitialSegment A T → A.length + ell = T.length → B.length = T.length - (1 : ℕ)
        → TreeSequenceInitialSegment B T → TreeSequenceInitialSegment A B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation e1 Cm H q A ell B htwo hAT
      hsum hBlen hBT
  have hlen : A.length ≤ B.length := by omega
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    exact (hBT.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hAT.2.1 i)
  · intro i
    exact (hBT.2.2 (Fin.castLE hlen i)).symm.trans (hAT.2.2 i)

private theorem helper_hRcard_279.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q); D.card ≤ em.rounds → R.card ≤ (2 : ℕ) *
        em.rounds := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation em Cm H q D R hDcard
  calc
    R.card ≤ ∑ eta ∈ D, (Cm.good.gamma q eta).card := Finset.card_biUnion_le
    _ = 2 * D.card := by
      rw [Finset.sum_congr rfl (fun eta heta => Cm.good.twoColors q eta heta)]
      change (∑ eta ∈ HierarchyStoredColorsAt H q, (2 : ℕ)) =
        2 * (HierarchyStoredColorsAt H q).card
      simp [Nat.mul_comm]
    _ ≤ 2 * em.rounds := Nat.mul_le_mul_left 2 hDcard

private theorem helper_hSne_377.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q); R.card ≤ (2 : ℕ) * em.rounds →
    let S : Finset (Fin k) := TreeMissingColors mu Tn \ (R ∪ ({ alpha } : Finset (Fin k))); (2 :
        ℕ) * em.rounds + (11 : ℕ) ≤ (TreeMissingColors mu Tn).card → S.Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu em Cm H q n Tn D R hRcard S hlarge
  apply Finset.card_pos.mp
  rw [Finset.card_sdiff]
  have hi : ((TreeMissingColors mu Tn) ∩ (R ∪ {alpha})).card ≤
      (R ∪ {alpha}).card := Finset.card_le_card Finset.inter_subset_right
  have hi' : ((R ∪ {alpha}) ∩ (TreeMissingColors mu Tn)).card ≤
      (R ∪ {alpha}).card := by
    simpa [Finset.inter_comm] using hi
  have hru : (R ∪ {alpha}).card ≤ 2 * em.rounds + 1 := by
    calc
      (R ∪ {alpha}).card ≤ R.card + ({alpha} : Finset (Fin k)).card :=
        Finset.card_union_le R {alpha}
      _ ≤ 2 * em.rounds + 1 := by simp; omega
  omega

private theorem helper_closedSingleton_400.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let mu : PartialEdgeColoring E k := P.coloring;
    ∀ (gamma : Fin k) (U : TreeSequence G e0), ColoredVertexSetClosed G mu (TreeSequenceVertexSet
        U) → gamma ∈ TreeMissingColors mu U → TreeColorSetClosed G mu U ({ gamma } : Finset (Fin
        k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P mu gamma U hc hm c hcs
  have hcg : c = gamma := Finset.mem_singleton.mp hcs
  subst c
  obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hb, hcol⟩ := Finset.mem_filter.mp hf
  exact hc hb hv hcol hvm

private theorem helper_hAeq_523.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
      Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (_ : (0 : ℕ) < H.dividerCount),
    A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P Cm H q A hz
  obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
  · have hv := congrArg Fin.val hzero
    simp [q] at hv
    omega
  · simp only [A, HierarchyStarredStage, hr, Fin.cases_succ]
    congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hr
    simpa [q] using hv.symm

private theorem helper_hRsub_564.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q);
    ∀ (hz : (0 : ℕ) < H.dividerCount),
    let i : Fin H.dividerCount := (⟨H.dividerCount - (1 : ℕ),
    by omega
    ⟩ : Fin H.dividerCount); q = i.succ →
    let Dprev : Finset (Fin k) := HierarchyStoredColorsAt H i.succ;
    let Rprev : Finset (Fin k) := Dprev.biUnion (Cm.good.gamma i.castSucc);
    ∀ (eta : Fin k), (
    ∀ theta ∈ HierarchyStoredColorsAt Cm.hierarchy i.succ, theta ≠ eta → Cm.good.gamma i.succ
        theta = Cm.good.gamma i.castSucc theta) → R ⊆ Rprev ∪ Cm.good.gamma i.succ eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P Cm H q D R hz i hq Dprev Rprev eta hcopy
      c hc
  obtain ⟨theta, htheta, hc⟩ := Finset.mem_biUnion.mp hc
  have hcNow : c ∈ Cm.good.gamma i.succ theta := by simpa only [hq] using hc
  by_cases hthetaEta : theta = eta
  · subst theta
    exact Finset.mem_union_right _ (by simpa only [hq] using hcNow)
  · have hthetaCurrent : theta ∈ Dprev := by
      simpa [Dprev, D, hq] using htheta
    have hthetaPrev : theta ∈ HierarchyStoredColorsAt H i.castSucc :=
      HierarchyStoredColorsAntitone H i hthetaCurrent
    have hcopyTheta := hcopy theta hthetaCurrent hthetaEta
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨theta, hthetaCurrent, by rw [← hcopyTheta]; exact hcNow⟩

private theorem helper_hRprevCard_578.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let _ : Finset (Fin k) := HierarchyStoredColorsAt H q;
    ∀ (hz : (0 : ℕ) < H.dividerCount),
    let i : Fin H.dividerCount := (⟨H.dividerCount - (1 : ℕ),
    by omega
    ⟩ : Fin H.dividerCount); q = i.succ →
    let Dprev : Finset (Fin k) := HierarchyStoredColorsAt H i.succ;
    let Rprev : Finset (Fin k) := Dprev.biUnion (Cm.good.gamma i.castSucc); Rprev.card ≤ (2 : ℕ) *
        em.rounds := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P em Cm H q D hz i hq Dprev Rprev
  calc
    Rprev.card ≤ ∑ theta ∈ Dprev, (Cm.good.gamma i.castSucc theta).card :=
      Finset.card_biUnion_le
    _ = 2 * Dprev.card := by
      rw [Finset.sum_congr rfl (fun theta htheta =>
        Cm.good.twoColors i.castSucc theta (HierarchyStoredColorsAntitone H i
          (by simpa [Dprev, D, hq] using htheta)))]
      change (∑ theta ∈ HierarchyStoredColorsAt H i.succ, (2 : ℕ)) =
        2 * (HierarchyStoredColorsAt H i.succ).card
      simp [Nat.mul_comm]
    _ ≤ 2 * em.rounds := by
      exact Nat.mul_le_mul_left 2 (by
        exact HierarchyStoredColorsCardinality H i.succ)

private theorem helper_hforbiddenCard_595.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q);
    ∀ (hz : (0 : ℕ) < H.dividerCount),
    let i : Fin H.dividerCount := (⟨H.dividerCount - (1 : ℕ),
    by omega
    ⟩ : Fin H.dividerCount);
    let Dprev : Finset (Fin k) := HierarchyStoredColorsAt H i.succ;
    let Rprev : Finset (Fin k) := Dprev.biUnion (Cm.good.gamma i.castSucc);
    ∀ (eta : Fin k), R ⊆ Rprev ∪ Cm.good.gamma i.succ eta → Rprev.card ≤ (2 : ℕ) * em.rounds →
        (Cm.good.gamma i.succ eta).card ≤ (2 : ℕ) → (Rprev ∪ R ∪ ({ alpha } : Finset (Fin
        k))).card ≤ (2 : ℕ) * em.rounds + (3 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha em Cm H q D R hz i Dprev Rprev eta
      hRsub hRprevCard hpairCard
  have hsub : Rprev ∪ R ∪ {alpha} ⊆ Rprev ∪ Cm.good.gamma i.succ eta ∪ {alpha} := by
    intro c hc
    simp only [Finset.mem_union] at hc ⊢
    rcases hc with h | h
    · rcases h with h | h
      · exact Or.inl (Or.inl h)
      · have hp := Finset.mem_union.mp (hRsub h)
        rcases hp with hp | hp
        · exact Or.inl (Or.inl hp)
        · exact Or.inl (Or.inr hp)
    · exact Or.inr h
  calc
    (Rprev ∪ R ∪ {alpha}).card ≤
        (Rprev ∪ Cm.good.gamma i.succ eta ∪ {alpha}).card :=
      Finset.card_le_card hsub
    _ ≤ (Rprev ∪ Cm.good.gamma i.succ eta).card + 1 := by
      calc
        _ ≤ (Rprev ∪ Cm.good.gamma i.succ eta).card + ({alpha} : Finset (Fin k)).card :=
          Finset.card_union_le _ _
        _ = _ := by simp
    _ ≤ Rprev.card + (Cm.good.gamma i.succ eta).card + 1 := by
      have := Finset.card_union_le Rprev (Cm.good.gamma i.succ eta)
      omega
    _ ≤ 2 * em.rounds + 3 := by omega

private theorem helper_hSne_623.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q);
    ∀ (hz : (0 : ℕ) < H.dividerCount),
    let i : Fin H.dividerCount := (⟨H.dividerCount - (1 : ℕ),
    by omega
    ⟩ : Fin H.dividerCount);
    let Dprev : Finset (Fin k) := HierarchyStoredColorsAt H i.succ;
    let Rprev : Finset (Fin k) := Dprev.biUnion (Cm.good.gamma i.castSucc);
    ∀ (_ : Fin k), (Rprev ∪ R ∪ ({ alpha } : Finset (Fin k))).card ≤ (2 : ℕ) * em.rounds + (3 : ℕ)
        → (2 : ℕ) * em.rounds + (11 : ℕ) ≤ (TreeMissingColors mu Tn).card →
    let S : Finset (Fin k) := TreeMissingColors mu Tn \ (Rprev ∪ R ∪ ({ alpha } : Finset (Fin
        k))); S.Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu em Cm H q n Tn D R hz i Dprev
      Rprev eta hforbiddenCard hlarge S
  apply Finset.card_pos.mp
  rw [Finset.card_sdiff]
  have hi : ((Rprev ∪ R ∪ {alpha}) ∩ TreeMissingColors mu Tn).card ≤
      (Rprev ∪ R ∪ {alpha}).card := Finset.card_le_card Finset.inter_subset_left
  omega

private theorem helper_hminus_645.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (_ : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    ∀ (hz : (0 : ℕ) < H.dividerCount),
    let i : Fin H.dividerCount := (⟨H.dividerCount - (1 : ℕ),
    by omega
    ⟩ : Fin H.dividerCount); q = i.succ → A = H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ))) →
    let Dprev : Finset (Fin k) := HierarchyStoredColorsAt H i.succ;
    let Rprev : Finset (Fin k) := Dprev.biUnion (Cm.good.gamma i.castSucc);
    ∀ (_ : Fin k), TreeColorSetMinusClosed G mu A Rprev := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu Cm H q A hz i hq hAeq Dprev
      Rprev eta
  have hstage : i.succ.castSucc =
      (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := by
    apply Fin.ext
    simp [i]
    omega
  rw [hAeq]
  simpa [Rprev, Dprev, q, hq, hstage] using Cm.good.minusClosed i

private theorem helper_hAlphaAtFirst_721.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; TreeSequenceInitialSegment A T → alpha
        ∈ TreeMissingColors mu A → (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha; alpha ∈
        MissingColors G mu (T.vertex ia) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha mu Cm H q A hAT haA
      firstSpec ia
  obtain ⟨w, hw, hmw⟩ := Finset.mem_biUnion.mp haA
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨i, hi⟩ := hw
  let iT := Fin.castLE (Nat.succ_le_succ hAT.1) i
  have hwi : alpha ∈ MissingColors G mu (T.vertex iT) := by
    rw [hAT.2.1 i, hi]
    exact hmw
  exact (firstSpec mu alpha iT hwi).1

private theorem helper_hiaBound_730.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; TreeSequenceInitialSegment A T → alpha
        ∈ TreeMissingColors mu A →
    ∀ (_ : Fin k), (
    ∀ (rho : PartialEdgeColoring E k) (c : Fin k) (i : Fin (T.length + (1 : ℕ))), c ∈
        MissingColors G rho (T.vertex i) → c ∈ MissingColors G rho (T.vertex
        (HierarchyFirstMissingPosition rho T c)) ∧ HierarchyFirstMissingPosition rho T c ≤ i) →
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha; (↑ia : ℕ) ≤
        A.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 mu Cm H q A hAT haA
      gamma firstSpec ia
  obtain ⟨w, hw, hmw⟩ := Finset.mem_biUnion.mp haA
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
  obtain ⟨i, hi⟩ := hw
  let iT := Fin.castLE (Nat.succ_le_succ hAT.1) i
  have hwi : alpha ∈ MissingColors G mu (T.vertex iT) := by
    rw [hAT.2.1 i, hi]
    exact hmw
  have hs := firstSpec mu alpha iT hwi
  have hv := hs.2
  change ia.val ≤ i.val at hv
  have := i.isLt
  omega

private theorem helper_hyNotA_838.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (_ : Fin k) (_ : Fin T.length),
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); (2 : ℕ) ≤ ell → TreeSequenceInitialSegment A T →
    ∀ (hsum : A.length + ell = T.length), B.length = T.length - (1 : ℕ) →
    ∀ (_ : Fin k) (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by omega
    ); A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ) → Ty.length = B.length → y
        ∉ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 Cm H q A ell B y htwo
      hAT hsum hBlen gamma htaildiff Ty hidx hTyLen hy
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨i, hi⟩ := hy
  have heq : T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) i) =
      T.vertex (Fin.last T.length) := by
    rw [hAT.2.1 i]
    exact hi
  have hidx := congrArg Fin.val (T.vertex_injective heq)
  have hiLt := i.isLt
  simp at hidx
  omega

private theorem helper_branch_859.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k), (
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)), Disjoint (MissingColors G
        P.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C
        i).length))) (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let y : V := T.vertex (Fin.last T.length); alpha ∈ MissingColors G mu y →
    ∀ (gamma : Fin k),
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T gamma;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let vg : V := T.vertex ig; gamma ∈ MissingColors G mu vg → alpha ∈ MissingColors G mu
        (T.vertex ia) → TwoColorComponent G mu gamma alpha (Sum.inl vg) = TwoColorComponent G mu
        gamma alpha (Sum.inl (T.vertex ia)) →
    let J : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu gamma alpha;
    let Q : Set (V ⊕ E) := TwoColorComponent G mu gamma alpha (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu gamma alpha (Sum.inl v)) → (
    ∀ (v : V), gamma ∈ MissingColors G mu v ∨ alpha ∈ MissingColors G mu v → (J.neighborSet
        (Sum.inl v)).Subsingleton) → vg ≠ y → T.vertex ia ≠ y → TwoColorComponent G mu gamma alpha
        (Sum.inl y) = TwoColorComponent G mu gamma alpha (Sum.inl vg) → Disjoint Q
        (TwoColorComponent G mu gamma alpha (Sum.inl vg)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha _ mu cm y haY gamma ig
      ia vg hgamvg hAlphaAtFirst hsame J Q self leaf hvgNeY hiaNeY heq
  obtain ⟨u, v, path, hp, hs⟩ :=
    TwoColorComponentSpanningPath G mu gamma alpha cm.proper (Sum.inl y)
  have endpoint (w : V) (hw : Sum.inl w ∈ Q)
      (hl : Set.Subsingleton (J.neighborSet (Sum.inl w))) :
      Sum.inl w = u ∨ Sum.inl w = v := by
    have hm : Sum.inl w ∈ path.support := by
      change Sum.inl w ∈ {x | x ∈ path.support}
      rw [hs]
      exact hw
    by_contra hn
    push Not at hn
    exact hp.isTrail.notMem_support_of_subsingleton_neighborSet hn.1 hn.2 hl hm
  change Q = TwoColorComponent G mu gamma alpha (Sum.inl vg) at heq
  have hvgQ : Sum.inl vg ∈ Q := by rw [heq]; exact self vg
  have hyQ : Sum.inl y ∈ Q := self y
  have hevg := endpoint vg hvgQ (leaf vg (Or.inl hgamvg))
  have hey := endpoint y hyQ (leaf y (Or.inr haY))
  by_cases hsameRoot : vg = T.vertex ia
  · have hboth : gamma ∈ MissingColors G mu vg ∧ alpha ∈ MissingColors G mu vg := by
      constructor
      · exact hgamvg
      · simpa [hsameRoot] using hAlphaAtFirst
    have hnoAdj : ∀ w, ¬ J.Adj (Sum.inl vg) w := by
      intro w hadj
      simp only [J, TwoColorIncidenceGraph] at hadj
      rcases w with w | f
      · simp [] at hadj
      · rcases hadj with ⟨hinc, hcol⟩
        rcases hcol with hc | hc
        · exact (Finset.mem_sdiff.mp hboth.1).2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨f, hinc, hc⟩⟩)
        · exact (Finset.mem_sdiff.mp hboth.2).2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨f, hinc, hc⟩⟩)
    have hmem : Sum.inl vg ∈ J.connectedComponentMk (Sum.inl y) := by
      change Sum.inl vg ∈ Q
      rw [heq]
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    have hreach : J.Reachable (Sum.inl vg) (Sum.inl y) :=
      SimpleGraph.ConnectedComponent.eq.mp hmem
    have hempty : J.neighborSet (Sum.inl vg) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun w hw =>
        hnoAdj w (by simpa only [SimpleGraph.mem_neighborSet] using hw))
    have hvgY : (Sum.inl vg : Sum V E) ≠ Sum.inl y := by
      intro h
      exact hvgNeY (Sum.inl.inj h)
    exact False.elim
      ((SimpleGraph.not_reachable_of_neighborSet_left_eq_empty (G := J) hvgY hempty) hreach)
  · have hiaQ : Sum.inl (T.vertex ia) ∈ Q := by
      rw [heq, hsame]
      exact self (T.vertex ia)
    have heia := endpoint (T.vertex ia) hiaQ
      (leaf (T.vertex ia) (Or.inr hAlphaAtFirst))
    have hneqGA : vg ≠ T.vertex ia := hsameRoot
    have hneqGY : vg ≠ y := hvgNeY
    have hneqAY : T.vertex ia ≠ y := hiaNeY
    rcases hevg with hgu | hgv
    · rcases heia with hau | hav
      · rcases hey with hyu | hyv
        · exact False.elim (hneqGA (Sum.inl.inj (hgu.trans hau.symm)))
        · exact False.elim (hneqGA (Sum.inl.inj (hgu.trans hau.symm)))
      · rcases hey with hyu | hyv
        · exact False.elim (hneqGY (Sum.inl.inj (hgu.trans hyu.symm)))
        · exact False.elim (hneqAY (Sum.inl.inj (hav.trans hyv.symm)))
    · rcases heia with hau | hav
      · rcases hey with hyu | hyv
        · exact False.elim (hneqAY (Sum.inl.inj (hau.trans hyu.symm)))
        · exact False.elim (hneqGY (Sum.inl.inj (hgv.trans hyv.symm)))
      · rcases hey with hyu | hyv
        · exact False.elim (hneqGA (Sum.inl.inj (hgv.trans hav.symm)))
        · exact False.elim (hneqGA (Sum.inl.inj (hgv.trans hav.symm)))

private theorem helper_hAstage_932.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
      (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyPathNumber P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (_ : Fin k) (_ : Fin T.length),
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
      Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    ∀ (_ : A.length + ell = T.length) (_ : Fin k) (_ : T.length - A.length = ell),
    (0 : ℕ) < H.dividerCount →
    A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 Cm H q A ell hsum
      gamma htaildiff hp
  obtain hzero | ⟨r, hr⟩ := Fin.eq_zero_or_eq_succ q
  · have hv := congrArg Fin.val hzero
    simp [q] at hv
    omega
  · simp only [A, HierarchyStarredStage, hr, Fin.cases_succ]
    congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hr
    simpa [q] using hv.symm

private theorem helper_hQoutsideA_956.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (gamma : Fin k),
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T gamma;
    let vg : V := T.vertex ig; vg ∈ TreeSequenceVertexSet A → TreeInterchangeable G A mu gamma
        alpha →
    let Q : Set (V ⊕ E) := TwoColorComponent G mu gamma alpha (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu gamma alpha (Sum.inl v)) → Disjoint Q
        (TwoColorComponent G mu gamma alpha (Sum.inl vg)) → TwoColorPathComponent G mu gamma alpha
        (Sum.inl y) → TwoColorPathComponent G mu gamma alpha (Sum.inl vg) →
    ∀ w ∈ TreeSequenceVertexSet A, Sum.inl w ∉ Q := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha mu Cm H q A y gamma ig
      vg hvgInA hinterchangeable Q self hdisjoint hpath hvgPath w hw hwQ
  have hsameComp := hinterchangeable (Sum.inl y) (Sum.inl vg) hpath hvgPath
    ⟨w, hw, hwQ⟩ ⟨vg, hvgInA, self vg⟩
  have hvgQ : Sum.inl vg ∈ Q := by
    change Sum.inl vg ∈ TwoColorComponent G mu gamma alpha (Sum.inl y)
    rw [hsameComp]
    exact self vg
  exact Set.disjoint_left.mp hdisjoint hvgQ (self vg)

private theorem helper_branch_975.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); ColoredVertexSetElementary G mu
        (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A B →
    ∀ (gamma : Fin k),
    let ig : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T gamma;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition mu T alpha;
    let vg : V := T.vertex ig; gamma ∈ MissingColors G mu vg → vg ∈ TreeSequenceVertexSet A →
        alpha ∈ MissingColors G mu (T.vertex ia) → T.vertex ia ∈ TreeSequenceVertexSet A →
        TwoColorComponent G mu gamma alpha (Sum.inl vg) = TwoColorComponent G mu gamma alpha
        (Sum.inl (T.vertex ia)) →
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu gamma alpha;
    let Q : Set (V ⊕ E) := TwoColorComponent G mu gamma alpha (Sum.inl y); (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G mu gamma alpha (Sum.inl v)) → Disjoint Q
        (TwoColorComponent G mu gamma alpha (Sum.inl vg)) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y); (
    ∀ (v : V) (c : Fin k), c ≠ gamma → c ≠ alpha → (c ∈ MissingColors G (TwoColorComponentSwap G
        mu gamma alpha (Sum.inl y)) v ↔ c ∈ MissingColors G mu v)) →
    ∀ w ∈ TreeSequenceVertexSet B, Sum.inl w ∈ Q → MissingColors G sigma w = MissingColors G mu w
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu Cm H q A ell B y helem hAB gamma
      ig ia vg hgamvg hvgInA hAlphaAtFirst hiaInA hsame J Q self hdisjoint sigma missingOther w
      hw hwQ
  have hwGamma : w ≠ vg := by
    intro h
    subst w
    exact Set.disjoint_left.mp hdisjoint hwQ (self vg)
  have hwAlpha : w ≠ T.vertex ia := by
    intro h
    subst w
    exact Set.disjoint_left.mp hdisjoint hwQ (by rw [hsame]; exact self (T.vertex ia))
  have hng : gamma ∉ MissingColors G mu w := fun hm =>
    Finset.disjoint_left.mp (helem hw (TreeSequenceInitialSegmentVertexSetSubset hAB hvgInA)
      hwGamma) hm hgamvg
  have hna : alpha ∉ MissingColors G mu w := fun hm =>
    Finset.disjoint_left.mp (helem hw (TreeSequenceInitialSegmentVertexSetSubset hAB hiaInA)
      hwAlpha) hm hAlphaAtFirst
  obtain ⟨fg, hfg, hfgc⟩ : ∃ f, Incident G w f ∧ mu f = some gamma := by
    simpa [MissingColors, PresentColors] using hng
  obtain ⟨fa, hfa, hfac⟩ : ∃ f, Incident G w f ∧ mu f = some alpha := by
    simpa [MissingColors, PresentColors] using hna
  have edgeOfVertex {v : V} {f : E}
      (hv : Sum.inl v ∈ Q) (hf : Incident G v f)
      (hc : mu f = some gamma ∨ mu f = some alpha) : Sum.inr f ∈ Q := by
    change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl y) at hv
    change J.connectedComponentMk (Sum.inr f) = J.connectedComponentMk (Sum.inl y)
    have hadj : J.Adj (Sum.inr f) (Sum.inl v) := by
      simpa only [J, TwoColorIncidenceGraph] using And.intro hf hc
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  have hfgQ := edgeOfVertex hwQ hfg (Or.inl hfgc)
  have hfaQ := edgeOfVertex hwQ hfa (Or.inr hfac)
  have hnewAlpha : sigma fg = some alpha := by
    simp [sigma, TwoColorComponentSwap, Q, hfgQ, hfgc]
  have hnewGamma : sigma fa = some gamma := by
    simp [sigma, TwoColorComponentSwap, Q, hfaQ, hfac]
  have hnsGamma : gamma ∉ MissingColors G sigma w := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fa, hfa, hnewGamma⟩
  have hnsAlpha : alpha ∉ MissingColors G sigma w := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fg, hfg, hnewAlpha⟩
  ext c
  by_cases hcg : c = gamma
  · rw [hcg]
    simp only [hng, hnsGamma]
  by_cases hca : c = alpha
  · rw [hca]
    simp only [hna, hnsAlpha]
  exact missingOther w c hcg hca

private theorem helper_he1Incident_1026.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (_ : Fin k) (e1 : Fin T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑e1 : ℕ) = A.length) →
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
        TreeSequenceInitialSegment A T →
    ∀ (hsum : A.length + ell = T.length), B.length = T.length - (1 : ℕ) →
    ∀ (_ : Fin k) (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by omega
    ); A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ) → Ty.length = B.length →
        TreeIncidentEdge A (T.edge e1) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 he1 Cm H q A ell B
      hAT hsum hBlen gamma htaildiff Ty hidx hTyLen
  obtain ⟨i, hi⟩ := T.attaches e1
  have hiBound : i.val ≤ A.length := by
    have hiLt := i.isLt
    have heval : e1.val = A.length := by exact he1
    omega
  let iA : Fin (A.length + 1) := ⟨i.val, by omega⟩
  have hindex : Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ e1.isLt)) =
      Fin.castLE (Nat.succ_le_succ hAT.1) iA := by
    apply Fin.ext
    rfl
  refine ⟨A.vertex iA, ?_, ?_⟩
  · simp [TreeSequenceVertexSet]
  · change A.vertex iA ∈ G.ends (T.edge e1)
    rw [← hAT.2.1 iA, hindex.symm, hi]
    simp

private theorem helper_he1notQ_1042.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) (e1 : Fin T.length), P.coloring (T.edge e1) = some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (gamma : Fin k),
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu gamma alpha;
    let Q : Set (V ⊕ E) := TwoColorComponent G mu gamma alpha (Sum.inl y); (
    ∀ w ∈ TreeSequenceVertexSet A, Sum.inl w ∉ Q) → TreeIncidentEdge A (T.edge e1) → Sum.inr
        (T.edge e1) ∉ Q := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 hfirst mu Cm H q A y
      gamma J Q hQoutsideA he1Incident hQe
  obtain ⟨w, hwA, hwInc⟩ := he1Incident
  have hadj : J.Adj (Sum.inl w) (Sum.inr (T.edge e1)) := by
    change Incident G w (T.edge e1) ∧
      (mu (T.edge e1) = some gamma ∨ mu (T.edge e1) = some alpha)
    exact ⟨hwInc, Or.inr hfirst⟩
  have hwQ : Sum.inl w ∈ Q := by
    change J.connectedComponentMk (Sum.inl w) = J.connectedComponentMk (Sum.inl y)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hQe
  exact hQoutsideA w hwA hwQ

private theorem helper_hgammaCutoff_1122.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) (e1 : Fin T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑e1 : ℕ) = A.length) → P.coloring (T.edge e1) =
        some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    ∀ (htwo : (2 : ℕ) ≤ ell) (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1
        : ℕ)),
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q);
    ∀ gamma ∉ R,
    ∀ (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length) (hAshort : A.length + (1 : ℕ) < T.length),
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (1 : ℕ)) ↦
    by omega
    ) (
    have _ : A.length + (1 : ℕ) < T.length := hAshort; Decidable.byContradiction fun (a :
        ¬A.length + (1 : ℕ) ≤ T.length) ↦
    by omega
    ); X.length = A.length + (1 : ℕ) →
    ∀ eta ∈ HierarchyStoredColorsAt H q, gamma ∈ Cm.good.gamma q eta ∨ alpha ∈ Cm.good.gamma q eta
        → (↑(HierarchyFirstMissingPosition mu T eta) : ℕ) ≤ X.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 he1 hfirst mu Cm H q
      A ell B htwo hsum hBlen D R gamma hgammaR htaildiff Ty hidx hTyLen hAshort X hXlen
  clear * - X mu T H q A Cm gamma alpha R hgammaR hfirst e1 he1 hXlen
  intro eta heta hp
  have havoid := Cm.good.avoidance q eta heta
  rcases hp with hg | ha
  · exact False.elim (hgammaR (Finset.mem_biUnion.mpr ⟨eta, heta, hg⟩))
  · by_contra hnot
    have hpast : X.length < (HierarchyFirstMissingPosition mu T eta).val := by omega
    have he1A : e1.val = A.length := by simpa [A, H, q] using he1
    have hterminal : H.stage q.succ = T := by
      have hq : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
      rw [hq, H.terminalStage]
    have hsegment : alpha ∈ HierarchySegmentColors H q eta := by
      change alpha ∈ Finset.univ.filter fun c => ∃ r : Fin (H.stage q.succ).length,
        A.length ≤ r.val ∧ r.val <
          min (HierarchyFirstMissingPosition mu T eta).val (H.stage q.succ).length ∧
            mu ((H.stage q.succ).edge r) = some c
      rw [hterminal]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨e1, ?_, ?_, hfirst⟩
      · omega
      · apply Nat.lt_min.mpr
        constructor
        · rw [hXlen] at hpast
          omega
        · exact e1.isLt
    exact (Finset.mem_sdiff.mp (havoid ha)).2 hsegment

private theorem helper_branch_1162.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (gamma : Fin k),
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G mu gamma alpha;
    let Q : Set (V ⊕ E) := TwoColorComponent G mu gamma alpha (Sum.inl y); (
    ∀ w ∈ TreeSequenceVertexSet A, Sum.inl w ∉ Q) →
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y);
    ∀ (t : Fin A.length), A.vertex t.succ ∈ TreeSequenceVertexSet A → Incident G (A.vertex t.succ)
        (A.edge t) → Sum.inr (A.edge t) ∈ Q → sigma (A.edge t) = mu (A.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha mu Cm H q A y gamma J Q
      hQoutsideA sigma t htVertex htIncident hQe
  exact (hQoutsideA _ htVertex
    (TwoColorComponent.vertex_mem_of_incident hQe htIncident)).elim

private theorem helper_hfixedX_1181.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) (e1 : Fin T.length), (
    let A : TreeSequence G e0 := HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount); (↑e1 : ℕ) = A.length) →
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length);
    ∀ (htwo : (2 : ℕ) ≤ ell), TreeSequenceInitialSegment A T →
    ∀ (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1 : ℕ)) (gamma : Fin k)
        (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length) (hAshort : A.length + (1 : ℕ) < T.length),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y);
        sigma (T.edge e1) = mu (T.edge e1) →
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (1 : ℕ)) ↦
    by omega
    ) (
    have _ : A.length + (1 : ℕ) < T.length := hAshort; Decidable.byContradiction fun (a :
        ¬A.length + (1 : ℕ) ≤ T.length) ↦
    by omega
    ); X.length = A.length + (1 : ℕ) → TreeSequenceInitialSegment X T → (
    ∀ (t : Fin A.length), sigma (A.edge t) = mu (A.edge t)) →
    ∀ (t : Fin X.length), sigma (X.edge t) = mu (X.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 he1 mu Cm H q A ell B
      y htwo hAT hsum hBlen gamma htaildiff Ty hidx hTyLen hAshort sigma hfixedSeed X hXlen hXT
      hfixedA t
  have htbound : t.val < A.length + 1 := by simpa only [hXlen] using t.isLt
  have htval : t.val ≤ A.length := by omega
  by_cases htSeed : t.val = A.length
  · have hteq : Fin.castLE hXT.1 t = e1 := by
      apply Fin.ext
      have hv := he1
      change e1.val = A.length at hv
      simp only [Fin.val_castLE]
      rw [hv]
      exact htSeed
    rw [← hXT.2.2 t, hteq]
    exact hfixedSeed
  · have htA : t.val < A.length := by omega
    let tA : Fin A.length := ⟨t.val, htA⟩
    have he : Fin.castLE hXT.1 t = Fin.castLE hAT.1 tA := by
      apply Fin.ext
      rfl
    rw [← hXT.2.2 t, he, hAT.2.2 tA]
    exact hfixedA tA

private theorem helper_branch_1237.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) ,
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length);
    ∀ (htwo : (2 : ℕ) ≤ ell) (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1
        : ℕ)) (gamma : Fin k) (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length) (hAshort : A.length + (1 : ℕ) < T.length),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y); (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v) →
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (1 : ℕ)) ↦
    by omega
    ) (
    have _ : A.length + (1 : ℕ) < T.length := hAshort; Decidable.byContradiction fun (a :
        ¬A.length + (1 : ℕ) ≤ T.length) ↦
    by omega
    ); TreeSequenceInitialSegment X B → (
    ∀ (t : Fin X.length), sigma (X.edge t) = mu (X.edge t)) → (
    ∀ {S U W : TreeSequence G e0}, TreeSequenceInitialSegment S U → TreeSequenceInitialSegment U W
        → TreeSequenceInitialSegment S W) →
    ∀ {a c : TreeSequence G e0}, TashkinovAugmentation mu a c → Relation.ReflTransGen
        (TashkinovAugmentation mu) c X → Relation.ReflTransGen (TashkinovAugmentation sigma) c X →
        Relation.ReflTransGen (TashkinovAugmentation sigma) a X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha mu Cm H q A ell B y htwo
      hsum hBlen gamma htaildiff Ty hidx hTyLen hAshort sigma hmissingBEquality X hXB hfixedX
      segTrans U W hstep htail ih
  obtain ⟨hlen, hUW, c, hcolor, hc⟩ := hstep
  have hWX := TashkinovAugmentationSequenceInitialSegment mu W X htail
  have hUX := segTrans hUW hWX
  have hcNew : c ∈ TreeMissingColors sigma U := by
    obtain ⟨v, hvU, hcv⟩ := Finset.mem_biUnion.mp hc
    have hvB := TreeSequenceInitialSegmentVertexSetSubset hXB
      (TreeSequenceInitialSegmentVertexSetSubset hUX hvU)
    exact Finset.mem_biUnion.mpr ⟨v, hvU, (hmissingBEquality v hvB).symm ▸ hcv⟩
  let tW : Fin W.length := Fin.cast hlen.symm (Fin.last U.length)
  have hf := hfixedX (Fin.castLE hWX.1 tW)
  rw [hWX.2.2 tW] at hf
  exact Relation.ReflTransGen.head ⟨hlen, hUW, c, hf.trans hcolor, hcNew⟩ ih

private theorem helper_branch_1267.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length);
    ∀ (htwo : (2 : ℕ) ≤ ell) (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1
        : ℕ)),
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    ∀ (gamma : Fin k) (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length) (hAshort : A.length + (1 : ℕ) < T.length),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y);
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (1 : ℕ)) ↦
    by omega
    ) (
    have _ : A.length + (1 : ℕ) < T.length := hAshort; Decidable.byContradiction fun (a :
        ¬A.length + (1 : ℕ) ≤ T.length) ↦
    by omega
    ); X.length = A.length + (1 : ℕ) → TreeSequenceInitialSegment X T → (
    ∀ {S U : TreeSequence G e0}, TreeSequenceInitialSegment S T → TreeSequenceInitialSegment U T →
        S.length ≤ U.length → TreeSequenceInitialSegment S U) → TreeSequenceInitialSegment Tn A →
        (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence mu S X →
        TashkinovAugmentationSequence sigma S X) → em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.SE ∨ em.series.data.kind (Fin.last em.rounds) = some
        TashkinovExtensionKind.RE →
    ∀ (f : E) (seed : TreeSequence G e0), em.series.data.connectingEdges (Fin.last em.rounds) =
        ({ f } : Finset E) → TreeSequenceAdjoinEdge (em.series.data.tree (Fin.last
        em.rounds).castSucc) f seed → TashkinovAugmentationSequence mu seed T →
        (em.series.data.kind n = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        sigma Tn X ∨ (em.series.data.kind n = some TashkinovExtensionKind.SE ∨ em.series.data.kind
        n = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), em.series.data.connectingEdges n = ({ f } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X) ∧
        TashkinovAugmentationSequence mu X T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 mu em Cm H q A ell B
      y htwo hsum hBlen n Tn gamma htaildiff Ty hidx hTyLen hAshort sigma X hXlen hXT
      prefixOverlap hTnA transportRoute hkind f seed hedges hadjoin hroute
  have hseedT := TashkinovAugmentationSequenceInitialSegment mu seed T hroute
  have hseedX : TreeSequenceInitialSegment seed X :=
    prefixOverlap hseedT hXT (by
      have hseedLen := hadjoin.1
      change seed.length = Tn.length + 1 at hseedLen
      have := hTnA.1
      simp only [X, TreeSequencePrefix]
      omega)
  have hrouteX := TashkinovAugmentationSequenceRestrict mu seed X T hroute hseedX hXT
  exact ⟨Or.inr ⟨hkind, f, seed, hedges, hadjoin, transportRoute seed hrouteX⟩,
    TashkinovAugmentationSequenceSuffix mu seed X T hroute hseedX hXT⟩

private theorem helper_hsplitMissing_1278.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k) (_ : Fin T.length),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length);
    ∀ (htwo : (2 : ℕ) ≤ ell) (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1
        : ℕ)), TreeSequenceInitialSegment A B → alpha ∈ TreeMissingColors mu A →
    ∀ gamma ∈ TreeMissingColors mu A,
    ∀ (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length) (hAshort : A.length + (1 : ℕ) < T.length),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y); (
    ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G mu v) →
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤
        A.length + (1 : ℕ)) ↦
    by omega
    ) (
    have _ : A.length + (1 : ℕ) < T.length := hAshort; Decidable.byContradiction fun (a :
        ¬A.length + (1 : ℕ) ≤ T.length) ↦
    by omega
    ); TreeSequenceInitialSegment A X → gamma ∈ TreeMissingColors sigma X ∧ alpha ∈
        TreeMissingColors sigma X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha e1 mu Cm H q A ell B y
      htwo hsum hBlen hAB haA gamma hgammaA htaildiff Ty hidx hTyLen hAshort sigma
      hmissingBEquality X hAX
  constructor
  · obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgammaA
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAX hv,
        (hmissingBEquality v (TreeSequenceInitialSegmentVertexSetSubset hAB hv)).symm ▸ hmv⟩
  · obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp haA
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAX hv,
        (hmissingBEquality v (TreeSequenceInitialSegmentVertexSetSubset hAB hv)).symm ▸ hmv⟩

private theorem helper_branch_1321.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    let y : V := T.vertex (Fin.last T.length);
    ∀ (Pnew : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), (¬
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)), Disjoint (MissingColors G
        Pnew.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C
        i).length))) (MissingColors G Pnew.coloring y)) → (HierarchyEligibleCommonMissingIndices G
        k e0 input T phi ett base C ctx).Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation y Pnew hnoCommonPnew
  simp only [not_forall] at hnoCommonPnew
  obtain ⟨i, hi, hd⟩ := hnoCommonPnew
  obtain ⟨beta, hb, hby⟩ := Finset.not_disjoint_iff.mp hd
  refine ⟨i, ?_⟩
  change i ∈ (Finset.Icc 1 (HierarchyFullTailLength C - 1)).filter _
  exact Finset.mem_filter.mpr ⟨hi, Pnew, beta, hb, hby⟩

private theorem helper_hgammaNewTerminal_1425.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let y : V := T.vertex (Fin.last T.length);
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    ∀ (gamma : Fin k),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y);
    ∀ (Pnew : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Pnew.coloring =
        sigma → gamma ∈ TreeMissingColors sigma Tn →
        Pnew.corresponding.replacementETT.series.data.tree (Fin.last
        Pnew.corresponding.replacementETT.rounds).castSucc = Tn → (
    ∀ (c₁ c₂ : PartialEdgeColoring E k), c₁ = c₂ →
    ∀ (U : TreeSequence G e0), TreeMissingColors c₁ U = TreeMissingColors c₂ U) → gamma ∈
        TreeMissingColors Pnew.coloring (Pnew.corresponding.replacementETT.series.data.tree
        (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha mu em y n Tn gamma sigma
      Pnew hPnew hgammaSigmaTn hterminalPnewTn treeMissingColorEq
  have h : gamma ∈ TreeMissingColors sigma
      (Pnew.corresponding.replacementETT.series.data.tree
        (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc) := by
    rw [hterminalPnewTn]
    exact hgammaSigmaTn
  rw [treeMissingColorEq Pnew.coloring sigma hPnew _]
  exact h

private theorem helper_hstartPnew_1464.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), HierarchyPathNumber
        P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let y : V := T.vertex (Fin.last T.length);
    ∀ (gamma : Fin k),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y);
        gamma ∈ MissingColors G sigma y → gamma ∈ TreeMissingColors sigma A →
    ∀ (Pnew : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Pnew.coloring =
        sigma → HierarchyStarredStage H q = HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount) → (
    ∀ (c₁ c₂ : PartialEdgeColoring E k), c₁ = c₂ →
    ∀ (U : TreeSequence G e0), TreeMissingColors c₁ U = TreeMissingColors c₂ U) → (
    ∀ (c₁ c₂ : PartialEdgeColoring E k), c₁ = c₂ →
    ∀ (v : V), MissingColors G c₁ v = MissingColors G c₂ v) → gamma ∈ TreeMissingColors
        Pnew.coloring (HierarchyStarredStage Pnew.counterexample.hierarchy (Fin.last
        Pnew.counterexample.hierarchy.dividerCount)) ∧ gamma ∈ MissingColors G Pnew.coloring
        (T.vertex (Fin.last T.length)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P hsituation alpha mu Cm H q A y gamma
      sigma hgammaNewY hgammaSigmaA Pnew hPnew hstarPnew treeMissingColorEq missingColorEq
  constructor
  · have h : gamma ∈ TreeMissingColors sigma
        (HierarchyStarredStage Pnew.counterexample.hierarchy
          (Fin.last Pnew.counterexample.hierarchy.dividerCount)) := by
      rw [← hstarPnew]
      exact hgammaSigmaA
    rw [treeMissingColorEq Pnew.coloring sigma hPnew _]
    exact h
  · rw [missingColorEq Pnew.coloring sigma hPnew _]
    exact hgammaNewY

private theorem helper_continuation_2499.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k) (e1
        : Fin T.length), (↑e1 : ℕ) = (HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).length → P.coloring (T.edge e1) = some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell →
    ∀ (htwo : (2 : ℕ) ≤ ell) (hsum : A.length + ell = T.length) (hBlen : B.length = T.length - (1
        : ℕ)) (gamma : Fin k), gamma ≠ alpha →
    ∀ (htaildiff : T.length - A.length = ell),
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive;
    have _ : (1 : ℕ) ≤ T.length := T.positive;
    have _ : (1 : ℕ) ≤ A.length := A.positive;
    have _ : (1 : ℕ) ≤ T.length := T.positive;
    have _ : (1 : ℕ) ≤ A.length := A.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    have _ : (1 : ℕ) ≤ T.length := T.positive;
    have _ : (1 : ℕ) ≤ A.length := A.positive;
    have _ : (1 : ℕ) ≤ T.length := T.positive;
    have _ : (1 : ℕ) ≤ A.length := A.positive;
    by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        omega
    );
    ∀ (hidx : A.length + (T.length - A.length - (1 : ℕ)) = T.length - (1 : ℕ)) (hTyLen : Ty.length
        = B.length) (hAshort : A.length + (1 : ℕ) < T.length),
    let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G mu gamma alpha (Sum.inl y);
        sigma (T.edge e1) = mu (T.edge e1) →
    let X : TreeSequence G e0 := TreeSequencePrefix T (A.length + (1 : ℕ)) (
    have this : (1 : ℕ) ≤ A.length := A.positive;
    have _ : (1 : ℕ) ≤ T.length := T.positive;
    have _ : (1 : ℕ) ≤ A.length := A.positive;
    by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        omega
    ) (
    have _ : A.length + (1 : ℕ) < T.length := hAshort;
    have _ : (1 : ℕ) ≤ T.length := T.positive;
    have _ : (1 : ℕ) ≤ A.length := A.positive;
    by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        omega
    ); X.length = A.length + (1 : ℕ) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 em sigma T) (bs : HierarchyBase
        corr.replacementETT sigma) (K : TashkinovHierarchy corr.replacementETT bs) (Pnew :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx), Pnew.coloring = sigma
        → (
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)), Disjoint (MissingColors G
        Pnew.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C
        i).length))) (MissingColors G Pnew.coloring y)) → HierarchyPathNumber
        Pnew.counterexample.hierarchy = (1 : ℕ) → (HierarchyStarredStage K (Fin.last
        K.dividerCount)).length = A.length → (HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length = A.length → gamma ∈
        TreeMissingColors Pnew.coloring (HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount)) ∧ gamma ∈ MissingColors G
        Pnew.coloring (T.vertex (Fin.last T.length)) → (0 : ℕ) <
        Pnew.counterexample.hierarchy.dividerCount ∧ gamma ∈ TreeMissingColors Pnew.coloring
        (Pnew.counterexample.hierarchy.stage (⟨Pnew.counterexample.hierarchy.dividerCount,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (Pnew.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        Pnew.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ gamma ∈ TreeMissingColors
        Pnew.coloring (Pnew.corresponding.replacementETT.series.data.tree (Fin.last
        Pnew.corresponding.replacementETT.rounds).castSucc) →
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing P alpha e1 he1 hfirst mu em
      Cm H q A ell B y hell htwo hsum hBlen gamma hgammaNe htaildiff Ty hidx hTyLen hAshort sigma
      hfixedSeed X hXlen corr bs K Pnew hPnew hnoCommonPnew hnewSituationPnew hKstarLen
      hPnewStarLen hstartPnew hnormalizedPnew
  by_cases hunused : ∀ t : Fin T.length, A.length ≤ t.val →
      sigma (T.edge t) ≠ some gamma
  · have hunusedNew :
        ∀ t : Fin T.length,
          (HierarchyStarredStage Pnew.counterexample.hierarchy
            (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length ≤ t.val →
            Pnew.coloring (T.edge t) ≠ some gamma := by
      intro t ht hc
      have htA : A.length ≤ t.val := by rw [← hPnewStarLen]; exact ht
      have hc' : sigma (T.edge t) = some gamma := by rw [← hPnew]; exact hc
      exact hunused t htA hc'
    exact ⟨HierarchyFullTailLength C - 1,
      HierarchyClaimNineUnusedTailColor G k e0 input T phi ett base C ctx
      hvertexMissing Pnew hnewSituationPnew gamma hstartPnew
      hnormalizedPnew hnoCommonPnew hunusedNew⟩
  · let S : Finset (Fin T.length) :=
      Finset.univ.filter fun t => A.length ≤ t.val ∧ sigma (T.edge t) = some gamma
    have hS : S.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      apply hunused
      intro t ht
      by_contra hc
      have htmem : t ∈ S := by simp [S, ht, hc]
      rw [hempty] at htmem
      simp at htmem
    let ej : Fin T.length := S.min' hS
    have hejMem : ej ∈ S := Finset.min'_mem S hS
    have hejData := (Finset.mem_filter.mp hejMem).2
    have hejColor : sigma (T.edge ej) = some gamma := hejData.2
    have hseedIndex : e1.val = A.length := by exact he1
    have hseedNotGamma : sigma (T.edge e1) ≠ some gamma := by
      have hcolor : mu (T.edge e1) = some alpha := by simpa [mu] using hfirst
      rw [hfixedSeed, hcolor]
      exact fun h => hgammaNe (Option.some.inj h).symm
    have hAej : A.length < ej.val := by
      have hmin : ej.val ≤ e1.val ∨ e1.val ≤ ej.val := le_total ej.val e1.val
      by_contra hn
      have heq : ej.val = A.length := by omega
      have hteq : ej = e1 := Fin.ext (by rw [heq, hseedIndex])
      exact hseedNotGamma (hteq ▸ hejColor)
    let j : ℕ := ej.val - A.length + 1
    have hjLower : 2 ≤ j := by dsimp [j]; omega
    have hjUpper : j ≤ HierarchyFullTailLength C := by
      rw [hell]
      have hejl := ej.isLt
      dsimp [j]
      omega
    have hej : ej.val = A.length + (j - 1) := by
      dsimp only [j]
      clear * - hAej
      omega
    have hfirstNew : Pnew.coloring (T.edge ej) = some gamma ∧
        ∀ t : Fin T.length, A.length ≤ t.val → t.val < ej.val →
          Pnew.coloring (T.edge t) ≠ some gamma := by
      constructor
      · rw [hPnew]
        exact hejColor
      · intro t ht hlt hc
        have hc' : sigma (T.edge t) = some gamma := by rw [← hPnew]; exact hc
        have hmem : t ∈ S := by simp [S, ht, hc']
        have hmin : ej.val ≤ t.val := Finset.min'_le S t hmem
        omega
    have hejNew : ej.val =
        (HierarchyStarredStage Pnew.counterexample.hierarchy
          (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length + (j - 1) := by
      rw [hPnewStarLen]
      exact hej
    have hfirstNewK :
        Pnew.coloring (T.edge ej) = some gamma ∧
          ∀ t : Fin T.length,
            (HierarchyStarredStage Pnew.counterexample.hierarchy
              (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length ≤ t.val →
              t.val < ej.val → Pnew.coloring (T.edge t) ≠ some gamma := by
      refine ⟨hfirstNew.1, ?_⟩
      intro t ht hlt hc
      apply hfirstNew.2 t
      · rw [hPnewStarLen] at ht
        exact ht
      · exact hlt
      · exact hc
    have hjEligible := HierarchyClaimNineFirstUseAfterSeed G k e0 input T phi ett base C ctx
      hvertexMissing Pnew hnewSituationPnew gamma hstartPnew
      hnormalizedPnew hnoCommonPnew j hjLower hjUpper ej hejNew hfirstNewK
    exact ⟨j - 1, hjEligible⟩

private theorem helper_continuation_2476.{u_1, u_2} :
    helperContinuation2476Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing P hsituation alpha e1 he1
      hfirst mu em bm Cm H q A ell B y hell htwo hsum hBlen n Tn gamma hgammaNe htaildiff Ty hidx
      hTyLen hAshort hAstage hcase sigma hgammaNewY hfixedSeed X hXlen _ corr bs K good same
      hgammaSigmaA Pnew hPnew hnoCommonPnew hmeasureNew hmeasurePnew hmeasureOld
      hnewSituationPnew hstarPnew hKstarLen hgammaNewA hgammaSigmaTn terminalTreeOf
  have hterminalOriginal := terminalTreeOf Pnew.coloring Pnew.corresponding
  have hterminalEm := terminalTreeOf P.coloring P.corresponding
  have hterminalPnewTn : Pnew.corresponding.replacementETT.series.data.tree
      (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc = Tn := by
    exact hterminalOriginal.trans (hterminalEm.symm.trans (by rfl))
  have treeMissingColorEq (c₁ c₂ : PartialEdgeColoring E k)
      (hc : c₁ = c₂) (U : TreeSequence G e0) :
      TreeMissingColors c₁ U = TreeMissingColors c₂ U := by
    cases hc
    rfl
  have missingColorEq (c₁ c₂ : PartialEdgeColoring E k)
      (hc : c₁ = c₂) (v : V) :
      MissingColors G c₁ v = MissingColors G c₂ v := by
    cases hc
    rfl
  have hPnewStarLen :
      (HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length = A.length := by
    change (HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount)).length =
      (HierarchyStarredStage H q).length
    rw [hstarPnew]
  have hgammaNewTerminal : gamma ∈ TreeMissingColors Pnew.coloring
      (Pnew.corresponding.replacementETT.series.data.tree
        (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc) := by
    exact @helper_hgammaNewTerminal_1425 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hsituation) (@alpha) (@gamma) (@Pnew) (@hPnew) (@hgammaSigmaTn) (@hterminalPnewTn)
        (@treeMissingColorEq)
  have hnormalizedNew :
      (0 < K.dividerCount ∧ gamma ∈ TreeMissingColors Pnew.coloring
        (K.stage ⟨K.dividerCount, by omega⟩)) ∨
      (K.dividerCount = 0 ∧
        gamma ∈ TreeMissingColors Pnew.coloring
          (Pnew.corresponding.replacementETT.series.data.tree
            (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc)) := by
    rcases hcase with hp | hz
    · left
      have hcount : H.dividerCount = K.dividerCount := same.1.2.1
      refine ⟨?_, ?_⟩
      · simpa [hcount] using hp.1
      · have hgammaKstage : gamma ∈ TreeMissingColors sigma
            (K.stage ⟨K.dividerCount, by omega⟩) := by
          rw [← hmeasureNew.2.2, ← hAstage hp.1]
          exact hgammaSigmaA
        rw [treeMissingColorEq Pnew.coloring sigma hPnew _]
        exact hgammaKstage
    · right
      have hcount : H.dividerCount = K.dividerCount := same.1.2.1
      refine ⟨?_, ?_⟩
      · simpa [hcount] using hz.1
      · exact hgammaNewTerminal
  have hstartNew :
      gamma ∈ TreeMissingColors Pnew.coloring
          (HierarchyStarredStage K (Fin.last K.dividerCount)) ∧
        gamma ∈ MissingColors G Pnew.coloring y := by
    rw [hPnew]
    exact ⟨hgammaNewA, hgammaNewY⟩
  have hstartPnew :
      gamma ∈ TreeMissingColors Pnew.coloring
          (HierarchyStarredStage Pnew.counterexample.hierarchy
            (Fin.last Pnew.counterexample.hierarchy.dividerCount)) ∧
        gamma ∈ MissingColors G Pnew.coloring
      (T.vertex (Fin.last T.length)) := by
    exact @helper_hstartPnew_1464 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hsituation) (@alpha) (@gamma) (@hgammaNewY) (@hgammaSigmaA) (@Pnew) (@hPnew)
        (@hstarPnew) (@treeMissingColorEq) (@missingColorEq)
  have hcountKP : K.dividerCount =
      Pnew.counterexample.hierarchy.dividerCount := by
    calc
      K.dividerCount = H.dividerCount := same.1.2.1.symm
      _ = C.hierarchy.dividerCount := P.sameGood.1.2.1.symm
      _ = Pnew.counterexample.hierarchy.dividerCount := Pnew.sameGood.1.2.1
  have hstageKP : K.stage ⟨K.dividerCount, by omega⟩ =
      Pnew.counterexample.hierarchy.stage
        ⟨Pnew.counterexample.hierarchy.dividerCount, by omega⟩ := by
    calc
      K.stage ⟨K.dividerCount, by omega⟩ = H.stage ⟨H.dividerCount, by omega⟩ :=
        hmeasureNew.2.2.symm
      _ = C.hierarchy.stage ⟨C.hierarchy.dividerCount, by omega⟩ :=
        hmeasureOld.2.2.symm
      _ = Pnew.counterexample.hierarchy.stage
          ⟨Pnew.counterexample.hierarchy.dividerCount, by omega⟩ :=
        hmeasurePnew.2.2
  have hnormalizedPnew :
      (0 < Pnew.counterexample.hierarchy.dividerCount ∧
        gamma ∈ TreeMissingColors Pnew.coloring
          (Pnew.counterexample.hierarchy.stage
            ⟨Pnew.counterexample.hierarchy.dividerCount, by omega⟩)) ∨
      (Pnew.counterexample.hierarchy.dividerCount = 0 ∧
        gamma ∈ TreeMissingColors Pnew.coloring
          (Pnew.corresponding.replacementETT.series.data.tree
            (Fin.last Pnew.corresponding.replacementETT.rounds).castSucc)) := by as_aux_lemma =>
    rcases hnormalizedNew with hp | hz
    · left
      refine ⟨?_, ?_⟩
      · rw [← hcountKP]
        exact hp.1
      · rw [← hstageKP]
        exact hp.2
    · right
      refine ⟨?_, hgammaNewTerminal⟩
      rw [← hcountKP]
      exact hz.1
  exact @helper_continuation_2499 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hvertexMissing) (@P) (@alpha) (@e1) (@he1) (@hfirst) (@hell) (@htwo) (@hsum) (@hBlen)
      (@gamma) (@hgammaNe) (@htaildiff) (@hidx) (@hTyLen) (@hAshort) (@hfixedSeed) (@hXlen)
      (@corr) (@bs) (@K) (@Pnew) (@hPnew) (@hnoCommonPnew) (@hnewSituationPnew) (@hKstarLen)
      (@hPnewStarLen) (@hstartPnew) (@hnormalizedPnew)
private theorem helper_continuation_2461.{u_1, u_2} :
    helperContinuation2461Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing P hsituation alpha e1 he1
      hfirst mu em bm Cm cm H q A ell B y hell htwo hAT hsum hBlen hAB n Tn gamma hgammaA
      hgammaNe hgammaTn hmissingGammaB hmissingAlphaB hne ig vg htaildiff Ty hidx hTyLen Q
      hAshort hyNotA hdisjoint hpath hAstage hcase sigma hmissingBEquality hgammaNewY hfixedSeed
      X hXlen hAX hAXstrict hXB hfixedPrefix hstoredFirst hgammaCutoff hTnA routes hsplitMissing
  obtain ⟨_, modifiedColoring, corr, hmax, bs, K, good, same⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 P.corresponding.replacementInput T mu em bm Cm cm
      gamma alpha hne
      (by
        change gamma ∈ TreeMissingColors mu
            (HierarchyFullTailPrefix Cm (HierarchyFullTailLength Cm - 1)) ∧
          alpha ∈ TreeMissingColors mu
            (HierarchyFullTailPrefix Cm (HierarchyFullTailLength Cm - 1))
        exact ⟨hmissingGammaB, hmissingAlphaB⟩)
      (Sum.inl y) hpath sigma rfl hcase
      hdisjoint X hAX hAXstrict hXB hfixedPrefix routes.1 routes.2 hsplitMissing
      hmissingBEquality hstoredFirst hgammaCutoff
  have hgammaSigmaA : gamma ∈ TreeMissingColors sigma A := by
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgammaA
    exact Finset.mem_biUnion.mpr
      ⟨v, hv, (hmissingBEquality v (TreeSequenceInitialSegmentVertexSetSubset hAB hv)).symm ▸ hmv⟩
  have hvTerminal : y ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last T.length, rfl⟩
  let Cs : HierarchyCounterexample bs := by
    exact @helperCs1237 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hAT) (@gamma)
        (@hyNotA) (@hgammaNewY) (@corr) (@hmax) (@bs) (@K) (@good) (@hgammaSigmaA) (@hvTerminal)
  obtain ⟨Pnew, hPnew⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    P sigma corr bs Cs same
  by_cases hnoCommonPnew :
      ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
        Disjoint
          (MissingColors G Pnew.coloring
            ((HierarchyFullTailPrefix C i).vertex
              (Fin.last (HierarchyFullTailPrefix C i).length)))
          (MissingColors G Pnew.coloring y)
  swap
  · exact @helper_branch_1321 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation) (@Pnew)
      (@hnoCommonPnew)
  have hmeasureNew := P2752_T2_HierarchyMeasures H K same.1
  have hmeasurePnew := P2752_T2_HierarchyMeasures C.hierarchy
    Pnew.counterexample.hierarchy Pnew.sameGood.1
  have hmeasureOld := P2752_T2_HierarchyMeasures C.hierarchy H P.sameGood.1
  have hnewSituation : HierarchyPathNumber K = 1 := by
    calc
      HierarchyPathNumber K = HierarchyPathNumber H := hmeasureNew.2.1.symm
      _ = 1 := hsituation
  have hnewSituationPnew :
      HierarchyPathNumber Pnew.counterexample.hierarchy = 1 := by
    calc
      HierarchyPathNumber Pnew.counterexample.hierarchy =
          HierarchyPathNumber C.hierarchy := hmeasurePnew.2.1.symm
      _ = HierarchyPathNumber H := hmeasureOld.2.1
      _ = 1 := hsituation
  have hstarNew : HierarchyStarredStage H q =
      HierarchyStarredStage K (Fin.last K.dividerCount) := hmeasureNew.1
  have hstarPnew : HierarchyStarredStage H q =
      HierarchyStarredStage Pnew.counterexample.hierarchy
        (Fin.last Pnew.counterexample.hierarchy.dividerCount) :=
    hmeasureOld.1.symm.trans hmeasurePnew.1
  have hKstarLen : (HierarchyStarredStage K (Fin.last K.dividerCount)).length =
      A.length := by
    change (HierarchyStarredStage K (Fin.last K.dividerCount)).length =
      (HierarchyStarredStage H q).length
    rw [← hstarNew]
  have hgammaNewA : gamma ∈ TreeMissingColors sigma
      (HierarchyStarredStage K (Fin.last K.dividerCount)) := by
    rw [← hstarNew]
    exact hgammaSigmaA
  have hgammaSigmaTn : gamma ∈ TreeMissingColors sigma Tn := by
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgammaTn
    have hvA := TreeSequenceInitialSegmentVertexSetSubset hTnA hv
    have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hvA
    exact Finset.mem_biUnion.mpr ⟨v, hv, (hmissingBEquality v hvB).symm ▸ hmv⟩
  have hterminalTree : corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
    exact corr.terminalData.1
  have terminalTreeOf (coloring : PartialEdgeColoring E k)
      (c : CorrespondingExtendedTashkinovTree G k e0 ett coloring T) :
      c.replacementETT.series.data.tree
          (Fin.last c.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    exact c.terminalData.1
  exact @helper_continuation_2476 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hvertexMissing) (@P) (@hsituation) (@alpha) (@e1) (@he1) (@hfirst) (@hell) (@htwo)
      (@hsum) (@hBlen) (@gamma) (@hgammaNe) (@htaildiff) (@hidx) (@hTyLen) (@hAshort) (@hAstage)
      (@hcase) (@hgammaNewY) (@hfixedSeed) (@hXlen) (@modifiedColoring) (@corr) (@bs) (@K) (@good)
      (@same) (@hgammaSigmaA) (@Pnew) (@hPnew) (@hnoCommonPnew) (@hmeasureNew) (@hmeasurePnew)
      (@hmeasureOld) (@hnewSituationPnew) (@hstarPnew) (@hKstarLen) (@hgammaNewA)
      (@hgammaSigmaTn) (@terminalTreeOf)
private theorem helper_continuation_2492.{u_1, u_2} :
    helperContinuation2492Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing P hsituation alpha noCommon
      e1 he1
      hfirst mu em bm Cm cm H q A ell B y hell htwo hAT hsum hBlen hAB haA n Tn D R hAcore gamma
      hgammaA hgammaR hgammaNe hgammaTn hmissingGammaB hmissingAlphaB hne ig vg htaildiff Ty hidx
      hTyLen Q hAshort hyNotA hdisjoint hpath hAstage hcase hQoutsideA sigma missingOther
      hmissingBEquality hgammaNewY hfixedSeed X hXlen hXT prefixOverlap hAX hAXstrict hXB
  have hfixedPrefix : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      sigma (T.edge t) = mu (T.edge t) := by
    intro t lower upper
    have position : t.val = A.length := by rw [hXlen] at upper; omega
    have equal : t = e1 := Fin.ext (by rw [position, he1])
    rw [equal]
    exact hfixedSeed
  have hstoredFirst : ∀ eta ∈ HierarchyStoredColorsAt H q,
      HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition mu T eta := by
    intro eta member
    have absent := (Finset.mem_sdiff.mp member).2
    have notGamma : eta ≠ gamma := fun equal => absent (equal ▸ hgammaA)
    have notAlpha : eta ≠ alpha := fun equal => absent (equal ▸ haA)
    exact TreeSequenceFirstMissingPositionMembershipCongr
      (fun index => missingOther (T.vertex index) eta notGamma notAlpha)
  have hgammaCutoff : ∀ eta ∈ HierarchyStoredColorsAt H q,
      (gamma ∈ Cm.good.gamma q eta ∨ alpha ∈ Cm.good.gamma q eta) →
        (HierarchyFirstMissingPosition mu T eta).val ≤ X.length := by
    exact @helper_hgammaCutoff_1122 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hsituation) (@alpha) (@e1) (@he1) (@hfirst) (@htwo) (@hsum) (@hBlen) (@gamma)
        (@hgammaR) (@htaildiff) (@hidx) (@hTyLen) (@hAshort) (@hXlen)
  have hfixedA : ∀ t : Fin A.length, sigma (A.edge t) = mu (A.edge t) := by as_aux_lemma =>
    intro t
    obtain ⟨i, hi⟩ := A.attaches t
    have htVertex : A.vertex t.succ ∈ TreeSequenceVertexSet A := by
      simp [TreeSequenceVertexSet]
    have htIncident : Incident G (A.vertex t.succ) (A.edge t) := by
      change A.vertex t.succ ∈ G.ends (A.edge t)
      rw [hi]
      simp
    by_cases hQe : Sum.inr (A.edge t) ∈ Q
    · exact @helper_branch_1162 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha) (@gamma) (@hQoutsideA) (@t) (@htVertex) (@htIncident) (@hQe)
    · simp [sigma, TwoColorComponentSwap, Q, hQe]
  have hfixedX : ∀ t : Fin X.length, sigma (X.edge t) = mu (X.edge t) := by
    exact @helper_hfixedX_1181 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha) (@e1) (@he1) (@htwo) (@hAT) (@hsum) (@hBlen) (@gamma) (@htaildiff) (@hidx)
        (@hTyLen) (@hAshort) (@hfixedSeed) (@hXlen) (@hXT) (@hfixedA)
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) : TreeSequenceInitialSegment S W := by
    exact hSU.trans hUW
  have coreToA := H.coreInitialSegmentOfStarredStage (Fin.last H.dividerCount)
  have TnToCore : TreeSequenceInitialSegment Tn bm.core := by
    exact bm.lastRoundInitialSegmentCore
  have hTnA : TreeSequenceInitialSegment Tn A := segTrans TnToCore coreToA
  have transportRoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence mu S X) :
      TashkinovAugmentationSequence sigma S X := by as_aux_lemma =>
    unfold TashkinovAugmentationSequence at hroute ⊢
    refine Relation.ReflTransGen.head_induction_on hroute ?_ ?_
    · exact Relation.ReflTransGen.refl
    · exact @helper_branch_1237 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha)  (@htwo) (@hsum) (@hBlen) (@gamma) (@htaildiff) (@hidx) (@hTyLen)
        (@hAshort) (@hmissingBEquality) (@hXB) (@hfixedX) (@segTrans)
  have routes :
      ((em.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn X) ∨
        ((em.series.data.kind n = some TashkinovExtensionKind.SE ∨
            em.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            em.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence sigma seed X)) ∧
        TashkinovAugmentationSequence mu X T := by as_aux_lemma =>
    have old := P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu em
    rcases old with ⟨hkind, hroute⟩ |
      ⟨hkind, f, seed, hedges, hadjoin, hincident, hcolor, hroute⟩
    · have hTnX := segTrans hTnA hAX
      have hrouteX := TashkinovAugmentationSequenceRestrict mu Tn X T hroute hTnX hXT
      exact ⟨Or.inl ⟨hkind, transportRoute Tn hrouteX⟩,
        TashkinovAugmentationSequenceSuffix mu Tn X T hroute hTnX hXT⟩
    · exact @helper_branch_1267 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha) (@e1) (@htwo) (@hsum) (@hBlen) (@gamma) (@htaildiff) (@hidx) (@hTyLen)
        (@hAshort) (@hXlen) (@hXT) (@prefixOverlap) (@hTnA) (@transportRoute) (@hkind) (@f)
        (@seed) (@hedges) (@hadjoin) (@hroute)
  have hsplitMissing : gamma ∈ TreeMissingColors sigma X ∧ alpha ∈ TreeMissingColors sigma X := by
    exact @helper_hsplitMissing_1278 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hsituation) (@alpha) (@e1) (@htwo) (@hsum) (@hBlen) (@hAB) (@haA) (@gamma) (@hgammaA)
        (@htaildiff) (@hidx) (@hTyLen) (@hAshort) (@hmissingBEquality) (@hAX)
  exact @helper_continuation_2461 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hvertexMissing) (@P) (@hsituation) (@alpha) (@e1) (@he1) (@hfirst) (@hell) (@htwo) (@hAT)
      (@hsum) (@hBlen) (@hAB) (@gamma) (@hgammaA) (@hgammaNe) (@hgammaTn) (@hmissingGammaB)
      (@hmissingAlphaB) (@hne) (@htaildiff) (@hidx) (@hTyLen) (@hAshort) (@hyNotA) (@hdisjoint)
      (@hpath) (@hAstage) (@hcase) (@hmissingBEquality) (@hgammaNewY) (@hfixedSeed) (@hXlen)
      (@hAX) (@hAXstrict) (@hXB) (@hfixedPrefix) (@hstoredFirst) (@hgammaCutoff) (@hTnA)
      (@routes) (@hsplitMissing)
private theorem helper_continuation_2398.{u_1, u_2} :
    helperContinuation2398Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing P hsituation alpha
      hnormalized noCommon e1 he1 hfirst mu em bm Cm cm H q A ell B y hell htwo helem hAT hsum
      hBlen hBT
      hAB haA haY n Tn D R hAcore gamma hgammaA hgammaR hgammaNe hgammaTn hmissingGammaB
      hmissingAlphaB hne ig ia vg hgamvg hvgInA hAlphaAtFirst hiaInA htaildiff Ty hidx hTyLen
      hchange hsame hinterchangeable J Q self
  have leaf (v : V) (hv : gamma ∈ MissingColors G mu v ∨ alpha ∈ MissingColors G mu v) :
      Set.Subsingleton (J.neighborSet (Sum.inl v)) := by
    exact TwoColorMissingVertexNeighborsSubsingleton G mu cm.proper gamma alpha v hv
  have hAshort : A.length + 1 < T.length := by omega
  have hyNotA : y ∉ TreeSequenceVertexSet A := by
    exact @helper_hyNotA_838 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha) (@e1) (@htwo) (@hAT) (@hsum) (@hBlen) (@gamma) (@htaildiff) (@hidx) (@hTyLen)
  have hvgNeY : vg ≠ y := by
    intro h
    exact hyNotA (h ▸ hvgInA)
  have hiaNeY : T.vertex ia ≠ y := by
    intro h
    exact hyNotA (h ▸ hiaInA)
  have hdisjoint : Disjoint Q
      (TwoColorComponent G mu gamma alpha (Sum.inl vg)) := by as_aux_lemma =>
    rcases TwoColorComponentsDisjoint G mu gamma alpha (Sum.inl y) (Sum.inl vg) with heq | hd
    · exact @helper_branch_859 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha) (@noCommon) (@haY) (@gamma) (@hgamvg) (@hAlphaAtFirst) (@hsame) (@self) (@leaf)
        (@hvgNeY)
            (@hiaNeY) (@heq)
    · exact hd
  have hpath : TwoColorPathComponent G mu gamma alpha (Sum.inl y) :=
    ⟨hne, Sum.inl y, self y, leaf y (Or.inr haY)⟩
  have hAstage (hp : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact @helper_hAstage_932 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha) (@e1) (@hsum) (@gamma) (@htaildiff) (@hp)
  have hcase :
      (0 < H.dividerCount ∧ gamma ∈ TreeMissingColors mu
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧
        (gamma ∈ TreeMissingColors mu Tn ∨
          (gamma ∈ TreeMissingColors mu A ∧
            gamma ∉ TashkinovStoredColors em.series.data n ∧
            alpha ∉ TashkinovStoredColors em.series.data n))) := by
    rcases hnormalized with hp | hz
    · exact Or.inl ⟨hp.1, by rw [← hAstage hp.1]; exact hgammaA⟩
    · exact Or.inr ⟨hz.1, Or.inl hgammaTn⟩
  have hvgPath : TwoColorPathComponent G mu gamma alpha (Sum.inl vg) :=
    ⟨hne, Sum.inl vg, self vg, leaf vg (Or.inl hgamvg)⟩
  have hQoutsideA : ∀ w, w ∈ TreeSequenceVertexSet A →
      Sum.inl w ∉ Q := by
    exact @helper_hQoutsideA_956 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hsituation) (@alpha) (@gamma) (@hvgInA) (@hinterchangeable) (@self) (@hdisjoint)
        (@hpath) (@hvgPath)
  let sigma := TwoColorComponentSwap G mu gamma alpha (Sum.inl y)
  obtain ⟨missingOutside, missingGammaToAlpha, missingAlphaToGamma, missingOther⟩ :=
    TwoColorComponentSwapMissingBehavior G mu gamma alpha hne cm.proper (Sum.inl y)
  have hmissingBEquality : ∀ v, v ∈ TreeSequenceVertexSet B →
      MissingColors G sigma v = MissingColors G mu v := by as_aux_lemma =>
    clear * - J helem hAB hvgInA hiaInA hdisjoint hsame self hgamvg hAlphaAtFirst missingOther
        missingOutside hne
    intro w hw
    by_cases hwQ : Sum.inl w ∈ Q
    · exact @helper_branch_975 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@helem)
        (@hAB) (@gamma) (@hgamvg) (@hvgInA) (@hAlphaAtFirst) (@hiaInA) (@hsame) (@self)
        (@hdisjoint) (@missingOther) (@w) (@hw) (@hwQ)
    · exact missingOutside w hwQ
  have hgammaNewY : gamma ∈ MissingColors G sigma y :=
    missingAlphaToGamma y (self y) haY
  have he1Incident : TreeIncidentEdge A (T.edge e1) := by
    exact @helper_he1Incident_1026 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hsituation) (@alpha) (@e1) (@he1) (@hAT) (@hsum) (@hBlen) (@gamma) (@htaildiff) (@hidx)
        (@hTyLen)
  have he1notQ : Sum.inr (T.edge e1) ∉ Q := by
    exact @helper_he1notQ_1042 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha) (@e1) (@hfirst) (@gamma) (@hQoutsideA) (@he1Incident)
  have hfixedSeed : sigma (T.edge e1) = mu (T.edge e1) := by
    simp [sigma, TwoColorComponentSwap, Q, he1notQ]
  let X := TreeSequencePrefix T (A.length + 1)
    (by have := A.positive; omega) (by have := hAshort; omega)
  have hXlen : X.length = A.length + 1 := rfl
  have hXT : TreeSequenceInitialSegment X T :=
    TreeSequenceInitialSegment.prefix_segment T (A.length + 1) (by omega) hAshort.le
  have prefixOverlap {S U : TreeSequence G e0}
      (hST : TreeSequenceInitialSegment S T)
      (hUT : TreeSequenceInitialSegment U T) (hle : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := hUT.of_common_extension hST hle
  have hleAX : A.length ≤ X.length := by
    rw [hXlen]
    omega
  have hAX : TreeSequenceInitialSegment A X := prefixOverlap hAT hXT hleAX
  have hAXstrict : A.length < X.length := by rw [hXlen]; omega
  have hXB : TreeSequenceInitialSegment X B := by
    have lengthBound : X.length ≤ B.length := by
      rw [hBlen, hXlen]
      omega
    exact prefixOverlap hXT hBT lengthBound
  exact @helper_continuation_2492 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hvertexMissing) (@P) (@hsituation) (@alpha) (@noCommon) (@e1) (@he1) (@hfirst)
      (@hell) (@htwo) (@hAT) (@hsum) (@hBlen) (@hAB) (@haA) (@hAcore) (@gamma) (@hgammaA)
      (@hgammaR) (@hgammaNe) (@hgammaTn) (@hmissingGammaB) (@hmissingAlphaB) (@hne) (@htaildiff)
      (@hidx) (@hTyLen) (@hAshort) (@hyNotA) (@hdisjoint) (@hpath) (@hAstage) (@hcase)
      (@hQoutsideA) (@missingOther) (@hmissingBEquality) (@hgammaNewY) (@hfixedSeed) (@hXlen)
      (@hXT) (@prefixOverlap) (@hAX) (@hAXstrict) (@hXB)
private theorem helper_continuation_2395.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyPathNumber P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k), (0 : ℕ) < P.counterexample.hierarchy.dividerCount ∧ alpha ∈
        TreeMissingColors P.coloring (P.counterexample.hierarchy.stage
        (⟨P.counterexample.hierarchy.dividerCount,
    have _ : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a :
        ¬P.counterexample.hierarchy.dividerCount < P.counterexample.hierarchy.dividerCount + (2 :
        ℕ)) ↦
    by omega
    ⟩ : Fin (P.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        P.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ alpha ∈ TreeMissingColors P.coloring
        (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc) → (
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)), Disjoint (MissingColors G
        P.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C
        i).length))) (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) →
    ∀ (e1 : Fin T.length), (↑e1 : ℕ) = (HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).length → P.coloring (T.edge e1) = some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell → (2 : ℕ) ≤ ell →
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T
        → A.length + ell = T.length → B.length = T.length - (1 : ℕ) → TreeSequenceInitialSegment B
        T → TreeSequenceInitialSegment A B → alpha ∈ TreeMissingColors mu A → alpha ∈
        MissingColors G mu y → alpha ∈ TreeMissingColors mu B →
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q); (H.dividerCount = (0 : ℕ) → A =
        bm.core) → (
    ∃ gamma ∈ TreeMissingColors mu A, gamma ∉ R ∧ gamma ≠ alpha ∧ gamma ∈ TreeMissingColors mu Tn
        ∧ TreeColorSetClosed G mu A ({ gamma } : Finset (Fin k)) ∧ (H.dividerCount = (0 : ℕ) ∨
        gamma ∉ (HierarchyStoredColorsAt H q).biUnion (Cm.good.gamma (⟨H.dividerCount - (1 : ℕ),
    by
                            have := GoldbergSeymour.TreeSequence.positive T
                            omega
    ⟩ : Fin (H.dividerCount + (1 : ℕ)))))) → (HierarchyEligibleCommonMissingIndices G k e0 input T
        phi ett base C ctx).Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing P hsituation alpha
      hnormalized noCommon e1 he1 hfirst mu em bm Cm cm H q A ell B y hell htwo helem hAT hsum
      hBlen hBT
      hAB haA haY hmissingB n Tn D R hAcore hgammaData
  obtain ⟨gamma, hgammaA, hgammaR, hgammaNe, hgammaTn, hgammaClosed,
    hgammaPrev⟩ := hgammaData
  have hmissingGammaB : gamma ∈ TreeMissingColors mu B := by
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgammaA
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hmv⟩
  have hmissingAlphaB : alpha ∈ TreeMissingColors mu B := hmissingB
  have hne : gamma ≠ alpha := hgammaNe
  have firstSpec (rho : PartialEdgeColoring E k) (c : Fin k)
      (i : Fin (T.length + 1)) (hi : c ∈ MissingColors G rho (T.vertex i)) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
        HierarchyFirstMissingPosition rho T c ≤ i := by
    exact TreeSequenceFirstMissingPositionWitness hi
  obtain ⟨vgWitness, hvgA, hvg⟩ := Finset.mem_biUnion.mp hgammaA
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hvgA
  obtain ⟨igA, higA⟩ := hvgA
  let igT := Fin.castLE (Nat.succ_le_succ hAT.1) igA
  have hgamig : gamma ∈ MissingColors G mu (T.vertex igT) := by
    rw [hAT.2.1 igA, higA]
    exact hvg
  let ig := HierarchyFirstMissingPosition mu T gamma
  let ia := HierarchyFirstMissingPosition mu T alpha
  let vg := T.vertex ig
  have hgamvg : gamma ∈ MissingColors G mu vg := (firstSpec mu gamma igT hgamig).1
  have higBound : ig.val ≤ A.length := by
    have hm := (firstSpec mu gamma igT hgamig).2
    change ig.val ≤ igA.val at hm
    have := igA.isLt
    omega
  have hvgInA : vg ∈ TreeSequenceVertexSet A := by
    let i : Fin (A.length + 1) := ⟨ig.val, by omega⟩
    have hi : Fin.castLE (Nat.succ_le_succ hAT.1) i = ig := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, (hAT.2.1 i).symm.trans (congrArg T.vertex hi)⟩
  have hAlphaAtFirst : alpha ∈ MissingColors G mu (T.vertex ia) := by
    exact @helper_hAlphaAtFirst_721 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@hsituation) (@alpha) (@hAT) (@haA) (@firstSpec)
  have hiaBound : ia.val ≤ A.length := by
    exact @helper_hiaBound_730 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation)
        (@alpha) (@e1) (@hAT) (@haA) (@gamma) (@firstSpec)
  have hiaInA : T.vertex ia ∈ TreeSequenceVertexSet A := by
    let iA : Fin (A.length + 1) := ⟨ia.val, by omega⟩
    have hiA : Fin.castLE (Nat.succ_le_succ hAT.1) iA = ia := Fin.ext rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨iA, (hAT.2.1 iA).symm.trans (congrArg T.vertex hiA)⟩
  have horderedUnused :
      (gamma ∉ TreeMissingColors mu A ∨ alpha ∉ TreeMissingColors mu A) →
        TreeVertexOrder T vg (T.vertex ia) ∧
          gamma ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
            A.length ≤ t.val ∧ t.val < ia.val ∧ mu (T.edge t) = some c) := by
    intro h
    rcases h with h | h
    · exact (h hgammaA).elim
    · exact (h haA).elim
  have htaildiff : T.length - A.length = ell := by omega
  have equalTrees {S U : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hlen : S.length = U.length) : S = U := by
    exact hSU.eq_of_length_eq hlen
  let Ty := TreeSequencePrefix T (min (A.length + (T.length - A.length - 1)) T.length)
    (by have := A.positive; have := T.positive; omega) (Nat.min_le_right _ _)
  have hTyT : TreeSequenceInitialSegment Ty T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hsumA : A.length + (T.length - A.length) = T.length :=
    Nat.add_sub_of_le hAT.1
  have hidx : A.length + (T.length - A.length - 1) = T.length - 1 := by
    calc
      A.length + (T.length - A.length - 1) =
          (A.length + (T.length - A.length)) - 1 := by omega
      _ = T.length - 1 := by rw [hsumA]
  have hTyLen : Ty.length = B.length := by
    change min (A.length + (T.length - A.length - 1)) T.length = B.length
    rw [hidx, Nat.min_eq_left (by omega), hBlen]
  have hBToTy : TreeSequenceInitialSegment B Ty := by
    exact hTyT.of_common_extension hBT hTyLen.symm.le
  have hBTy : B = Ty := equalTrees hBToTy hTyLen.symm
  have hchange := ChangeLemma G k e0 P.corresponding.replacementInput T mu em bm Cm
    cm.proper cm.oneEdgeUncolored cm.lowerRung cm.fewerDividers
    cm.lexicographicMinimality helem cm.largeMissingSet gamma alpha hne
    (by
      change gamma ∈ TreeMissingColors mu Ty ∧ alpha ∈ TreeMissingColors mu Ty
      rw [← hBTy]
      exact ⟨hmissingGammaB, hmissingAlphaB⟩) horderedUnused
  have hchangeClosed := hchange.2.2 ⟨hgammaA, hgammaClosed⟩
  have hsame : TwoColorComponent G mu gamma alpha (Sum.inl vg) =
      TwoColorComponent G mu gamma alpha (Sum.inl (T.vertex ia)) := hchangeClosed.1
  have hinterchangeable : TreeInterchangeable G A mu gamma alpha := hchangeClosed.2
  let J := TwoColorIncidenceGraph G mu gamma alpha
  let Q := TwoColorComponent G mu gamma alpha (Sum.inl y)
  have self (v : V) : Sum.inl v ∈ TwoColorComponent G mu gamma alpha (Sum.inl v) := by
    change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk (Sum.inl v)
    rfl
  exact @helper_continuation_2398 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hvertexMissing) (@P) (@hsituation) (@alpha) (@hnormalized) (@noCommon) (@e1) (@he1)
      (@hfirst) (@hell) (@htwo) (@helem) (@hAT) (@hsum) (@hBlen) (@hBT) (@hAB) (@haA) (@haY)
      (@hAcore) (@gamma) (@hgammaA) (@hgammaR) (@hgammaNe) (@hgammaTn) (@hmissingGammaB)
      (@hmissingAlphaB) (@hne) (@hgamvg) (@hvgInA) (@hAlphaAtFirst) (@hiaInA) (@htaildiff)
      (@hidx) (@hTyLen) (@hchange) (@hsame) (@hinterchangeable) (@self)
private theorem helper_continuation_2508.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C), (
    ∀ (mu : PartialEdgeColoring E k), IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
    ∀ (v : V), (MissingColors G mu v).Nonempty) →
    ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyPathNumber P.counterexample.hierarchy = (1 : ℕ) →
    ∀ (alpha : Fin k), (0 : ℕ) < P.counterexample.hierarchy.dividerCount ∧ alpha ∈
        TreeMissingColors P.coloring (P.counterexample.hierarchy.stage
        (⟨P.counterexample.hierarchy.dividerCount,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (P.counterexample.hierarchy.dividerCount + (2 : ℕ)))) ∨
        P.counterexample.hierarchy.dividerCount = (0 : ℕ) ∧ alpha ∈ TreeMissingColors P.coloring
        (P.corresponding.replacementETT.series.data.tree (Fin.last
        P.corresponding.replacementETT.rounds).castSucc) → (
    ∀ i ∈ Finset.Icc (1 : ℕ) (HierarchyFullTailLength C - (1 : ℕ)), Disjoint (MissingColors G
        P.coloring ((HierarchyFullTailPrefix C i).vertex (Fin.last (HierarchyFullTailPrefix C
        i).length))) (MissingColors G P.coloring (T.vertex (Fin.last T.length)))) →
    ∀ (e1 : Fin T.length), (↑e1 : ℕ) = (HierarchyStarredStage P.counterexample.hierarchy (Fin.last
        P.counterexample.hierarchy.dividerCount)).length → P.coloring (T.edge e1) = some alpha →
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := HierarchyFullTailLength Cm;
    let B : TreeSequence G e0 := HierarchyFullTailPrefix Cm (ell - (1 : ℕ));
    let y : V := T.vertex (Fin.last T.length); HierarchyFullTailLength C = ell → (2 : ℕ) ≤ ell →
        ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) → TreeSequenceInitialSegment A T
        → A.length + ell = T.length → B.length = T.length - (1 : ℕ) → TreeSequenceInitialSegment B
        T → TreeSequenceInitialSegment A B → alpha ∈ TreeMissingColors mu A → alpha ∈
        MissingColors G mu y → alpha ∈ TreeMissingColors mu B →
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q); (H.dividerCount = (0 : ℕ) → A =
        bm.core) → (H.dividerCount = (0 : ℕ) →
    ∃ gamma ∈ TreeMissingColors mu A, gamma ∉ R ∧ gamma ≠ alpha ∧ gamma ∈ TreeMissingColors mu Tn
        ∧ TreeColorSetClosed G mu A ({ gamma } : Finset (Fin k))) →
        (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hvertexMissing P hsituation alpha
      hnormalized noCommon e1 he1 hfirst mu em bm Cm cm H q A ell B y hell htwo helem hAT hsum
      hBlen hBT
      hAB haA haY hmissingB n Tn D R hAcore hgammaZero
  have hgammaPositive (hz : 0 < H.dividerCount) : ∃ gamma : Fin k,
      gamma ∈ TreeMissingColors mu A ∧ gamma ∉ R ∧ gamma ≠ alpha ∧
        gamma ∈ TreeMissingColors mu Tn ∧
        TreeColorSetClosed G mu A {gamma} ∧
        gamma ∉ ((HierarchyStoredColorsAt H q).biUnion
          (Cm.good.gamma (⟨H.dividerCount - 1, by omega⟩ : Fin (H.dividerCount + 1)))) := by
              as_aux_lemma =>
    clear * - P mu em bm Cm cm H q A Tn R D alpha hz
    let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
    have hq : q = i.succ := by
      apply Fin.ext
      simp [i, q]
      omega
    have hAeq : A = H.stage ⟨H.dividerCount, by omega⟩ := by
      exact @helper_hAeq_523 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hz)
    have segTrans {S U W : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U)
        (hUW : TreeSequenceInitialSegment U W) : TreeSequenceInitialSegment S W := by
      exact hSU.trans hUW
    have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
        TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
          (H.stage ⟨a + d, by omega⟩) := by
      exact H.stageInitialSegmentOfLE _ _ (by change a ≤ a + d; exact Nat.le_add_right _ _)
    have coreToA : TreeSequenceInitialSegment bm.core A := by
      rw [hAeq]
      have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
      have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
      simpa [he] using segTrans H.coreInsideFirst hs
    have TnToCore : TreeSequenceInitialSegment Tn bm.core := by
      exact bm.lastRoundInitialSegmentCore
    have hTnA := segTrans TnToCore coreToA
    let Dprev := HierarchyStoredColorsAt H i.succ
    let Rprev := Dprev.biUnion (Cm.good.gamma i.castSucc)
    obtain ⟨eta, hη, _⟩ := Cm.good.uniqueRefresh i
    rcases hη with ⟨heta, hpair, hcopy⟩
    have hRsub : R ⊆ Rprev ∪ Cm.good.gamma i.succ eta := by
      exact @helper_hRsub_564 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hz) (@hq) (@eta)
          (@hcopy)
    have hRprevCard : Rprev.card ≤ 2 * em.rounds := by
      exact @helper_hRprevCard_578 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@hz) (@hq)
    have hpairCard : (Cm.good.gamma i.succ eta).card ≤ 2 := by
      have hp := Cm.good.twoColors i.succ eta (by simpa [D, hq] using heta)
      exact le_of_eq hp
    have hforbiddenCard : (Rprev ∪ R ∪ {alpha}).card ≤ 2 * em.rounds + 3 := by
      exact @helper_hforbiddenCard_595 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@hz) (@eta) (@hRsub) (@hRprevCard) (@hpairCard)
    have hlarge : 2 * em.rounds + 11 ≤ (TreeMissingColors mu Tn).card := by
      simpa [Tn, n] using cm.largeMissingSet
    let S := TreeMissingColors mu Tn \ (Rprev ∪ R ∪ {alpha})
    have hSne : S.Nonempty := by
      exact @helper_hSne_623 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hz)
          (@eta) (@hforbiddenCard) (@hlarge)
    obtain ⟨gamma, hg⟩ := hSne
    have hgparts := Finset.mem_sdiff.mp hg
    have hgnot := hgparts.2
    have hgA : gamma ∈ TreeMissingColors mu A := by
      obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgparts.1
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hmv⟩
    have hgR : gamma ∉ R := by
      intro h
      exact hgnot (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hgAlpha : gamma ≠ alpha := by
      intro h
      exact hgnot (Finset.mem_union_right _ (by simp [h]))
    have hgPrev : gamma ∉ Rprev := by
      intro h
      exact hgnot (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hminus : TreeColorSetMinusClosed G mu A Rprev := by
      exact @helper_hminus_645 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hz)
          (@hq) (@hAeq) (@eta)
    have hminusClosed :
        TreeColorSetClosed G mu A (TreeMissingColors mu A \ Rprev) := hminus
    have hgClosed : TreeColorSetClosed G mu A {gamma} := by
      intro c hc
      have hcgamma : c = gamma := Finset.mem_singleton.mp hc
      subst c
      exact hminusClosed gamma (Finset.mem_sdiff.mpr ⟨hgA, hgPrev⟩)
    have hgPrev' : gamma ∉ ((HierarchyStoredColorsAt H q).biUnion
        (Cm.good.gamma (⟨H.dividerCount - 1, by omega⟩ : Fin (H.dividerCount + 1))) : Finset (Fin
            k)) := by
      change gamma ∉ ((HierarchyStoredColorsAt H i.succ).biUnion
        (Cm.good.gamma i.castSucc)) at hgPrev
      simpa [q, hq, i] using hgPrev
    exact ⟨gamma, hgA, hgR, hgAlpha, hgparts.1, hgClosed, hgPrev'⟩
  have hgammaData : ∃ gamma : Fin k,
      gamma ∈ TreeMissingColors mu A ∧ gamma ∉ R ∧ gamma ≠ alpha ∧
        gamma ∈ TreeMissingColors mu Tn ∧ TreeColorSetClosed G mu A {gamma} ∧
        (H.dividerCount = 0 ∨ gamma ∉ ((HierarchyStoredColorsAt H q).biUnion
          (Cm.good.gamma (⟨H.dividerCount - 1, by omega⟩ : Fin (H.dividerCount + 1))))) := by
              as_aux_lemma =>
    by_cases hz : H.dividerCount = 0
    · obtain ⟨gamma, hA, hR, hne, hTn, hclosed⟩ := hgammaZero hz
      exact ⟨gamma, hA, hR, hne, hTn, hclosed, Or.inl hz⟩
    · have hp : 0 < H.dividerCount := Nat.pos_of_ne_zero hz
      obtain ⟨gamma, hA, hR, hne, hTn, hclosed, hprev⟩ := hgammaPositive hp
      exact ⟨gamma, hA, hR, hne, hTn, hclosed, Or.inr hprev⟩
  exact @helper_continuation_2395 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hvertexMissing) (@P) (@hsituation) (@alpha) (@hnormalized) (@noCommon) (@e1) (@he1)
      (@hfirst) (@hell) (@htwo) (@helem) (@hAT) (@hsum) (@hBlen) (@hBT) (@hAB) (@haA) (@haY)
      (@hmissingB) (@hAcore) (@hgammaData)
private theorem helper_branch_4026.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q); A = bm.core → q = (0 : Fin
        (H.dividerCount + (1 : ℕ))) → (
    let p : Fin em.rounds := (⟨em.rounds - (1 : ℕ),
    have this : (1 : ℕ) ≤ em.rounds := em.roundsPositive; Decidable.byContradiction fun (a :
        ¬em.rounds - (1 : ℕ) < em.rounds) ↦
    by
              omega
    ⟩ : Fin em.rounds); ColoredVertexSetElementary G (em.series.data.coloring p.castSucc)
        (TreeSequenceVertexSet Tn)) → em.series.data.kind n = some TashkinovExtensionKind.PE →
    ∃ gamma ∈ TreeMissingColors mu A, gamma ∉ R ∧ gamma ≠ alpha ∧ gamma ∈ TreeMissingColors mu Tn
        ∧ TreeColorSetClosed G mu A ({ gamma } : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu em bm Cm H q A n Tn D R hAcore
      hq0 lowerElementary hpe
  let S := (TreeMissingColors mu Tn ∩ TreeMissingColors mu bm.closure) \ R
  have hScard : 4 ≤ S.card := by
    simpa [S, R, D, n, Tn, H, q, hq0, mu, bm] using
      (Cm.good.parallelBase hpe).2
  have hSsub : S ⊆ {alpha} → S.card ≤ 1 := by
    intro hs
    exact (Finset.card_le_card hs).trans (by simp)
  have hremove : (S \ {alpha}).Nonempty := by
    apply Finset.card_pos.mp
    by_contra h
    have he : S \ {alpha} = ∅ := Finset.card_eq_zero.mp (by omega)
    apply (by omega : ¬ S.card ≤ 1)
    apply hSsub
    intro c hc
    by_contra hca
    have hc' : c ∈ S \ {alpha} := Finset.mem_sdiff.mpr ⟨hc, by simpa using hca⟩
    rw [he] at hc'
    simp at hc'
  obtain ⟨gamma, hg⟩ := hremove
  have hgS : gamma ∈ S := (Finset.mem_sdiff.mp hg).1
  have hgAlpha : gamma ≠ alpha := by
    intro he
    exact (Finset.mem_sdiff.mp hg).2 (by simp [he])
  have hgparts := Finset.mem_sdiff.mp hgS
  have hgint := Finset.mem_inter.mp hgparts.1
  have hgA : gamma ∈ TreeMissingColors mu A := by
    obtain ⟨u⟩ := (bm.parallel hpe).2.2
    have hTnA : TreeSequenceInitialSegment Tn A := by
      rw [hAcore]
      exact u.leftSegment
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hgint.1
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hmv⟩
  have hclosedCore := ParallelCommonMissingClosed G k e0
    P.corresponding.replacementInput T mu mu em (by
      have := em.roundsPositive
      omega) bm em.generatingColoring hpe lowerElementary
  have hgClosed : TreeColorSetClosed G mu A {gamma} := by
    rw [hAcore]
    intro c hc
    have hcgamma : c = gamma := Finset.mem_singleton.mp hc
    subst c
    exact hclosedCore gamma hgparts.1
  exact ⟨gamma, hgA, hgparts.2, hgAlpha, hgint.1, hgClosed⟩

private theorem helper_branch_4070.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (P :
        HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
    let mu : PartialEdgeColoring E k := P.coloring;
    let em : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
        P.corresponding.replacementETT;
    let bm : HierarchyBase P.corresponding.replacementETT P.coloring := P.replacementBase;
    let Cm : HierarchyCounterexample P.replacementBase := P.counterexample;
    let _ : HierarchyMinimumCounterexampleContext G k e0 P.corresponding.replacementInput T
        P.coloring P.corresponding.replacementETT P.replacementBase P.counterexample :=
        P.minimumContext;
    let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := Cm.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (em.rounds + (1 : ℕ)) := Fin.last em.rounds;
    let Tn : TreeSequence G e0 := em.series.data.tree n.castSucc;
    let D : Finset (Fin k) := HierarchyStoredColorsAt H q;
    let R : Finset (Fin k) := D.biUnion (Cm.good.gamma q); R.card ≤ (2 : ℕ) * em.rounds → A =
        bm.core → ¬em.series.data.kind n = some TashkinovExtensionKind.PE →
    ∃ gamma ∈ TreeMissingColors mu A, gamma ∉ R ∧ gamma ≠ alpha ∧ gamma ∈ TreeMissingColors mu Tn
        ∧ TreeColorSetClosed G mu A ({ gamma } : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu em bm Cm cm H q A n Tn D R
      hRcard hAcore hpe
  have hAeq : A = Tn := by
    rw [hAcore]
    exact bm.nonparallel hpe
  let S := TreeMissingColors mu Tn \ (R ∪ {alpha})
  have hlarge : 2 * em.rounds + 11 ≤ (TreeMissingColors mu Tn).card := by
    simpa [Tn, n] using cm.largeMissingSet
  have hSne : S.Nonempty := by
    exact @helper_hSne_377 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
        (@hRcard) (@hlarge)
  obtain ⟨gamma, hg⟩ := hSne
  have hgTn := (Finset.mem_sdiff.mp hg).1
  have hgnot := (Finset.mem_sdiff.mp hg).2
  have hgR : gamma ∉ R := by
    intro hc
    exact hgnot (Finset.mem_union_left _ hc)
  have hgAlpha : gamma ≠ alpha := by
    intro he
    exact hgnot (Finset.mem_union_right _ (by simp [he]))
  have closedSingleton (U : TreeSequence G e0)
      (hc : ColoredVertexSetClosed G mu (TreeSequenceVertexSet U))
      (hm : gamma ∈ TreeMissingColors mu U) :
      TreeColorSetClosed G mu U {gamma} := by
    exact @helper_closedSingleton_400 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@gamma) (@U) (@hc) (@hm)
  have stableClosed (U : TreeSequence G e0) (S : Finset (Fin k))
      (psi pi : PartialEdgeColoring E k)
      (hpsi : IsProperEdgeColoring G psi) (hpsiOne : IsOneEdgeUncolored psi e0)
      (hpi : IsProperEdgeColoring G pi) (hpiOne : IsOneEdgeUncolored pi e0)
      (hs : StableColoring U S psi pi)
      (hc : ColoredVertexSetClosed G psi (TreeSequenceVertexSet U)) :
      ColoredVertexSetClosed G pi (TreeSequenceVertexSet U) := by
    exact StableColoring.closed U S psi pi hpsi hpsiOne hpi hpiOne hc hs
  let p : Fin em.rounds := ⟨em.rounds - 1, by have := em.roundsPositive; omega⟩
  have hp : p.succ = n := by
    apply Fin.ext
    change p.val + 1 = em.rounds
    dsimp [p]
    exact Nat.sub_add_cancel em.roundsPositive
  have hphi : mu = em.series.data.coloring p.succ := by
    rw [hp]
    exact em.generatingColoring
  have hTn : Tn = em.series.data.tree p.succ.castSucc := by rw [hp]
  have hclosedTn : TreeColorSetClosed G mu Tn {gamma} := by
    generalize heq : p.succ = target
    cases em.series.certified target with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero p heq).elim
    | PE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        delta gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
            strictExtension =>
      have hci : ci = p := Fin.ext (by
        have hv := congrArg Fin.val heq
        simp at hv ⊢
        omega)
      subst ci
      have hfinalPE : em.series.data.kind n = some TashkinovExtensionKind.PE := by
        rw [← hp, currentKind]
      exact (hpe hfinalPE).elim
    | RE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
      have hci : ci = p := Fin.ext (by
        have hv := congrArg Fin.val heq
        simp at hv ⊢
        omega)
      subst ci
      have hclosedPrev : ColoredVertexSetClosed G mu
          (TreeSequenceVertexSet (em.series.data.tree p.succ.castSucc)) := by
        rw [hphi, currentColoring]
        exact previousClosed
      rw [hTn]
      exact closedSingleton _ hclosedPrev (by simpa [hphi, currentColoring, hTn] using hgTn)
    | SE ci previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative currentColoring
        currentStored currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
            strictExtension =>
      have hci : ci = p := Fin.ext (by
        have hv := congrArg Fin.val heq
        simp at hv ⊢
        omega)
      subst ci
      have hstableClosed : ColoredVertexSetClosed G choice.selected
          (TreeSequenceVertexSet (em.series.data.tree p.succ.castSucc)) :=
        stableClosed (em.series.data.tree p.succ.castSucc)
        (TashkinovStoredColors em.series.data p.castSucc)
        (em.series.data.coloring p.castSucc) choice.selected
        previousProper previousOneUncolored choice.selectedProper
        choice.selectedOneUncolored choice.selectedStable previousClosed
      have hclosedNow : ColoredVertexSetClosed G mu
          (TreeSequenceVertexSet (em.series.data.tree p.succ.castSucc)) := by
        rw [hphi, currentColoring]
        exact hstableClosed
      rw [hTn]
      exact closedSingleton _ hclosedNow (by simpa [hphi, currentColoring, hTn] using hgTn)
  have hclosed : TreeColorSetClosed G mu A {gamma} := by
    rw [hAeq]
    exact hclosedTn
  have hgA : gamma ∈ TreeMissingColors mu A := by rw [hAeq]; exact hgTn
  exact ⟨gamma, hgA, hgR, hgAlpha, hgTn, hclosed⟩

theorem HierarchyClaimNineFirstUseSeed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (hvertexMissing : ∀ (mu : PartialEdgeColoring E k),
      IsProperEdgeColoring G mu → IsOneEdgeUncolored mu e0 →
        ∀ v : V, (MissingColors G mu v).Nonempty)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (hsituation : HierarchyPathNumber P.counterexample.hierarchy = 1)
    (alpha : Fin k)
    (hstart :
      alpha ∈
        TreeMissingColors P.coloring
          (HierarchyStarredStage P.counterexample.hierarchy
            (Fin.last (P.counterexample.hierarchy).dividerCount)) ∧
      alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)))
    (hnormalized :
      (0 < (P.counterexample.hierarchy).dividerCount ∧
        alpha ∈
          TreeMissingColors P.coloring
            ((P.counterexample.hierarchy).stage
              ⟨(P.counterexample.hierarchy).dividerCount, by omega⟩)) ∨
      ((P.counterexample.hierarchy).dividerCount = 0 ∧
        alpha ∈
          TreeMissingColors P.coloring
            (P.corresponding.replacementETT.series.data.tree
              ((Fin.last P.corresponding.replacementETT.rounds :
                  Fin (P.corresponding.replacementETT.rounds + 1))).castSucc)))
    (_ : ∀ i ∈ Finset.Icc 1 (HierarchyFullTailLength C - 1),
      Disjoint
        (MissingColors G P.coloring
          ((HierarchyFullTailPrefix C i).vertex
            (Fin.last (HierarchyFullTailPrefix C i).length)))
        (MissingColors G P.coloring (T.vertex (Fin.last T.length))))
    (e1 : Fin T.length)
    (he1 :
      e1.val =
      (HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)).length)
    (hfirst : P.coloring (T.edge e1) = some alpha) :
    (HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx).Nonempty := by
  classical
  let mu := P.coloring
  let em := P.corresponding.replacementETT
  let bm := P.replacementBase
  let Cm := P.counterexample
  let cm := P.minimumContext
  let H := Cm.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength Cm
  let B := HierarchyFullTailPrefix Cm (ell - 1)
  let y := T.vertex (Fin.last T.length)
  have hstar := (P2752_T2_HierarchyMeasures C.hierarchy H P.sameGood.1).1
  have hell : HierarchyFullTailLength C = ell := by
    simp only [HierarchyFullTailLength, hstar]
    rfl
  have hprefix (i : ℕ) : HierarchyFullTailPrefix C i =
      HierarchyFullTailPrefix Cm i := by
    simp only [HierarchyFullTailPrefix, hstar]
    rfl
  have htwo : 2 ≤ ell :=
    HierarchyCounterexampleTailAtLeastTwo G k e0
      P.corresponding.replacementInput T mu em bm Cm cm.proper cm.oneEdgeUncolored
      cm.lowerRung cm.fewerDividers cm.lexicographicMinimality cm.largeMissingSet
  have helem : ColoredVertexSetElementary G mu (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0
      P.corresponding.replacementInput T mu em bm Cm cm.proper cm.oneEdgeUncolored
      cm.lowerRung cm.fewerDividers cm.lexicographicMinimality cm.largeMissingSet
  have hAT := H.lastStarredInitialSegment
  have hsum : A.length + ell = T.length := Nat.add_sub_of_le hAT.1
  have hBlen : B.length = T.length - 1 := by
    dsimp [B, HierarchyFullTailPrefix]
    change min (A.length + (ell - 1)) T.length = T.length - 1
    omega
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hAB : TreeSequenceInitialSegment A B := by
    exact @helper_hAB_259 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation) (@e1)
        (@htwo) (@hAT) (@hsum) (@hBlen) (@hBT)
  have haA : alpha ∈ TreeMissingColors mu A := hstart.1
  have haY : alpha ∈ MissingColors G mu y := hstart.2
  have hmissingB : alpha ∈ TreeMissingColors mu B := by
    obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp haA
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hmv⟩
  let n : Fin (em.rounds + 1) := Fin.last em.rounds
  let Tn := em.series.data.tree n.castSucc
  let D := HierarchyStoredColorsAt H q
  let R := D.biUnion (Cm.good.gamma q)
  have hDcard : D.card ≤ em.rounds := by
    change (HierarchyStoredColorsAt H q).card ≤ em.rounds
    exact HierarchyStoredColorsCardinality H q
  have hRcard : R.card ≤ 2 * em.rounds := by
    exact @helper_hRcard_279 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hsituation) (@hDcard)
  have hAcore (hz : H.dividerCount = 0) : A = bm.core := by
    have hq : q = 0 := Fin.ext (by simp [q, hz])
    simp [A, H, q, bm, HierarchyStarredStage, hq]
  have hgammaZero (hz : H.dividerCount = 0) : ∃ gamma : Fin k,
      gamma ∈ TreeMissingColors mu A ∧ gamma ∉ R ∧ gamma ≠ alpha ∧
        gamma ∈ TreeMissingColors mu Tn ∧ TreeColorSetClosed G mu A {gamma} := by as_aux_lemma =>
    clear * - P mu em bm Cm cm H q A Tn R hRcard hAcore hz alpha
    have hAcore : A = bm.core := by simpa [bm] using hAcore hz
    have hq0 : q = 0 := Fin.ext (by simp [q, hz])
    have lowerElementary :
        let p : Fin em.rounds := ⟨em.rounds - 1, by have := em.roundsPositive; omega⟩
        ColoredVertexSetElementary G (em.series.data.coloring p.castSucc)
          (TreeSequenceVertexSet Tn) := by
      dsimp only
      dsimp only [Tn]
      by_cases hr : em.rounds = 1
      · have hp : (⟨em.rounds - 1, by have := em.roundsPositive; omega⟩ : Fin em.rounds).castSucc
          = 0 := by
          apply Fin.ext
          simp [hr]
        have htree : n.castSucc = (⟨1, by omega⟩ : Fin (em.rounds + 2)) := by
          apply Fin.ext
          simp [n, hr]
        rw [hp, htree]
        exact (TechnicalTheoremBase G k em.rounds e0
          P.corresponding.replacementInput em.series).1
      · have hmore : 1 < em.rounds := by
          have := em.roundsPositive
          omega
        obtain ⟨pred, hround, hmax, _, _⟩ := CertifiedETTPredecessor G k e0
          P.corresponding.replacementInput T mu em (Cm.maximum) hmore
        have htree : n.castSucc = (⟨em.rounds, by omega⟩ : Fin (em.rounds + 2)) := by
          apply Fin.ext
          rfl
        rw [htree]
        have hpredPositive : 0 < pred.rounds := by rw [hround]; omega
        have hpredLower : pred.rounds < em.rounds := by rw [hround]; omega
        exact (cm.lowerRung pred hpredPositive hpredLower hmax).1
    by_cases hpe : em.series.data.kind n = some TashkinovExtensionKind.PE
    · exact @helper_branch_4026 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hAcore)
        (@hq0) (@lowerElementary) (@hpe)
    · exact @helper_branch_4070 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@hRcard)
        (@hAcore) (@hpe)
  exact @helper_continuation_2508 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
      (@hvertexMissing) (@P) (@hsituation) (@alpha) (@hnormalized) (by assumption) (@e1) (@he1)
      (@hfirst) (@hell) (@htwo) (@helem) (@hAT) (@hsum) (@hBlen) (@hBT) (@hAB) (@haA) (@haY)
      (@hmissingB) (@hAcore) (@hgammaZero)
end GoldbergSeymour

end
