/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseTwoTwoData
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation

/-!
# Shared facts for HierarchySituationTwoSubcaseTwoTwo

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.SecondSubcaseTransport

/-- Shared dependent data used by more than one proof branch. -/
abbrev hsameTwo964Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ));
  (∀ {c : Fin k},
    c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) → c ∉ TreeMissingColors phi A) →
  let Bshort : TreeSequence G e0 :=
   HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ));
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage P.counterexample.hierarchy
      (Fin.last P.counterexample.hierarchy.dividerCount) =
     A) →
  (∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStoredColorsAt H q =
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount) ∧
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      C.good.gamma q eta =
       P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta) →
  ∀ beta ∈ TreeMissingColors phi Bshort,
   (∀ (t : Fin T.length), A.length ≤ (↑t : ℕ) → phi (T.edge t) ≠ some beta) →
    beta ∉ HierarchyStoredColorsAt H q →
     (H.dividerCount = (0 : ℕ) →
       beta ∈ TreeMissingColors phi A →
        beta ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
      (beta ∉ TreeMissingColors phi A → D.theta ∉ HierarchyStoredColorsAt H q) →
       (∀ eta ∈ HierarchyStoredColorsAt H q,
         beta ∈ C.good.gamma q eta → eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) →
        beta ≠ D.alpha →
         beta ≠ D.theta →
          let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
          beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
            (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Bshort.length →
           T.vertex ib ∈ TreeSequenceVertexSet B →
            T.vertex ib ≠ T.vertex D.penultimateVertexIndex →
             T.vertex ib ≠ T.vertex D.terminalVertexIndex →
              TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) →
               (beta ∉ TreeMissingColors phi A →
                 beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) →
                beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B →
                 (let H : TashkinovHierarchy ett base := C.hierarchy;
                  have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
                  have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
                  have A : TreeSequence G e0 := HierarchyStarredStage H q;
                  have Tnq : TreeSequence G e0 :=
                   H.stage
                    (⟨H.dividerCount,
                      by
                      have := GoldbergSeymour.TreeSequence.positive T
                      omega⟩ :
                     Fin (H.dividerCount + (2 : ℕ)));
                  have Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
                  have Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
                  have Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
                  have va : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
                  have vb : V := T.vertex (HierarchyFirstMissingPosition phi T D.alpha);
                  have sameComponent : Prop :=
                   TwoColorComponent G phi beta D.alpha (Sum.inl va) =
                    TwoColorComponent G phi beta D.alpha (Sum.inl vb);
                  ((0 : ℕ) < H.dividerCount ∧
                     (beta ∈ TreeMissingColors phi Tnq ∨
                      Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
                       Dnq) →
                    sameComponent) ∧
                   (H.dividerCount = (0 : ℕ) ∧
                      (beta ∈ TreeMissingColors phi Tn ∨
                       Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
                        Dn) →
                     sameComponent) ∧
                    (beta ∈ TreeMissingColors phi A ∧
                      TreeColorSetClosed G phi A ({ beta } : Finset (Fin k)) →
                     sameComponent ∧ TreeInterchangeable G A phi beta D.alpha)) →
                  TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
                    TwoColorComponent G phi beta D.alpha
                     (Sum.inl (T.vertex D.penultimateVertexIndex)) →
                   let z : V ⊕ E := Sum.inl (T.vertex D.terminalVertexIndex);
                   let muOne : PartialEdgeColoring E k :=
                    TwoColorComponentSwap G phi beta D.alpha z;
                   Disjoint
                     (TwoColorComponent G phi beta D.alpha
                      (Sum.inl (T.vertex D.terminalVertexIndex)))
                     (TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib))) →
                    TwoColorPathComponent G phi beta D.alpha z →
                     Sum.inl (T.vertex ib) ∉ TwoColorComponent G phi beta D.alpha z →
                      Sum.inl (T.vertex D.penultimateVertexIndex) ∉
                        TwoColorComponent G phi beta D.alpha z →
                       (∀ w ∈ TreeSequenceVertexSet B,
                         MissingColors G (TwoColorComponentSwap G phi beta D.alpha z) w =
                          MissingColors G phi w) →
                        (∀ (t : Fin T.length),
                          A.length ≤ (↑t : ℕ) → muOne (T.edge t) = phi (T.edge t)) →
                         (∀ c ∈ HierarchyStoredColorsAt H q,
                           HierarchyFirstMissingPosition muOne T c =
                            HierarchyFirstMissingPosition phi T c) →
                          (beta ∈ TreeMissingColors phi A →
                            (0 : ℕ) < H.dividerCount ∧
                              beta ∈
                               TreeMissingColors phi
                                (H.stage
                                 (⟨H.dividerCount,
                                   by
                                   have := GoldbergSeymour.TreeSequence.positive T
                                   omega⟩ :
                                  Fin (H.dividerCount + (2 : ℕ)))) ∨
                             H.dividerCount = (0 : ℕ) ∧
                              beta ∈
                               TreeMissingColors phi
                                (ett.series.data.tree (Fin.last ett.rounds).castSucc)) →
                           ∀ (corrOne : CorrespondingExtendedTashkinovTree G k e0 ett muOne T),
                            MaximumProperty corrOne.replacementETT →
                             ∀ (baseOne : HierarchyBase corrOne.replacementETT muOne)
                              (KOne : TashkinovHierarchy corrOne.replacementETT baseOne)
                              (goodOne : GoodHierarchy KOne),
                              SameGoodHierarchy C.good goodOne →
                               beta ∈ MissingColors G muOne (T.vertex D.terminalVertexIndex) →
                                ∀
                                 (POne :
                                  HierarchyReplacementPresentation G k e0 input T phi ett base C
                                   ctx),
                                 POne.coloring = muOne →
                                  let rho : PartialEdgeColoring E k := POne.coloring;
                                  let ettOne :
                                   ExtendedTashkinovTree G k e0
                                    POne.corresponding.replacementInput T POne.coloring :=
                                   POne.corresponding.replacementETT;
                                  let baseOne' :
                                   HierarchyBase POne.corresponding.replacementETT
                                    POne.coloring :=
                                   POne.replacementBase;
                                  let COne' : HierarchyCounterexample POne.replacementBase :=
                                   POne.counterexample;
                                  let HOne :
                                   TashkinovHierarchy POne.corresponding.replacementETT
                                    POne.replacementBase :=
                                   COne'.hierarchy;
                                  let qOne : Fin (HOne.dividerCount + (1 : ℕ)) :=
                                   Fin.last HOne.dividerCount;
                                  TreeMissingColors rho A = TreeMissingColors phi A →
                                   beta ∉ HierarchyStoredColorsAt HOne qOne →
                                    beta ∉
                                      MissingColors G rho (T.vertex D.penultimateVertexIndex) →
                                     beta ∈
                                       MissingColors G rho (T.vertex D.terminalVertexIndex) →
                                      beta ∈ MissingColors G rho (T.vertex ib) →
                                       HierarchyFirstMissingPosition rho T beta = ib →
                                        HierarchyFirstMissingPosition rho T D.theta =
                                          D.penultimateVertexIndex →
                                         (∀ (t : Fin T.length),
                                           A.length ≤ (↑t : ℕ) → rho (T.edge t) ≠ some beta) →
                                          (beta ∈ TreeMissingColors phi A →
                                            (0 : ℕ) < HOne.dividerCount ∧
                                              beta ∈
                                               TreeMissingColors rho
                                                (HOne.stage
                                                 (⟨HOne.dividerCount,
                                                   by
                                                   have :=
                                                    GoldbergSeymour.TreeSequence.positive T
                                                   omega⟩ :
                                                  Fin (HOne.dividerCount + (2 : ℕ)))) ∨
                                             HOne.dividerCount = (0 : ℕ) ∧
                                              beta ∈
                                               TreeMissingColors rho
                                                (ettOne.series.data.tree
                                                 (Fin.last ettOne.rounds).castSucc)) →
                                           beta ∈ TreeMissingColors rho B ∧
                                             D.theta ∈ TreeMissingColors rho B →
                                            (let H : TashkinovHierarchy ettOne baseOne' :=
                                              COne'.hierarchy;
                                             have q : Fin (H.dividerCount + (1 : ℕ)) :=
                                              Fin.last H.dividerCount;
                                             have n : Fin (ettOne.rounds + (1 : ℕ)) :=
                                              Fin.last ettOne.rounds;
                                             have A : TreeSequence G e0 :=
                                              HierarchyStarredStage H q;
                                             have Tnq : TreeSequence G e0 :=
                                              H.stage
                                               (⟨H.dividerCount,
                                                 by
                                                 have := GoldbergSeymour.TreeSequence.positive T
                                                 omega⟩ :
                                                Fin (H.dividerCount + (2 : ℕ)));
                                             have Tn : TreeSequence G e0 :=
                                              ettOne.series.data.tree n.castSucc;
                                             have Dn : Finset (Fin k) :=
                                              TashkinovStoredColors ettOne.series.data n;
                                             have Dnq : Finset (Fin k) :=
                                              HierarchyStoredColorsAt H q;
                                             have va : V :=
                                              T.vertex
                                               (HierarchyFirstMissingPosition rho T beta);
                                             have vb : V :=
                                              T.vertex
                                               (HierarchyFirstMissingPosition rho T D.theta);
                                             have sameComponent : Prop :=
                                              TwoColorComponent G rho beta D.theta
                                                (Sum.inl va) =
                                               TwoColorComponent G rho beta D.theta
                                                (Sum.inl vb);
                                             ((0 : ℕ) < H.dividerCount ∧
                                                (beta ∈ TreeMissingColors rho Tnq ∨
                                                 Disjoint
                                                  (insert beta ({ D.theta } : Finset (Fin k)) :
                                                   Finset (Fin k))
                                                  Dnq) →
                                               sameComponent) ∧
                                              (H.dividerCount = (0 : ℕ) ∧
                                                 (beta ∈ TreeMissingColors rho Tn ∨
                                                  Disjoint
                                                   (insert beta ({ D.theta } : Finset (Fin k)) :
                                                    Finset (Fin k))
                                                   Dn) →
                                                sameComponent) ∧
                                               (beta ∈ TreeMissingColors rho A ∧
                                                 TreeColorSetClosed G rho A
                                                  ({ beta } : Finset (Fin k)) →
                                                sameComponent ∧
                                                 TreeInterchangeable G A rho beta D.theta)) →
                                             TwoColorComponent G rho beta D.theta
                                               (Sum.inl (T.vertex ib)) =
                                              TwoColorComponent G rho beta D.theta
                                               (Sum.inl (T.vertex D.penultimateVertexIndex))

end GoldbergSeymour.SharedFacts.SecondSubcaseTransport

end
