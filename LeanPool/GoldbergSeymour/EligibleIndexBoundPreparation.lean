/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.ShorteningProofs

public import LeanPool.GoldbergSeymour.SharedFacts.SubcaseThreeOnePreparation1


public import LeanPool.GoldbergSeymour.TerminalRoute
public import LeanPool.GoldbergSeymour.HierarchyEligibleCommonMissingIndices
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport

/-!
# Hierarchy Situation Three Eligible Index Bound

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

namespace EligibleIndexBound

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch1346Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (∀ (psi : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G psi →
      ∀ (B : Finset V),
       ColoredVertexSetElementary G psi B →
        ∀ (u v w : V),
         u ∈ B →
          v ∈ B →
           u ≠ v →
            w ≠ u →
             w ≠ v →
              a ∈ MissingColors G psi u →
               b ∈ MissingColors G psi v →
                a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
                 TwoColorComponent G psi a b (Sum.inl u) =
                   TwoColorComponent G psi a b (Sum.inl v) →
                  Disjoint (TwoColorComponent G psi a b (Sum.inl w))
                    (TwoColorComponent G psi a b (Sum.inl u)) ∧
                   TwoColorPathComponent G psi a b (Sum.inl w) ∧
                    ∀ x ∈ B,
                     MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
                      MissingColors G psi x) →
  (∀ {X Y Z : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  let A : TreeSequence G e0 :=
   HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount) =
     A) →
  TreeSequenceInitialSegment A T →
  ∀ (hlen : (4 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
    (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  TreeSequenceInitialSegment B T →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix R.counterexample
      (HierarchyFullTailLength R.counterexample - (1 : ℕ)) =
     B) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) →
  (∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))),
    U.vertex j ∈ TreeSequenceVertexSet U) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k)
    (j : Fin (B.length + (1 : ℕ))),
    c ∈ MissingColors G R.coloring (B.vertex j) →
     (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (X : TreeSequence G e0),
    TreeSequenceInitialSegment A X →
     A.length < X.length →
      TreeSequenceInitialSegment X B →
       ∀ (a b eta : Fin k),
        eta ∈
          HierarchyStoredColorsAt R.counterexample.hierarchy
           (Fin.last R.counterexample.hierarchy.dividerCount) →
         a ∈
           R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount)
            eta →
          (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length →
           ∀ (jb : Fin (B.length + (1 : ℕ))),
            A.length < (↑jb : ℕ) →
             (↑jb : ℕ) ≤ X.length →
              b ∈ MissingColors G R.coloring (B.vertex jb) →
               a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨
                 b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                (∀ (t : Fin T.length),
                  A.length ≤ (↑t : ℕ) →
                   (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some a) →
                 (∀ (t : Fin T.length),
                   A.length ≤ (↑t : ℕ) →
                    (↑t : ℕ) < X.length →
                     R.coloring (T.edge t) = some b →
                      TreeIncidentEdge
                        (R.corresponding.replacementETT.series.data.tree
                         (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                        (T.edge t) ∧
                       b ∈
                        TashkinovStoredColors R.corresponding.replacementETT.series.data
                         (Fin.last R.corresponding.replacementETT.rounds)) →
                  ∃ (S :
                   HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                   (∀ v ∈ TreeSequenceVertexSet B,
                     MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
                    (∀ (t : Fin T.length),
                      A.length ≤ (↑t : ℕ) →
                       (↑t : ℕ) < X.length →
                        S.coloring (T.edge t) = R.coloring (T.edge t)) ∧
                     (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                       b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧
                      (b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                       a ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length)))) →
  (∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀
     eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount),
     eta ∈
       HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount)
        eta =
       S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount)
        eta) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (c : Fin k) (j : Fin (B.length + (1 : ℕ))),
    A.length < (↑j : ℕ) →
     c ∈ MissingColors G R.coloring (B.vertex j) →
      c ∉ TreeMissingColors R.coloring A) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∉ TreeMissingColors R.coloring A,
     c ∉
       HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) →
      c ∉
       TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds)) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀
     eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount),
     ∀ (f : E),
      ∃
       a ∈
        R.counterexample.good.gamma
         (Fin.last R.counterexample.hierarchy.dividerCount) eta,
       R.coloring f ≠ some a) →
  ∀ (m : ℕ)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  ∀
   alpha ∈
    MissingColors G P.coloring
     ((HierarchyFullTailPrefix C m).vertex
      (Fin.last (HierarchyFullTailPrefix C m).length)),
   alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) →
    ∀ (hm : (2 : ℕ) ≤ m) (hmT : A.length + (m + (1 : ℕ)) < T.length),
     let X : TreeSequence G e0 :=
      TreeSequencePrefix T (A.length + (m + (1 : ℕ)))
       (have this : (1 : ℕ) ≤ A.length := A.positive;
       Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ A.length + (m + (1 : ℕ))) ↦ by
        omega)
       (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) ↦
        by omega);
     TreeSequenceInitialSegment A X →
      TreeSequenceInitialSegment X B →
       A.length < X.length →
        let jm : Fin (B.length + (1 : ℕ)) :=
         (⟨A.length + m,
           id
            (Decidable.byContradiction
             fun (a : ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) ↦ by omega)⟩ :
          Fin (B.length + (1 : ℕ)));
        let jnext : Fin (B.length + (1 : ℕ)) :=
         (⟨A.length + (m + (1 : ℕ)),
           id
            (Decidable.byContradiction
             fun (a : ¬A.length + (m + (1 : ℕ)) < T.length - (1 : ℕ) + (1 : ℕ)) ↦
             by omega)⟩ :
          Fin (B.length + (1 : ℕ)));
        let tnext : Fin T.length :=
         (⟨A.length + m,
           Decidable.byContradiction fun (a : ¬A.length + m < T.length) ↦ by
            omega⟩ :
          Fin T.length);
        alpha ∈ MissingColors G P.coloring (B.vertex jm) →
         ∀ theta ∈ MissingColors G P.coloring (B.vertex jnext),
          (∀
            (S :
             HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
            ∀ c ∈ MissingColors G S.coloring (B.vertex jnext),
             c ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length)) →
              m + (1 : ℕ) ∈
               HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C
                ctx) →
           (∀
             (R :
              HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
             ∀ b ∈ MissingColors G R.coloring (B.vertex jnext),
              ∀ (t : Fin T.length),
               A.length ≤ (↑t : ℕ) →
                (↑t : ℕ) < X.length →
                 R.coloring (T.edge t) = some b →
                  TreeIncidentEdge
                    (R.corresponding.replacementETT.series.data.tree
                     (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                    (T.edge t) ∧
                   b ∈
                    TashkinovStoredColors
                     R.corresponding.replacementETT.series.data
                     (Fin.last R.corresponding.replacementETT.rounds)) →
            (∀
              (R :
               HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
              ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
               ∀ (t : Fin T.length),
                A.length ≤ (↑t : ℕ) →
                 (↑t : ℕ) < X.length →
                  R.coloring (T.edge t) = some b →
                   TreeIncidentEdge
                     (R.corresponding.replacementETT.series.data.tree
                      (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                     (T.edge t) ∧
                    b ∈
                     TashkinovStoredColors
                      R.corresponding.replacementETT.series.data
                      (Fin.last R.corresponding.replacementETT.rounds)) →
             (∀
               (R :
                HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
               (eta a : Fin k),
               eta ∈
                 HierarchyStoredColorsAt R.counterexample.hierarchy
                  (Fin.last R.counterexample.hierarchy.dividerCount) →
                a ∈
                  R.counterexample.good.gamma
                   (Fin.last R.counterexample.hierarchy.dividerCount) eta →
                 eta ∈ MissingColors G R.coloring (B.vertex jnext) →
                  ∀ (t : Fin T.length),
                   A.length ≤ (↑t : ℕ) →
                    (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some a) →
              alpha ∉
                HierarchyStoredColorsAt P.counterexample.hierarchy
                 (Fin.last P.counterexample.hierarchy.dividerCount) →
               m + (1 : ℕ) ∈
                HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C
                 ctx

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperAdvance1257Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy →
  HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C →
  (∀ (mu : PartialEdgeColoring E k),
    IsProperEdgeColoring G mu →
     IsOneEdgeUncolored mu e0 → ∀ (v : V), (MissingColors G mu v).Nonempty) →
  (∀ (psi : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G psi →
      ∀ (B : Finset V),
       ColoredVertexSetElementary G psi B →
        ∀ (u v w : V),
         u ∈ B →
          v ∈ B →
           u ≠ v →
            w ≠ u →
             w ≠ v →
              a ∈ MissingColors G psi u →
               b ∈ MissingColors G psi v →
                a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
                 TwoColorComponent G psi a b (Sum.inl u) =
                   TwoColorComponent G psi a b (Sum.inl v) →
                  Disjoint (TwoColorComponent G psi a b (Sum.inl w))
                    (TwoColorComponent G psi a b (Sum.inl u)) ∧
                   TwoColorPathComponent G psi a b (Sum.inl w) ∧
                    ∀ x ∈ B,
                     MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
                      MissingColors G psi x) →
  (∀ {X Y Z : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  (∀ {X Y Z : TreeSequence G e0},
    TreeSequenceInitialSegment X Z →
     TreeSequenceInitialSegment Y Z → X.length ≤ Y.length → TreeSequenceInitialSegment X Y) →
  let A : TreeSequence G e0 :=
   HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount) =
     A) →
  TreeSequenceInitialSegment A T →
  ∀ (hlen : (4 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
    (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  TreeSequenceInitialSegment B T →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix R.counterexample
      (HierarchyFullTailLength R.counterexample - (1 : ℕ)) =
     B) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) →
  (∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))),
    U.vertex j ∈ TreeSequenceVertexSet U) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (c : Fin k) (j : Fin (B.length + (1 : ℕ))),
    c ∈ MissingColors G R.coloring (B.vertex j) →
     (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (X : TreeSequence G e0),
    TreeSequenceInitialSegment A X →
     A.length < X.length →
      TreeSequenceInitialSegment X B →
       ∀ (a b eta : Fin k),
        eta ∈
          HierarchyStoredColorsAt R.counterexample.hierarchy
           (Fin.last R.counterexample.hierarchy.dividerCount) →
         a ∈
           R.counterexample.good.gamma
            (Fin.last R.counterexample.hierarchy.dividerCount) eta →
          (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length →
           ∀ (jb : Fin (B.length + (1 : ℕ))),
            A.length < (↑jb : ℕ) →
             (↑jb : ℕ) ≤ X.length →
              b ∈ MissingColors G R.coloring (B.vertex jb) →
               a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨
                 b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                (∀ (t : Fin T.length),
                  A.length ≤ (↑t : ℕ) →
                   (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some a) →
                 (∀ (t : Fin T.length),
                   A.length ≤ (↑t : ℕ) →
                    (↑t : ℕ) < X.length →
                     R.coloring (T.edge t) = some b →
                      TreeIncidentEdge
                        (R.corresponding.replacementETT.series.data.tree
                         (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                        (T.edge t) ∧
                       b ∈
                        TashkinovStoredColors
                         R.corresponding.replacementETT.series.data
                         (Fin.last R.corresponding.replacementETT.rounds)) →
                  ∃ (S :
                   HierarchyReplacementPresentation G k e0 input T phi ett base C
                    ctx),
                   (∀ v ∈ TreeSequenceVertexSet B,
                     MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
                    (∀ (t : Fin T.length),
                      A.length ≤ (↑t : ℕ) →
                       (↑t : ℕ) < X.length →
                        S.coloring (T.edge t) = R.coloring (T.edge t)) ∧
                     (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                       b ∈
                        MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧
                      (b ∈
                        MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                       a ∈
                        MissingColors G S.coloring (T.vertex (Fin.last T.length)))) →
  (∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀
     eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount),
     eta ∈
       HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount)
        eta =
       S.counterexample.good.gamma
        (Fin.last S.counterexample.hierarchy.dividerCount) eta) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (eta a : Fin k),
    eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount) →
     a ∈
       R.counterexample.good.gamma
        (Fin.last R.counterexample.hierarchy.dividerCount) eta →
      ∀ (t : Fin T.length),
       A.length ≤ (↑t : ℕ) →
        (↑t : ℕ) < (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) →
         R.coloring (T.edge t) ≠ some a) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (c : Fin k) (j : Fin (B.length + (1 : ℕ))),
    A.length < (↑j : ℕ) →
     c ∈ MissingColors G R.coloring (B.vertex j) →
      c ∉ TreeMissingColors R.coloring A) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∉ TreeMissingColors R.coloring A,
     c ∉
       HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) →
      c ∉
       TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds)) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (j : ℕ),
    (1 : ℕ) ≤ j →
     j < T.length - A.length →
      ∀
       c ∈
        MissingColors G R.coloring
         ((HierarchyFullTailPrefix C j).vertex
          (Fin.last (HierarchyFullTailPrefix C j).length)),
       ∀ (t : Fin T.length),
        A.length ≤ (↑t : ℕ) →
         (↑t : ℕ) < A.length + j →
          R.coloring (T.edge t) = some c →
           TreeIncidentEdge
             (R.corresponding.replacementETT.series.data.tree
              (Fin.last R.corresponding.replacementETT.rounds).castSucc)
             (T.edge t) ∧
            c ∈
             TashkinovStoredColors R.corresponding.replacementETT.series.data
              (Fin.last R.corresponding.replacementETT.rounds)) →
  (∀ (t : Fin T.length),
    A.length + HierarchyPathNumber C.hierarchy ≤ (↑t : ℕ) →
     G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀
     eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount),
     ∀ (f : E),
      ∃
       a ∈
        R.counterexample.good.gamma
         (Fin.last R.counterexample.hierarchy.dividerCount) eta,
       R.coloring f ≠ some a) →
  ∀ (m : ℕ),
  HierarchyPathNumber C.hierarchy ≤ m →
  m < HierarchyFullTailLength C - (1 : ℕ) →
  ∀
   (P :
    HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  ∀
   alpha ∈
    MissingColors G P.coloring
     ((HierarchyFullTailPrefix C m).vertex
      (Fin.last (HierarchyFullTailPrefix C m).length)),
   alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) →
    m + (1 : ℕ) ∈
     HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C
      ctx

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch2404Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (by
     have := TreeSequence.positive T
     omega)
    (by
     have := TreeSequence.positive T
     omega);
  B.length = T.length - (1 : ℕ) →
  let r : Fin T.length :=
   (⟨T.length - (1 : ℕ), by
     have := TreeSequence.positive T
     omega⟩ :
    Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0) (hSBlen : S.length ≤ B.length) (beta : Fin k),
  alpha ≠ beta →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (H.dividerCount ≠ (0 : ℕ) →
    A =
     H.stage
      (⟨H.dividerCount, by
        have := TreeSequence.positive T
        omega⟩ :
       Fin (H.dividerCount + (2 : ℕ)))) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (P.corresponding.replacementETT.series.data.tree
      (⟨P.corresponding.replacementETT.rounds,
        by
        have := TreeSequence.positive T
        omega⟩ :
       Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
     B)
   (strictB :
    (P.corresponding.replacementETT.series.data.tree
       (⟨P.corresponding.replacementETT.rounds,
         by
         have := TreeSequence.positive T
         omega⟩ :
        Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (P.corresponding.replacementETT.series.data.tree
      (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
   (generatingB :
    mu =
     P.corresponding.replacementETT.series.data.coloring
      (Fin.last P.corresponding.replacementETT.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     mu)
   (HB :
    TashkinovHierarchy
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
   {
    rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
    series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
    strictAbovePenultimate := strictB, belowFinal := belowB,
    generatingColoring := generatingB :
    ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
   (bs : HierarchyBase corr.replacementETT sigma)
   (baseStageK :
    HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
     corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc)
   (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
   (nestedK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
   (strictK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     (HB.stage j.castSucc).length < (HB.stage j.succ).length)
   (coreInsideK :
    TreeSequenceInitialSegment bs.core
     (HB.stage
      (⟨(1 : ℕ), by
        have := TreeSequence.positive T
        have := TreeSequence.positive B
        omega⟩ :
       Fin (HB.dividerCount + (2 : ℕ)))))
   (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
   (increasingK :
    ∀ (i j : Fin HB.dividerCount),
     (↑i : ℕ) < (↑j : ℕ) → (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
   (dividerStageK :
    ∀ (i : Fin HB.dividerCount),
     HB.stage
       (⟨(↑i : ℕ) + (1 : ℕ), by
         have := TreeSequence.positive T
         have := TreeSequence.positive B
         omega⟩ :
        Fin (HB.dividerCount + (2 : ℕ))) =
      TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
       (by
        have := TreeSequence.positive T
        have := TreeSequence.positive B
        omega)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
   {
    dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
    terminalStage := terminalStageK, nested := nestedK, strict := strictK,
    dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
    dividerIncreasing := increasingK, dividerStage := dividerStageK,
    coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  HierarchyPathNumber KF ≤ HierarchyPathNumber H →
  HB.stage (Fin.last HB.dividerCount).castSucc =
    H.stage (Fin.last H.dividerCount).castSucc →
  (H.stage (Fin.last H.dividerCount).castSucc).length < B.length →
  ¬HierarchyPathNumber KF < HierarchyPathNumber H →
  HierarchyCounterexampleLess
   (HierarchyPathNumber KF,
    B.length -
     (HB.stage
       (⟨HB.dividerCount, by
         have := TreeSequence.positive T
         have := TreeSequence.positive B
         omega⟩ :
        Fin (HB.dividerCount + (2 : ℕ)))).length)
   (HierarchyPathNumber H,
    T.length -
     (H.stage
       (⟨H.dividerCount, by
         have := TreeSequence.positive T
         omega⟩ :
        Fin (H.dividerCount + (2 : ℕ)))).length)

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperLastOrdinary2387Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := old.hierarchy;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (by
     have := TreeSequence.positive T
     omega)
    (by
     have := TreeSequence.positive T
     omega);
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (P.corresponding.replacementETT.series.data.tree
      (⟨P.corresponding.replacementETT.rounds,
        by
        have := TreeSequence.positive T
        omega⟩ :
       Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
     B)
   (strictB :
    (P.corresponding.replacementETT.series.data.tree
       (⟨P.corresponding.replacementETT.rounds,
         by
         have := TreeSequence.positive T
         omega⟩ :
        Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (P.corresponding.replacementETT.series.data.tree
      (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
   (generatingB :
    mu =
     P.corresponding.replacementETT.series.data.coloring
      (Fin.last P.corresponding.replacementETT.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     mu)
   (HB :
    TashkinovHierarchy
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     baseB)
   (hcountB : HB.dividerCount = H.dividerCount),
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
    HB.stage j.castSucc =
      H.stage
       (Fin.cast
         (by
          have := TreeSequence.positive T
          have := TreeSequence.positive B
          omega)
         j).castSucc ∧
     HierarchyStarredStage HB j =
      HierarchyStarredStage H
       (Fin.cast
        (by
         have := TreeSequence.positive T
         have := TreeSequence.positive B
         omega)
        j)) →
  HB.stage (Fin.last HB.dividerCount).castSucc = H.stage (Fin.last H.dividerCount).castSucc

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch1318Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  let A : TreeSequence G e0 :=
   HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
  ∀ (hlen : (4 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
    (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  (∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))),
    U.vertex j ∈ TreeSequenceVertexSet U) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k)
    (j : Fin (B.length + (1 : ℕ))),
    c ∈ MissingColors G R.coloring (B.vertex j) →
     (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (X : TreeSequence G e0),
    TreeSequenceInitialSegment A X →
     A.length < X.length →
      TreeSequenceInitialSegment X B →
       ∀ (a b eta : Fin k),
        eta ∈
          HierarchyStoredColorsAt R.counterexample.hierarchy
           (Fin.last R.counterexample.hierarchy.dividerCount) →
         a ∈
           R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta →
          (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length →
           ∀ (jb : Fin (B.length + (1 : ℕ))),
            A.length < (↑jb : ℕ) →
             (↑jb : ℕ) ≤ X.length →
              b ∈ MissingColors G R.coloring (B.vertex jb) →
               a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨
                 b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                (∀ (t : Fin T.length),
                  A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some a) →
                 (∀ (t : Fin T.length),
                   A.length ≤ (↑t : ℕ) →
                    (↑t : ℕ) < X.length →
                     R.coloring (T.edge t) = some b →
                      TreeIncidentEdge
                        (R.corresponding.replacementETT.series.data.tree
                         (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                        (T.edge t) ∧
                       b ∈
                        TashkinovStoredColors R.corresponding.replacementETT.series.data
                         (Fin.last R.corresponding.replacementETT.rounds)) →
                  ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                   (∀ v ∈ TreeSequenceVertexSet B,
                     MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
                    (∀ (t : Fin T.length),
                      A.length ≤ (↑t : ℕ) →
                       (↑t : ℕ) < X.length → S.coloring (T.edge t) = R.coloring (T.edge t)) ∧
                     (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                       b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧
                      (b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                       a ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length)))) →
  (∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀
     eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount),
     eta ∈
       HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
       S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀
     eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount),
     ∀ (f : E),
      ∃
       a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
       R.coloring f ≠ some a) →
  ∀ (m : ℕ) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  ∀ alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)),
   ∀ (hm : (2 : ℕ) ≤ m) (hmT : A.length + (m + (1 : ℕ)) < T.length),
    let X : TreeSequence G e0 :=
     TreeSequencePrefix T (A.length + (m + (1 : ℕ)))
      (have this : (1 : ℕ) ≤ A.length := A.positive;
      Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ A.length + (m + (1 : ℕ))) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) ↦ by omega);
    TreeSequenceInitialSegment A X →
     TreeSequenceInitialSegment X B →
      A.length < X.length →
       let jm : Fin (B.length + (1 : ℕ)) :=
        (⟨A.length + m,
          id
           (Decidable.byContradiction
            fun (a : ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) ↦ by omega)⟩ :
         Fin (B.length + (1 : ℕ)));
       let jnext : Fin (B.length + (1 : ℕ)) :=
        (⟨A.length + (m + (1 : ℕ)),
          id
           (Decidable.byContradiction
            fun (a : ¬A.length + (m + (1 : ℕ)) < T.length - (1 : ℕ) + (1 : ℕ)) ↦ by
            omega)⟩ :
         Fin (B.length + (1 : ℕ)));
       let tnext : Fin T.length :=
        (⟨A.length + m,
          Decidable.byContradiction fun (a : ¬A.length + m < T.length) ↦ by omega⟩ :
         Fin T.length);
       alpha ∈ MissingColors G P.coloring (B.vertex jm) →
        ∀ theta ∈ MissingColors G P.coloring (B.vertex jnext),
         (∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
           ∀ c ∈ MissingColors G S.coloring (B.vertex jnext),
            c ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length)) →
             m + (1 : ℕ) ∈
              HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx) →
          (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
            ∀ b ∈ MissingColors G R.coloring (B.vertex jnext),
             ∀ (t : Fin T.length),
              A.length ≤ (↑t : ℕ) →
               (↑t : ℕ) < X.length →
                R.coloring (T.edge t) = some b →
                 TreeIncidentEdge
                   (R.corresponding.replacementETT.series.data.tree
                    (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                   (T.edge t) ∧
                  b ∈
                   TashkinovStoredColors R.corresponding.replacementETT.series.data
                    (Fin.last R.corresponding.replacementETT.rounds)) →
           (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
             ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
              ∀ (t : Fin T.length),
               A.length ≤ (↑t : ℕ) →
                (↑t : ℕ) < X.length →
                 R.coloring (T.edge t) = some b →
                  TreeIncidentEdge
                    (R.corresponding.replacementETT.series.data.tree
                     (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                    (T.edge t) ∧
                   b ∈
                    TashkinovStoredColors R.corresponding.replacementETT.series.data
                     (Fin.last R.corresponding.replacementETT.rounds)) →
            (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
              (eta a : Fin k),
              eta ∈
                HierarchyStoredColorsAt R.counterexample.hierarchy
                 (Fin.last R.counterexample.hierarchy.dividerCount) →
               a ∈
                 R.counterexample.good.gamma
                  (Fin.last R.counterexample.hierarchy.dividerCount) eta →
                eta ∈ MissingColors G R.coloring (B.vertex jm) →
                 R.coloring (T.edge tnext) ≠ some a →
                  ∀ (t : Fin T.length),
                   A.length ≤ (↑t : ℕ) →
                    (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some a) →
             alpha ∈
               HierarchyStoredColorsAt P.counterexample.hierarchy
                (Fin.last P.counterexample.hierarchy.dividerCount) →
              m + (1 : ℕ) ∈
               HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch1872Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  let A : TreeSequence G e0 :=
   HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
  ∀ (hlen : (4 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
    (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  (∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))),
    U.vertex j ∈ TreeSequenceVertexSet U) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k)
    (j : Fin (B.length + (1 : ℕ))),
    c ∈ MissingColors G R.coloring (B.vertex j) →
     (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (X : TreeSequence G e0),
    TreeSequenceInitialSegment A X →
     A.length < X.length →
      TreeSequenceInitialSegment X B →
       ∀ (a b eta : Fin k),
        eta ∈
          HierarchyStoredColorsAt R.counterexample.hierarchy
           (Fin.last R.counterexample.hierarchy.dividerCount) →
         a ∈
           R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta →
          (↑(HierarchyFirstMissingPosition R.coloring T eta) : ℕ) ≤ X.length →
           ∀ (jb : Fin (B.length + (1 : ℕ))),
            A.length < (↑jb : ℕ) →
             (↑jb : ℕ) ≤ X.length →
              b ∈ MissingColors G R.coloring (B.vertex jb) →
               a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨
                 b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                (∀ (t : Fin T.length),
                  A.length ≤ (↑t : ℕ) → (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some a) →
                 (∀ (t : Fin T.length),
                   A.length ≤ (↑t : ℕ) →
                    (↑t : ℕ) < X.length →
                     R.coloring (T.edge t) = some b →
                      TreeIncidentEdge
                        (R.corresponding.replacementETT.series.data.tree
                         (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                        (T.edge t) ∧
                       b ∈
                        TashkinovStoredColors R.corresponding.replacementETT.series.data
                         (Fin.last R.corresponding.replacementETT.rounds)) →
                  ∃ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
                   (∀ v ∈ TreeSequenceVertexSet B,
                     MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
                    (∀ (t : Fin T.length),
                      A.length ≤ (↑t : ℕ) →
                       (↑t : ℕ) < X.length → S.coloring (T.edge t) = R.coloring (T.edge t)) ∧
                     (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                       b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧
                      (b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
                       a ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length)))) →
  (∀ (R S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀
     eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount),
     eta ∈
       HierarchyStoredColorsAt S.counterexample.hierarchy
        (Fin.last S.counterexample.hierarchy.dividerCount) ∧
      R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta =
       S.counterexample.good.gamma (Fin.last S.counterexample.hierarchy.dividerCount) eta) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀
     eta ∈
      HierarchyStoredColorsAt R.counterexample.hierarchy
       (Fin.last R.counterexample.hierarchy.dividerCount),
     ∀ (f : E),
      ∃
       a ∈ R.counterexample.good.gamma (Fin.last R.counterexample.hierarchy.dividerCount) eta,
       R.coloring f ≠ some a) →
  ∀ (m : ℕ) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  ∀ alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)),
   ∀ (hm : (2 : ℕ) ≤ m) (hmT : A.length + (m + (1 : ℕ)) < T.length),
    let X : TreeSequence G e0 :=
     TreeSequencePrefix T (A.length + (m + (1 : ℕ)))
      (have this : (1 : ℕ) ≤ A.length := A.positive;
      Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ A.length + (m + (1 : ℕ))) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) ↦ by omega);
    TreeSequenceInitialSegment A X →
     TreeSequenceInitialSegment X B →
      A.length < X.length →
       let jm : Fin (B.length + (1 : ℕ)) :=
        (⟨A.length + m,
          id
           (Decidable.byContradiction
            fun (a : ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) ↦ by omega)⟩ :
         Fin (B.length + (1 : ℕ)));
       let jnext : Fin (B.length + (1 : ℕ)) :=
        (⟨A.length + (m + (1 : ℕ)),
          id
           (Decidable.byContradiction
            fun (a : ¬A.length + (m + (1 : ℕ)) < T.length - (1 : ℕ) + (1 : ℕ)) ↦ by
            omega)⟩ :
         Fin (B.length + (1 : ℕ)));
       let tnext : Fin T.length :=
        (⟨A.length + m,
          Decidable.byContradiction fun (a : ¬A.length + m < T.length) ↦ by omega⟩ :
         Fin T.length);
       alpha ∈ MissingColors G P.coloring (B.vertex jm) →
        ∀ theta ∈ MissingColors G P.coloring (B.vertex jnext),
         (∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
           ∀ c ∈ MissingColors G S.coloring (B.vertex jnext),
            c ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length)) →
             m + (1 : ℕ) ∈
              HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx) →
          (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
            ∀ b ∈ MissingColors G R.coloring (B.vertex jnext),
             ∀ (t : Fin T.length),
              A.length ≤ (↑t : ℕ) →
               (↑t : ℕ) < X.length →
                R.coloring (T.edge t) = some b →
                 TreeIncidentEdge
                   (R.corresponding.replacementETT.series.data.tree
                    (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                   (T.edge t) ∧
                  b ∈
                   TashkinovStoredColors R.corresponding.replacementETT.series.data
                    (Fin.last R.corresponding.replacementETT.rounds)) →
           (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
             ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
              ∀ (t : Fin T.length),
               A.length ≤ (↑t : ℕ) →
                (↑t : ℕ) < X.length →
                 R.coloring (T.edge t) = some b →
                  TreeIncidentEdge
                    (R.corresponding.replacementETT.series.data.tree
                     (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                    (T.edge t) ∧
                   b ∈
                    TashkinovStoredColors R.corresponding.replacementETT.series.data
                     (Fin.last R.corresponding.replacementETT.rounds)) →
            (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
              (eta a : Fin k),
              eta ∈
                HierarchyStoredColorsAt R.counterexample.hierarchy
                 (Fin.last R.counterexample.hierarchy.dividerCount) →
               a ∈
                 R.counterexample.good.gamma
                  (Fin.last R.counterexample.hierarchy.dividerCount) eta →
                eta ∈ MissingColors G R.coloring (B.vertex jnext) →
                 ∀ (t : Fin T.length),
                  A.length ≤ (↑t : ℕ) →
                   (↑t : ℕ) < X.length → R.coloring (T.edge t) ≠ some a) →
             theta ∈
               HierarchyStoredColorsAt P.counterexample.hierarchy
                (Fin.last P.counterexample.hierarchy.dividerCount) →
              m + (1 : ℕ) ∈
               HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch1894Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (∀ (psi : PartialEdgeColoring E k) (a b : Fin k),
    a ≠ b →
     IsProperEdgeColoring G psi →
      ∀ (B : Finset V),
       ColoredVertexSetElementary G psi B →
        ∀ (u v w : V),
         u ∈ B →
          v ∈ B →
           u ≠ v →
            w ≠ u →
             w ≠ v →
              a ∈ MissingColors G psi u →
               b ∈ MissingColors G psi v →
                a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w →
                 TwoColorComponent G psi a b (Sum.inl u) =
                   TwoColorComponent G psi a b (Sum.inl v) →
                  Disjoint (TwoColorComponent G psi a b (Sum.inl w))
                    (TwoColorComponent G psi a b (Sum.inl u)) ∧
                   TwoColorPathComponent G psi a b (Sum.inl w) ∧
                    ∀ x ∈ B,
                     MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
                      MissingColors G psi x) →
  (∀ {X Y Z : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
     TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  let A : TreeSequence G e0 :=
   HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount);
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount) =
     A) →
  TreeSequenceInitialSegment A T →
  ∀ (hlen : (4 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
    (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  TreeSequenceInitialSegment B T →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    HierarchyFullTailPrefix R.counterexample
      (HierarchyFullTailLength R.counterexample - (1 : ℕ)) =
     B) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B)) →
  (∀ (U : TreeSequence G e0) (j : Fin (U.length + (1 : ℕ))),
    U.vertex j ∈ TreeSequenceVertexSet U) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k)
    (j : Fin (B.length + (1 : ℕ))),
    c ∈ MissingColors G R.coloring (B.vertex j) →
     (↑(HierarchyFirstMissingPosition R.coloring T c) : ℕ) = (↑j : ℕ)) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (c : Fin k)
    (j : Fin (B.length + (1 : ℕ))),
    A.length < (↑j : ℕ) →
     c ∈ MissingColors G R.coloring (B.vertex j) → c ∉ TreeMissingColors R.coloring A) →
  (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ∀ c ∉ TreeMissingColors R.coloring A,
     c ∉
       HierarchyStoredColorsAt R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) →
      c ∉
       TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds)) →
  ∀ (m : ℕ) (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  ∀
   alpha ∈
    MissingColors G P.coloring
     ((HierarchyFullTailPrefix C m).vertex
      (Fin.last (HierarchyFullTailPrefix C m).length)),
   alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) →
    ∀ (hm : (2 : ℕ) ≤ m) (hmT : A.length + (m + (1 : ℕ)) < T.length),
     let X : TreeSequence G e0 :=
      TreeSequencePrefix T (A.length + (m + (1 : ℕ)))
       (have this : (1 : ℕ) ≤ A.length := A.positive;
       Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ A.length + (m + (1 : ℕ))) ↦ by
        omega)
       (Decidable.byContradiction fun (a : ¬A.length + (m + (1 : ℕ)) ≤ T.length) ↦ by
        omega);
     let jm : Fin (B.length + (1 : ℕ)) :=
      (⟨A.length + m,
        id
         (Decidable.byContradiction
          fun (a : ¬A.length + m < T.length - (1 : ℕ) + (1 : ℕ)) ↦ by omega)⟩ :
       Fin (B.length + (1 : ℕ)));
     let jnext : Fin (B.length + (1 : ℕ)) :=
      (⟨A.length + (m + (1 : ℕ)),
        id
         (Decidable.byContradiction
          fun (a : ¬A.length + (m + (1 : ℕ)) < T.length - (1 : ℕ) + (1 : ℕ)) ↦ by
          omega)⟩ :
       Fin (B.length + (1 : ℕ)));
     alpha ∈ MissingColors G P.coloring (B.vertex jm) →
      ∀ theta ∈ MissingColors G P.coloring (B.vertex jnext),
       (∀ (S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
         ∀ c ∈ MissingColors G S.coloring (B.vertex jnext),
          c ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length)) →
           m + (1 : ℕ) ∈
            HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx) →
        (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
          ∀ b ∈ MissingColors G R.coloring (B.vertex jm),
           ∀ (t : Fin T.length),
            A.length ≤ (↑t : ℕ) →
             (↑t : ℕ) < X.length →
              R.coloring (T.edge t) = some b →
               TreeIncidentEdge
                 (R.corresponding.replacementETT.series.data.tree
                  (Fin.last R.corresponding.replacementETT.rounds).castSucc)
                 (T.edge t) ∧
                b ∈
                 TashkinovStoredColors R.corresponding.replacementETT.series.data
                  (Fin.last R.corresponding.replacementETT.rounds)) →
         alpha ∉
           HierarchyStoredColorsAt P.counterexample.hierarchy
            (Fin.last P.counterexample.hierarchy.dividerCount) →
          theta ∉
            HierarchyStoredColorsAt P.counterexample.hierarchy
             (Fin.last P.counterexample.hierarchy.dividerCount) →
           m + (1 : ℕ) ∈
            HierarchyEligibleCommonMissingIndices G k e0 input T phi ett base C ctx

/-- Typed data construction shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperKF3658.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →
  [inst : Fintype V] →
  [inst_1 : Fintype E] →
  [inst_2 : DecidableEq V] →
  [inst_3 : DecidableEq E] →
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
  (hlenT : (3 : ℕ) ≤ T.length) →
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (have _ : (1 : ℕ) ≤ T.length := T.positive;
      Decidable.byContradiction
        fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by
        omega)
      (have _ : (1 : ℕ) ≤ T.length := T.positive;
      Decidable.byContradiction
        fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        have _ : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction
          fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by
          omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦
    if e = f then some alpha else mu e;
  (positiveB :
      (1 : ℕ) ≤ P.corresponding.replacementETT.rounds) →
  (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              have _ : (1 : ℕ) ≤ T.length := T.positive;
              Decidable.byContradiction
                fun
                  (a :
                    ¬P.corresponding.replacementETT.rounds <
                        P.corresponding.replacementETT.rounds +
                          (2 : ℕ)) ↦
                by omega⟩ :
            Fin
              (P.corresponding.replacementETT.rounds +
                (2 : ℕ))))
        B) →
  (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                have _ : (1 : ℕ) ≤ T.length :=
                  T.positive;
                Decidable.byContradiction
                  fun
                    (a :
                      ¬P.corresponding.replacementETT.rounds <
                          P.corresponding.replacementETT.rounds +
                            (2 : ℕ)) ↦
                  by omega⟩ :
              Fin
                (P.corresponding.replacementETT.rounds +
                  (2 : ℕ)))).length <
        B.length) →
  (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last
            (P.corresponding.replacementETT.rounds +
              (1 : ℕ))))) →
  (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last
            P.corresponding.replacementETT.rounds)) →
  (baseB :
      HierarchyBase
        {
          rounds :=
            P.corresponding.replacementETT.rounds,
          roundsPositive := positiveB,
          series :=
            P.corresponding.replacementETT.series,
          abovePenultimate := aboveB,
          strictAbovePenultimate := strictB,
          belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0
            P.corresponding.replacementInput B
            mu }
        mu) →
  (HB :
      TashkinovHierarchy
        {
          rounds :=
            P.corresponding.replacementETT.rounds,
          roundsPositive := positiveB,
          series :=
            P.corresponding.replacementETT.series,
          abovePenultimate := aboveB,
          strictAbovePenultimate := strictB,
          belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0
            P.corresponding.replacementInput B
            mu }
        baseB) →
  let EB :
    ExtendedTashkinovTree G k e0
      P.corresponding.replacementInput B
      mu :=
    {
      rounds :=
        P.corresponding.replacementETT.rounds,
      roundsPositive := positiveB,
      series :=
        P.corresponding.replacementETT.series,
      abovePenultimate := aboveB,
      strictAbovePenultimate := strictB,
      belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0
        P.corresponding.replacementInput B
        mu };
  (corr :
      CorrespondingExtendedTashkinovTree G k
        e0 EB sigma B) →
  (bs :
      HierarchyBase corr.replacementETT
        sigma) →
  HB.stage
        (0 :
          Fin
            (HB.dividerCount +
              (2 : ℕ))) =
      corr.replacementETT.series.data.tree
        (Fin.last
            corr.replacementETT.rounds).castSucc →
  HB.stage
        (Fin.last
          (HB.dividerCount +
            (1 : ℕ))) =
      B →
  (∀
      (j :
        Fin
          (HB.dividerCount +
            (1 : ℕ))),
      TreeSequenceInitialSegment
        (HB.stage j.castSucc)
        (HB.stage j.succ)) →
  (∀
      (j :
        Fin
          (HB.dividerCount +
            (1 : ℕ))),
      (HB.stage
            j.castSucc).length <
        (HB.stage
            j.succ).length) →
  TreeSequenceInitialSegment
      bs.core
      (HB.stage
        (⟨(1 : ℕ),
            have _ :
              (1 : ℕ) ≤
                T.length :=
              T.positive;
            have _ :
              (1 : ℕ) ≤
                B.length :=
              B.positive;
            Decidable.byContradiction
              fun
                (a :
                  ¬(1 : ℕ) <
                      HB.dividerCount +
                        (2 :
                          ℕ)) ↦
              by omega⟩ :
          Fin
            (HB.dividerCount +
              (2 : ℕ)))) →
  (positiveK :
      ∀
        (i :
          Fin
            HB.dividerCount),
        (1 : ℕ) ≤
          (↑(HB.dividerPosition
                i) :
            ℕ)) →
  (∀
      (i j :
        Fin
          HB.dividerCount),
      (↑i : ℕ) < (↑j : ℕ) →
        (↑(HB.dividerPosition
                i) :
            ℕ) <
          (↑(HB.dividerPosition
                j) :
            ℕ)) →
  (∀
      (i :
        Fin
          HB.dividerCount),
      HB.stage
          (⟨(↑i : ℕ) +
                (1 : ℕ),
              have _ :
                (1 : ℕ) ≤
                  T.length :=
                T.positive;
              have _ :
                (1 : ℕ) ≤
                  B.length :=
                B.positive;
              Decidable.byContradiction
                fun
                  (a :
                    ¬(↑i :
                            ℕ) +
                          (1 :
                            ℕ) <
                        HB.dividerCount +
                          (2 :
                            ℕ)) ↦
                by
                omega⟩ :
            Fin
              (HB.dividerCount +
                (2 :
                  ℕ))) =
        TreeSequencePrefix
          B
          (↑(HB.dividerPosition
                i) :
            ℕ)
          (positiveK i)
          (have _ :
            (1 : ℕ) ≤
              T.length :=
            T.positive;
          have _ :
            (1 : ℕ) ≤
              B.length :=
            B.positive;
          Decidable.byContradiction
            fun
              (a :
                ¬(↑(HB.dividerPosition
                          i) :
                      ℕ) ≤
                    B.length) ↦
            by omega)) →
  TashkinovHierarchy
    corr.replacementETT
    bs := by
  classical
  intro V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett base C ctx P alpha mu hlenT B r f
      sigma positiveB aboveB strictB belowB generatingB baseB HB EB corr bs baseStageK
      terminalStageK nestedK strictK coreInsideK positiveK increasingK dividerStageK
  exact {
    dividerCount :=
      HB.dividerCount,
    stage := HB.stage,
    baseStage :=
      baseStageK,
    terminalStage :=
      terminalStageK,
    nested := nestedK,
    strict := strictK,
    dividerPosition :=
      HB.dividerPosition,
    dividerPositive :=
      positiveK,
    dividerIncreasing :=
      increasingK,
    dividerStage :=
      dividerStageK,
    coreInsideFirst :=
      coreInsideK :
    TashkinovHierarchy
      corr.replacementETT
      bs };

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperUniqueRefresh4523Conditions.{u_1, u_2} : Prop :=
  SharedFacts.ShorteningProofs.uniqueRefreshTransportStatement.{u_1, u_2}


/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperParallelBase4547Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := old.hierarchy;
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
   Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hp : HierarchyPathNumber H = HierarchyPathNumber C.hierarchy) (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (1 : ℕ))
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  let X : TreeSequence G e0 :=
   TreeSequencePrefix T (T.length - (2 : ℕ))
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) ↦ by omega)
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) ↦ by omega);
  ∀ (hTnX : TreeSequenceInitialSegment Tn X),
  let r : Fin T.length :=
   (⟨T.length - (1 : ℕ),
     have this : (1 : ℕ) ≤ T.length := T.positive;
     Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
    Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀
   (missingTree :
    ∀ (U : TreeSequence G e0),
     TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X →
      TreeMissingColors sigma U = TreeMissingColors mu U)
   (minusEq :
    ∀ (U : TreeSequence G e0),
     TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X →
      ∀ (R : Finset (Fin k)),
       TreeColorSetMinusClosed G sigma U R ↔ TreeColorSetMinusClosed G mu U R)
   (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (P.corresponding.replacementETT.series.data.tree
      (⟨P.corresponding.replacementETT.rounds,
        have this : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction
         fun
          (a :
           ¬P.corresponding.replacementETT.rounds <
             P.corresponding.replacementETT.rounds + (2 : ℕ)) ↦
         by omega⟩ :
       Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
     B)
   (strictB :
    (P.corresponding.replacementETT.series.data.tree
       (⟨P.corresponding.replacementETT.rounds,
         have this : (1 : ℕ) ≤ T.length := T.positive;
         Decidable.byContradiction
          fun
           (a :
            ¬P.corresponding.replacementETT.rounds <
              P.corresponding.replacementETT.rounds + (2 : ℕ)) ↦
          by omega⟩ :
        Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (P.corresponding.replacementETT.series.data.tree
      (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
   (generatingB :
    mu =
     P.corresponding.replacementETT.series.data.coloring
      (Fin.last P.corresponding.replacementETT.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     mu)
   (HB :
    TashkinovHierarchy
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     baseB)
   (goodB : GoodHierarchy HB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
   {
    rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
    series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
    strictAbovePenultimate := strictB, belowFinal := belowB, generatingColoring := generatingB :
    ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (coreBX : TreeSequenceVertexSet baseB.core ⊆ TreeSequenceVertexSet X)
   (closureBX :
    EB.series.data.kind (Fin.last EB.rounds) = some TashkinovExtensionKind.PE →
     TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X)
   (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
   (bs : HierarchyBase corr.replacementETT sigma) (hcore : baseB.core = bs.core)
   (hpe :
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
         series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
         strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := generatingB :
         ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.series.data.kind
       (Fin.last
        {
         rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.rounds) =
      some TashkinovExtensionKind.PE ↔
     corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
      some TashkinovExtensionKind.PE)
   (hclosure :
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
         series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
         strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := generatingB :
         ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.series.data.kind
       (Fin.last
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.rounds) =
      some TashkinovExtensionKind.PE →
     baseB.closure = bs.closure)
   (baseStageK :
    HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
     corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc)
   (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
   (nestedK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
   (strictK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     (HB.stage j.castSucc).length < (HB.stage j.succ).length)
   (coreInsideK :
    TreeSequenceInitialSegment bs.core
     (HB.stage
      (⟨(1 : ℕ),
        have this : (1 : ℕ) ≤ T.length := T.positive;
        have this : (1 : ℕ) ≤ B.length := B.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) < HB.dividerCount + (2 : ℕ)) ↦ by omega⟩ :
       Fin (HB.dividerCount + (2 : ℕ)))))
   (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
   (increasingK :
    ∀ (i j : Fin HB.dividerCount),
     (↑i : ℕ) < (↑j : ℕ) → (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
   (dividerStageK :
    ∀ (i : Fin HB.dividerCount),
     HB.stage
       (⟨(↑i : ℕ) + (1 : ℕ),
         have this : (1 : ℕ) ≤ T.length := T.positive;
         have this : (1 : ℕ) ≤ B.length := B.positive;
         Decidable.byContradiction fun (a : ¬(↑i : ℕ) + (1 : ℕ) < HB.dividerCount + (2 : ℕ)) ↦
          by omega⟩ :
        Fin (HB.dividerCount + (2 : ℕ))) =
      TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
       (have this : (1 : ℕ) ≤ T.length := T.positive;
       have this : (1 : ℕ) ≤ B.length := B.positive;
       Decidable.byContradiction fun (a : ¬(↑(HB.dividerPosition i) : ℕ) ≤ B.length) ↦ by
        omega)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
   helperKF3658 G k e0 input T phi ett base C ctx P alpha hlenT positiveB aboveB strictB belowB
    generatingB baseB HB corr bs baseStageK terminalStageK nestedK strictK coreInsideK
    positiveK increasingK dividerStageK;
  ∀
   (terminalTree :
    corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc = Tn)
   (storedEq :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HierarchyStoredColorsAt KF j = HierarchyStoredColorsAt HB j),
  let n : Fin (corr.replacementETT.rounds + (1 : ℕ)) := Fin.last corr.replacementETT.rounds;
  let Tn : TreeSequence G e0 := corr.replacementETT.series.data.tree n.castSucc;
  corr.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE →
  ¬TreeColorSetMinusClosed G sigma bs.core
     ((HierarchyStoredColorsAt KF (0 : Fin (KF.dividerCount + (1 : ℕ)))).biUnion
      (goodB.gamma (0 : Fin (KF.dividerCount + (1 : ℕ))))) ∧
   (4 : ℕ) ≤
    ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma bs.closure : Finset (Fin k)) \
      (HierarchyStoredColorsAt KF (0 : Fin (KF.dividerCount + (1 : ℕ)))).biUnion
       (goodB.gamma (0 : Fin (KF.dividerCount + (1 : ℕ))))).card

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperSameLast4591Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) {a b : ℕ}
   (s : Fin (a + (2 : ℕ)) → TreeSequence G e0) (t : Fin (b + (2 : ℕ)) → TreeSequence G e0)
   (u v : TreeSequence G e0),
  a = b →
  s ≍ t →
  u = v →
  (Fin.cases u (fun (i : Fin a) ↦ s i.castSucc.succ) (Fin.last a) : TreeSequence G e0) =
   (Fin.cases v (fun (i : Fin b) ↦ t i.castSucc.succ) (Fin.last b) : TreeSequence G e0)

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation5341Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (hpathLower : (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
   Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hp : HierarchyPathNumber H = HierarchyPathNumber C.hierarchy)
   (hpUpper : HierarchyPathNumber H < T.length - A.length) (htail : (2 : ℕ) ≤ T.length - A.length)
   (trans :
    ∀ {X Y Z : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y)
     (hYZ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)
   (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (by omega) (by omega);
  let X : TreeSequence G e0 := TreeSequencePrefix T (T.length - (2 : ℕ)) (by omega) (by omega);
  ∀ (hBlength : B.length = T.length - (1 : ℕ)) (hXlength : X.length = T.length - (2 : ℕ))
   (hBT : TreeSequenceInitialSegment B T) (hXB : TreeSequenceInitialSegment X B)
   (hTnX : TreeSequenceInitialSegment Tn X),
  let r : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  ∀
   (consecutive :
    ∀ (t : Fin T.length) (ht : A.length + HierarchyPathNumber H ≤ (↑t : ℕ)),
     G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ))
   (hyf : Incident G y f) (S : TreeSequence G e0) (hSBlen : S.length ≤ B.length) (beta : Fin k)
   (hbetaF : mu f = some beta) (z : V) (hzB : z ∈ TreeSequenceVertexSet B)
   (hbetaz : beta ∈ MissingColors G mu z) (hzy : z ≠ y) (hzX : z ∈ TreeSequenceVertexSet X)
   (hab : alpha ≠ beta),
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (fixed : ∀ (e : E) (hef : e ≠ f), sigma e = mu e)
   (missingFixed :
    ∀ (v : V) (hv : v ∈ TreeSequenceVertexSet X),
     MissingColors G sigma v = MissingColors G mu v)
   (fixedB : ∀ (t : Fin B.length), sigma (B.edge t) = mu (B.edge t))
   (missingTree :
    ∀ (U : TreeSequence G e0) (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X),
     TreeMissingColors sigma U = TreeMissingColors mu U)
   (minusEq :
    ∀ (U : TreeSequence G e0) (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X)
     (R : Finset (Fin k)),
     TreeColorSetMinusClosed G sigma U R ↔ TreeColorSetMinusClosed G mu U R)
   (lastPositive :
    ∀ (hq : H.dividerCount ≠ (0 : ℕ)),
     A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
   (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (P.corresponding.replacementETT.series.data.tree
      (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
       Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
     B)
   (strictB :
    (P.corresponding.replacementETT.series.data.tree
       (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
        Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (P.corresponding.replacementETT.series.data.tree
      (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
   (generatingB :
    mu =
     P.corresponding.replacementETT.series.data.coloring
      (Fin.last P.corresponding.replacementETT.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     mu)
   (HB :
    TashkinovHierarchy
     {
      rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
     baseB)
   (hcountB : HB.dividerCount = H.dividerCount)
   (hstagesB :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HB.stage j.castSucc = H.stage (Fin.cast (by omega) j).castSucc ∧
      HierarchyStarredStage HB j = HierarchyStarredStage H (Fin.cast (by omega) j))
   (goodB : GoodHierarchy HB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
   {
    rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
    series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
    strictAbovePenultimate := strictB, belowFinal := belowB,
    generatingColoring := generatingB :
    ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (coreBX : TreeSequenceVertexSet baseB.core ⊆ TreeSequenceVertexSet X)
   (closureBX :
    ∀ (hpe : EB.series.data.kind (Fin.last EB.rounds) = some TashkinovExtensionKind.PE),
     TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X)
   (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
   (hmaximum : MaximumProperty corr.replacementETT)
   (bs : HierarchyBase corr.replacementETT sigma) (hcore : baseB.core = bs.core)
   (hpe :
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
         series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
         strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := generatingB :
         ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.series.data.kind
       (Fin.last
        {
         rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.rounds) =
      some TashkinovExtensionKind.PE ↔
     corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
      some TashkinovExtensionKind.PE)
   (hclosure :
    {
     rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
         series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
         strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := generatingB :
         ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.series.data.kind
       (Fin.last
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }.rounds) =
      some TashkinovExtensionKind.PE →
     baseB.closure = bs.closure)
   (baseStageK :
    HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
     corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc)
   (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
   (nestedK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
   (strictK :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     (HB.stage j.castSucc).length < (HB.stage j.succ).length)
   (coreInsideK :
    TreeSequenceInitialSegment bs.core
     (HB.stage (⟨(1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ)))))
   (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
   (increasingK :
    ∀ (i j : Fin HB.dividerCount),
     (↑i : ℕ) < (↑j : ℕ) → (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
   (dividerStageK :
    ∀ (i : Fin HB.dividerCount),
     HB.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ))) =
      TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
       (Nat.le_of_lt_succ (HB.dividerPosition i).isLt)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
   {
    dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
    terminalStage := terminalStageK, nested := nestedK, strict := strictK,
    dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
    dividerIncreasing := increasingK, dividerStage := dividerStageK,
    coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  ∀
   (starredEq :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     HierarchyStarredStage KF j = HierarchyStarredStage HB j)
   (stageBX :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     TreeSequenceInitialSegment (HB.stage j.castSucc) X)
   (starBX :
    ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
     TreeSequenceVertexSet (HierarchyStarredStage HB j) ⊆ TreeSequenceVertexSet X)
   (allStageB :
    ∀ (j : Fin (HB.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (HB.stage j) B)
   (terminalTree :
    corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc = Tn)
   (terminalStored :
    TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) =
     TashkinovStoredColors EB.series.data (Fin.last EB.rounds)),
  False

/-- Dependent contract shared by the eligible-index bound proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation5697Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (hpathLower : (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase := old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
   Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 := P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hp : HierarchyPathNumber H = HierarchyPathNumber C.hierarchy)
   (hpUpper : HierarchyPathNumber H < T.length - A.length) (htail : (2 : ℕ) ≤ T.length - A.length)
   (trans :
    ∀ {X Y Z : TreeSequence G e0} (hXY : TreeSequenceInitialSegment X Y)
     (hYZ : TreeSequenceInitialSegment Y Z), TreeSequenceInitialSegment X Z)
   (chain :
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))),
     (↑i : ℕ) ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 : ℕ)))))
   (coreA : TreeSequenceInitialSegment P.replacementBase.core A)
   (hTnA : TreeSequenceInitialSegment Tn A) (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (by omega) (by omega);
  let X : TreeSequence G e0 := TreeSequencePrefix T (T.length - (2 : ℕ)) (by omega) (by omega);
  ∀ (hBlength : B.length = T.length - (1 : ℕ)) (hXlength : X.length = T.length - (2 : ℕ))
   (hBT : TreeSequenceInitialSegment B T) (hAX : TreeSequenceInitialSegment A X)
   (hXB : TreeSequenceInitialSegment X B) (hTnX : TreeSequenceInitialSegment Tn X)
   (hAB : TreeSequenceInitialSegment A B),
  let r : Fin T.length := (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  let w : V := T.vertex (Fin.last T.length);
  ∀
   (consecutive :
    ∀ (t : Fin T.length) (ht : A.length + HierarchyPathNumber H ≤ (↑t : ℕ)),
     G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ))
   (hends : G.ends f = s(y, w)) (hyf : Incident G y f) (S : TreeSequence G e0)
   (hSBlen : S.length ≤ B.length) (beta : Fin k) (hbetaF : mu f = some beta) (z : V)
   (hzB : z ∈ TreeSequenceVertexSet B) (hbetaz : beta ∈ MissingColors G mu z) (hzy : z ≠ y)
   (hzX : z ∈ TreeSequenceVertexSet X) (hab : alpha ≠ beta),
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (fixed : ∀ (e : E) (hef : e ≠ f), sigma e = mu e) (hsproper : IsProperEdgeColoring G sigma)
   (hsone : IsOneEdgeUncolored sigma e0)
   (incidentFixed : ∀ (e : E) (he : TreeIncidentEdge X e), sigma e = mu e)
   (missingFixed :
    ∀ (v : V) (hv : v ∈ TreeSequenceVertexSet X),
     MissingColors G sigma v = MissingColors G mu v)
   (fixedB : ∀ (t : Fin B.length), sigma (B.edge t) = mu (B.edge t))
   (stable :
    StableColoring Tn (TashkinovStoredColors P.corresponding.replacementETT.series.data n)
     (P.corresponding.replacementETT.series.data.coloring n) sigma)
   (hrouteB :
    P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence sigma Tn B ∨
     (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
       P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (edge : E) (seed : TreeSequence G e0),
       P.corresponding.replacementETT.series.data.connectingEdges n = ({ edge } : Finset E) ∧
        TreeSequenceAdjoinEdge Tn edge seed ∧ TashkinovAugmentationSequence sigma seed B)
   (missingTree :
    ∀ (U : TreeSequence G e0) (hUX : TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X),
     TreeMissingColors sigma U = TreeMissingColors mu U),
  False

theorem helper_coreA_200.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  (∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))),
      (↑i : ℕ) ≤ j →
        TreeSequenceInitialSegment (H.stage i)
          (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
  TreeSequenceInitialSegment P.replacementBase.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P old H A trans chain
  by_cases hq : H.dividerCount = 0
  · have he : A = P.replacementBase.core := by
      simp [A, HierarchyStarredStage, hq, Fin.last]
    rw [he]
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · have he : A = H.stage ⟨H.dividerCount, by omega⟩ := by
      unfold A HierarchyStarredStage
      obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
      · have hv := congrArg Fin.val hz
        simp only [Fin.val_last, Fin.val_zero] at hv
        contradiction
      · rw [hi]
        simp only [Fin.cases_succ]
        congr 1
        apply Fin.ext
        have hv := congrArg Fin.val hi
        simp only [Fin.val_last, Fin.val_succ] at hv
        exact hv.symm
    rw [he]
    exact trans H.coreInsideFirst (chain H.dividerCount (by omega) ⟨1, by omega⟩
      (by change 1 ≤ H.dividerCount; omega))

alias helper_hsproper_329 :=
  SharedFacts.ShorteningProofs.properRecoloring

theorem helper_hdata_519.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  HierarchyPathNumber H = HierarchyPathNumber C.hierarchy →
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) ↦ by omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  (∀ (e : E), TreeIncidentEdge X e → sigma e = mu e) →
  (∀ v ∈ TreeSequenceVertexSet X, MissingColors G sigma v = MissingColors G mu v) →
  StableColoring Tn (TashkinovStoredColors P.corresponding.replacementETT.series.data n)
      (P.corresponding.replacementETT.series.data.coloring n) sigma →
  (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn B ∨
      (P.corresponding.replacementETT.series.data.kind n =
            some TashkinovExtensionKind.SE ∨
          P.corresponding.replacementETT.series.data.kind n =
            some TashkinovExtensionKind.RE) ∧
        ∃ (edge : E) (seed : TreeSequence G e0),
          P.corresponding.replacementETT.series.data.connectingEdges n = { edge } ∧
            TreeSequenceAdjoinEdge Tn edge seed ∧
              TashkinovAugmentationSequence sigma seed B) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds)),
  MaximumProperty
      { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
        series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
        strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := generatingB :
        ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu } →
  ∀
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  (EB.series.data.kind (Fin.last EB.rounds) = some TashkinovExtensionKind.PE →
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X) →
  ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B),
  MaximumProperty corr.replacementETT ∧
    ∃ (bs : HierarchyBase corr.replacementETT sigma) (K :
      TashkinovHierarchy corr.replacementETT bs), SameHierarchyStages HB K := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H n Tn mu hp trans hlenT B X r
      f S hSBlen sigma hsproper hsone incidentFixed missingFixed stable hrouteB positiveB aboveB
      strictB belowB generatingB hmaxB baseB HB EB closureBX
  by_cases hpe : EB.series.data.kind (Fin.last EB.rounds) =
      some TashkinovExtensionKind.PE
  · have hb : TashkinovAugmentationSequence sigma Tn B := by
      rcases hrouteB with h | h
      · exact h.2
      · rcases h.1 with h | h <;> rw [hpe] at h <;> cases h
    have hcomb : CombinedStableColoring Tn baseB.closure
        (TashkinovStoredColors EB.series.data (Fin.last EB.rounds)) mu sigma := by
      refine ⟨?_, ?_⟩
      · have hh := stable
        change StableColoring Tn
          (TashkinovStoredColors EB.series.data (Fin.last EB.rounds))
          (P.corresponding.replacementETT.series.data.coloring
            (Fin.last P.corresponding.replacementETT.rounds)) sigma at hh
        rw [← P.corresponding.replacementETT.generatingColoring] at hh
        exact hh
      · refine ⟨?_, ?_⟩
        · intro edge he _
          obtain ⟨v, hv, hi⟩ := he
          exact incidentFixed edge ⟨v, closureBX hpe hv, hi⟩
        · intro v hv
          exact missingFixed v (closureBX hpe hv)
    exact HierarchySplitter G k e0 P.corresponding.replacementInput B mu sigma EB
      hmaxB old.positive P.minimumContext.lowerRung baseB HB hpe
      P.minimumContext.proper P.minimumContext.oneEdgeUncolored hsproper hsone hcomb hb
  · have hmodB := Td G k e0 P.corresponding.replacementInput B mu EB hmaxB
      old.positive P.minimumContext.lowerRung sigma hsproper hsone stable
    obtain ⟨corr⟩ := hmodB.2.2 B aboveB strictB hrouteB
    have hmaximum := MaximumPropertyTransport G k e0 EB sigma hmodB B corr hmaxB
    have terminalTree : corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
      rcases corr with ⟨ri, rs, re, hr, hp, hc, hl, hstored, he, hk, hpr, ho, hst⟩
      rcases re with ⟨rounds, positive, data, above, strict, below, generating⟩
      cases hr
      have hs : data = rs := eq_of_heq hp
      cases hs
      let j : Fin EB.rounds := ⟨EB.rounds - 1, by have := EB.roundsPositive; omega⟩
      have hj : j.succ = Fin.last EB.rounds := Fin.ext (by
        dsimp [j]; have := EB.roundsPositive; omega)
      change rs.data.tree (Fin.last EB.rounds).castSucc =
        EB.series.data.tree (Fin.last EB.rounds).castSucc
      rw [← hj]
      exact hl j
    have terminalKind : corr.replacementETT.series.data.kind
        (Fin.last corr.replacementETT.rounds) = EB.series.data.kind (Fin.last EB.rounds) := by
      rcases corr with ⟨ri, rs, re, hr, hp, hc, hl, hstored, he, hk, hpr, ho, hst⟩
      rcases re with ⟨rounds, positive, data, above, strict, below, generating⟩
      cases hr
      have hs : data = rs := eq_of_heq hp
      cases hs
      exact hk _
    let bs : HierarchyBase corr.replacementETT sigma := {
      core := baseB.core
      closure := baseB.closure
      supportPosition := Fin.cast (congrArg (fun U : TreeSequence G e0 => U.length + 1)
        terminalTree.symm) baseB.supportPosition
      supportPositive := baseB.supportPositive
      terminalMissingColors := rfl
      parallel := by
        dsimp only
        intro hp
        exact (hpe (terminalKind.symm.trans hp)).elim
      nonparallel := by
        dsimp only
        intro _
        exact (baseB.nonparallel hpe).trans terminalTree.symm }
    let K : TashkinovHierarchy corr.replacementETT bs := {
      dividerCount := HB.dividerCount
      stage := HB.stage
      baseStage := HB.baseStage.trans terminalTree.symm
      terminalStage := HB.terminalStage
      nested := HB.nested
      strict := HB.strict
      dividerPosition := HB.dividerPosition
      dividerPositive := HB.dividerPositive
      dividerIncreasing := HB.dividerIncreasing
      dividerStage := HB.dividerStage
      coreInsideFirst := HB.coreInsideFirst }
    refine ⟨corr, hmaximum, bs, K, rfl, rfl, heq_of_eq rfl, heq_of_eq rfl, ?_, ?_⟩
    · exact ⟨fun h => (hpe h).elim, fun h => (hpe (terminalKind.symm.trans h)).elim⟩
    · intro _; rfl

alias helper_terminalStored_647 :=
  SharedFacts.ShorteningProofs.terminalStoredColors

theorem helper_hpS_844.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  (2 : ℕ) ≤ HierarchyPathNumber C.hierarchy →
  ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let mu : PartialEdgeColoring E k := P.coloring;
  HierarchyPathNumber H = HierarchyPathNumber C.hierarchy →
  HierarchyPathNumber H < T.length - A.length →
  (2 : ℕ) ≤ T.length - A.length →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  TreeSequenceInitialSegment B T →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  (∀ (t : Fin T.length),
      A.length + HierarchyPathNumber H ≤ (↑t : ℕ) →
        G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)) →
  ∀ (S : TreeSequence G e0) (_ : S.length ≤ B.length) (beta : Fin k),
  alpha ≠ beta →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (H.dividerCount ≠ (0 : ℕ) →
      A =
        H.stage
          (⟨H.dividerCount,
              Decidable.byContradiction
                fun (a : ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦ by omega⟩ :
            Fin (H.dividerCount + (2 : ℕ)))) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
    (bs : HierarchyBase corr.replacementETT sigma)
    (baseStageK :
      HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc)
    (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
    (nestedK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
    (strictK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        (HB.stage j.castSucc).length < (HB.stage j.succ).length)
    (coreInsideK :
      TreeSequenceInitialSegment bs.core
        (HB.stage (⟨(1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ)))))
    (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
    (increasingK :
      ∀ (i j : Fin HB.dividerCount),
        (↑i : ℕ) < (↑j : ℕ) →
          (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
    (dividerStageK :
      ∀ (i : Fin HB.dividerCount),
        HB.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ))) =
          TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
            (Nat.le_of_lt_succ (HB.dividerPosition i).isLt)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
    { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
      terminalStage := terminalStageK, nested := nestedK, strict := strictK,
      dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
      dividerIncreasing := increasingK, dividerStage := dividerStageK,
      coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  HierarchyStarredStage KF (Fin.last KF.dividerCount) = A →
  HierarchyPathNumber KF ≤ HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathLower P alpha old H A mu hp hpUpper
      htail hlenT B hBT r f consecutive S hSBlen beta hab sigma lastPositive positiveB aboveB
      strictB belowB generatingB baseB HB EB corr bs baseStageK terminalStageK nestedK strictK
      coreInsideK positiveK increasingK dividerStageK KF lastStar
  let candidates := (Finset.Icc 1 (B.length - A.length)).filter fun i =>
    ∀ t : Fin B.length, A.length + i ≤ t.val →
      G.ends (B.edge t) = s(B.vertex t.castSucc, B.vertex t.succ)
  have hm : HierarchyPathNumber H ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by
      dsimp [B, TreeSequencePrefix]
      omega⟩, ?_⟩
    intro t ht
    rw [← hBT.2.2 t]
    have hc := consecutive (Fin.castLE hBT.1 t) ht
    have hv1 : (Fin.castLE hBT.1 t).castSucc =
        Fin.castLE (Nat.succ_le_succ hBT.1) t.castSucc := Fin.ext rfl
    have hv2 : (Fin.castLE hBT.1 t).succ =
        Fin.castLE (Nat.succ_le_succ hBT.1) t.succ := Fin.ext rfl
    rw [hv1, hv2, hBT.2.1 t.castSucc, hBT.2.1 t.succ] at hc
    exact hc
  have hn : candidates.Nonempty := ⟨HierarchyPathNumber H, hm⟩
  unfold HierarchyPathNumber
  dsimp only
  rw [lastStar]
  change (if h : candidates.Nonempty then candidates.min' h else B.length - A.length) ≤ _
  rw [dite_eq_left hn]
  exact Finset.min'_le candidates _ hm

theorem helper_consecutive_852.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  HierarchyPathNumber H < T.length - A.length →
  (3 : ℕ) ≤ T.length →
  ∀ (t : Fin T.length),
  A.length + HierarchyPathNumber H ≤ (↑t : ℕ) →
  G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P old H A hpUpper hlenT t ht
  let candidates := (Finset.Icc 1 (T.length - A.length)).filter fun i =>
    ∀ t : Fin T.length, A.length + i ≤ t.val →
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
  have hp' : HierarchyPathNumber H =
      (if h : candidates.Nonempty then candidates.min' h else T.length - A.length) := rfl
  have hn : candidates.Nonempty := by
    by_contra hn
    rw [dite_eq_right hn] at hp'
    omega
  have hm : candidates.min' hn = HierarchyPathNumber H := by
    simpa only [dite_eq_left hn] using hp'.symm
  have hc := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  rw [hm] at hc
  exact hc t ht

theorem helper_noInc_930.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (_ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) ↦ by omega);
  X.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment X T →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  let w : V := T.vertex (Fin.last T.length);
  T.vertex r.castSucc = y →
  G.ends f = s(y, w) →
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  ∀ (beta : Fin k),
  alpha ≠ beta →
  ∀ v ∈ TreeSequenceVertexSet X,
  ¬Incident G v f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha trans hlenT B X hXlength hXT r f y
      w hy hends S hSBlen beta hab v hv
  obtain ⟨j, hj⟩ : ∃ j, X.vertex j = v := by simpa [TreeSequenceVertexSet] using hv
  intro hi
  have hv' : v = y ∨ v = w := by simpa only [Incident, hends, Sym2.mem_iff] using hi
  rcases hv' with he | he
  · have hh := T.vertex_injective ((hXT.2.1 j).trans (hj.trans (he.trans hy.symm)))
    have hh := congrArg Fin.val hh
    have hj := j.isLt
    change j.val = T.length - 1 at hh
    change j.val < X.length + 1 at hj
    omega
  · have hh := T.vertex_injective ((hXT.2.1 j).trans (hj.trans he))
    have hh := congrArg Fin.val hh
    have hj := j.isLt
    change j.val = T.length at hh
    change j.val < X.length + 1 at hj
    omega

theorem helper_hrouteB_979.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (2 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (2 : ℕ) ≤ T.length) ↦ by omega);
  B.length = T.length - (1 : ℕ) →
  X.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  (∀ {S U W : TreeSequence G e0},
      TreeSequenceInitialSegment S W →
        TreeSequenceInitialSegment U W →
          S.length ≤ U.length → TreeSequenceInitialSegment S U) →
  TreeSequenceInitialSegment X B →
  TreeSequenceInitialSegment Tn X →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0) (hSBlen : S.length ≤ B.length),
  TashkinovAugmentationSequence mu S T →
  TreeSequenceInitialSegment
      (TreeSequencePrefix T (↑r : ℕ)
        (le_trans S.positive
          (id
            (Eq.mp
              (congrArg (LE.le S.length)
                (congrArg TreeSequence.length
                  (TreeSequencePrefix.eq_1 T (T.length - (1 : ℕ))
                    (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦
                      by omega)
                    (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦
                      by omega))))
              hSBlen)))
        (Nat.le_of_lt r.isLt))
      (TreeSequencePrefix T ((↑r : ℕ) + (1 : ℕ)) (by omega) (Nat.succ_le_of_lt r.isLt)) →
  ∀ (beta : Fin k),
  alpha ≠ beta →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ v ∈ TreeSequenceVertexSet X, MissingColors G sigma v = MissingColors G mu v) →
  (∀ (t : Fin B.length), sigma (B.edge t) = mu (B.edge t)) →
  P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence sigma Tn B ∨
    (P.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        P.corresponding.replacementETT.series.data.kind n =
          some TashkinovExtensionKind.RE) ∧
      ∃ (edge : E) (seed : TreeSequence G e0),
        P.corresponding.replacementETT.series.data.connectingEdges n = { edge } ∧
          TreeSequenceAdjoinEdge Tn edge seed ∧ TashkinovAugmentationSequence sigma seed B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha n Tn mu trans hlenT B X hBlength
      hXlength hBT common hXB hTnX r f S hSBlen hseq hpre beta hab sigma missingFixed fixedB
  rcases P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu
    P.corresponding.replacementETT with ⟨hpe, hseq⟩ |
      ⟨hkind, edge, seed, hedges, hseed, hincident, hcontrol, hseq⟩
  · have hpre := TashkinovAugmentationSequenceRestrict mu Tn B T hseq
      (trans hTnX hXB) hBT
    exact Or.inl ⟨hpe, TashkinovAugmentationSequenceColoringTransport mu sigma
      Tn X B hpre hXB (by omega) (fun t _ => fixedB t) missingFixed⟩
  · have hseedLen : seed.length = Tn.length + 1 := hseed.1
    have hseedB := common
      (TashkinovAugmentationSequenceInitialSegment mu seed T hseq) hBT
      (by have := hTnX.1; omega)
    have hpre := TashkinovAugmentationSequenceRestrict mu seed B T hseq hseedB hBT
    exact Or.inr ⟨hkind, edge, seed, hedges, hseed,
      TashkinovAugmentationSequenceColoringTransport mu sigma seed X B hpre hXB
        (by omega) (fun t _ => fixedB t) missingFixed⟩

theorem helper_terminalTree_1110.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  HierarchyPathNumber H = HierarchyPathNumber C.hierarchy →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B),
  MaximumProperty corr.replacementETT →
  ∀ (bs : HierarchyBase corr.replacementETT sigma),
  baseB.core = bs.core →
  ({ rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
              series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
              strictAbovePenultimate := strictB, belowFinal := belowB,
              generatingColoring := generatingB :
              ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                mu }.series.data.kind
          (Fin.last
            { rounds := P.corresponding.replacementETT.rounds,
                roundsPositive := positiveB,
                series := P.corresponding.replacementETT.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := generatingB :
                ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                  mu }.rounds) =
        some TashkinovExtensionKind.PE ↔
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
        some TashkinovExtensionKind.PE) →
  ({ rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
              series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
              strictAbovePenultimate := strictB, belowFinal := belowB,
              generatingColoring := generatingB :
              ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                mu }.series.data.kind
          (Fin.last
            { rounds := P.corresponding.replacementETT.rounds,
                roundsPositive := positiveB,
                series := P.corresponding.replacementETT.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := generatingB :
                ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                  mu }.rounds) =
        some TashkinovExtensionKind.PE →
      baseB.closure = bs.closure) →
  ∀
    (baseStageK :
      HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc)
    (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
    (nestedK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
    (strictK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        (HB.stage j.castSucc).length < (HB.stage j.succ).length)
    (coreInsideK :
      TreeSequenceInitialSegment bs.core
        (HB.stage (⟨(1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ)))))
    (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
    (increasingK :
      ∀ (i j : Fin HB.dividerCount),
        (↑i : ℕ) < (↑j : ℕ) →
          (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
    (dividerStageK :
      ∀ (i : Fin HB.dividerCount),
        HB.stage (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (HB.dividerCount + (2 : ℕ))) =
          TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
            (Nat.le_of_lt_succ (HB.dividerPosition i).isLt)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
    { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
      terminalStage := terminalStageK, nested := nestedK, strict := strictK,
      dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
      dividerIncreasing := increasingK, dividerStage := dividerStageK,
      coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  HB.stage ≍
      { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
          terminalStage := terminalStageK, nested := nestedK, strict := strictK,
          dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
          dividerIncreasing := increasingK, dividerStage := dividerStageK,
          coreInsideFirst := coreInsideK :
          TashkinovHierarchy corr.replacementETT bs }.stage →
  HB.dividerPosition ≍
      { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
          terminalStage := terminalStageK, nested := nestedK, strict := strictK,
          dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
          dividerIncreasing := increasingK, dividerStage := dividerStageK,
          coreInsideFirst := coreInsideK :
          TashkinovHierarchy corr.replacementETT bs }.dividerPosition →
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
      HierarchyStarredStage KF j = HierarchyStarredStage HB j) →
  corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H n Tn mu hp hlenT B r f S
      hSBlen sigma positiveB aboveB strictB belowB generatingB baseB HB EB corr hmaximum bs hcore
      hpe hclosure baseStageK terminalStageK nestedK strictK coreInsideK positiveK increasingK
      dividerStageK KF hstage hposition starredEq
  rcases corr with ⟨ri, rs, re, hr, hp, hc, hl, hstored, he, hk, hpr, ho, hst⟩
  rcases re with ⟨rounds, positive, data, above, strict, below, generating⟩
  cases hr
  have hs : data = rs := eq_of_heq hp
  cases hs
  let j : Fin EB.rounds := ⟨EB.rounds - 1, by have := EB.roundsPositive; omega⟩
  have hj : j.succ = Fin.last EB.rounds := Fin.ext (by
    dsimp [j]; have := EB.roundsPositive; omega)
  change rs.data.tree (Fin.last EB.rounds).castSucc =
    EB.series.data.tree (Fin.last EB.rounds).castSucc
  rw [← hj]
  exact hl j

theorem helper_firstEq_1174.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) ↦ by omega)
      (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) ↦ by omega);
  B.length = T.length - (1 : ℕ) →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) < T.length) ↦ by omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds, by omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (_ :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  (∀ (j : Fin (B.length + (1 : ℕ))),
      (↑j : ℕ) < B.length →
        MissingColors G sigma (B.vertex j) = MissingColors G mu (B.vertex j)) →
  (∀ (psi : PartialEdgeColoring E k) (c : Fin k) (j : Fin (B.length + (1 : ℕ))),
      c ∈ MissingColors G psi (B.vertex j) →
        (↑(HierarchyFirstMissingPosition psi B c) : ℕ) ≤ (↑j : ℕ)) →
  (∀ (psi : PartialEdgeColoring E k) (c : Fin k),
      (↑(HierarchyFirstMissingPosition psi B c) : ℕ) < B.length →
        c ∈ MissingColors G psi (B.vertex (HierarchyFirstMissingPosition psi B c))) →
  ∀ (c : Fin k),
  HierarchyFirstMissingPosition sigma B c = HierarchyFirstMissingPosition mu B c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu hlenT B hBlength r f S hSBlen
      sigma positiveB aboveB strictB belowB generatingB baseB HB earlyMissing firstLe firstMem c
  apply Fin.ext
  apply Nat.le_antisymm
  · by_contra hn
    have hlt : (HierarchyFirstMissingPosition mu B c).val < B.length := by
      have := (HierarchyFirstMissingPosition sigma B c).isLt
      omega
    have hm := firstMem mu c hlt
    rw [← earlyMissing _ hlt] at hm
    have := firstLe sigma c _ hm
    omega
  · by_contra hn
    have hlt : (HierarchyFirstMissingPosition sigma B c).val < B.length := by
      have := (HierarchyFirstMissingPosition mu B c).isLt
      omega
    have hm := firstMem sigma c hlt
    rw [earlyMissing _ hlt] at hm
    have := firstLe mu c _ hm
    omega

theorem helper_hpUpper_1652.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C),
  HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C →
  ∀ (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A →
  HierarchyPathNumber H = HierarchyPathNumber C.hierarchy →
  HierarchyPathNumber H < T.length - A.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx hpathUpper P old H A hAold hp
  rw [hp]
  have hh := hpathUpper
  unfold HierarchyFullTailLength at hh
  dsimp only at hh
  rw [hAold] at hh
  exact hh

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_trans_1665.{u_1, u_2} :
    SharedFacts.SubcaseThreeOnePreparation1.initialSegmentTransitiveStatement.{u_1, u_2} :=
  SharedFacts.SubcaseThreeOnePreparation1.initialSegmentTransitive.{u_1, u_2}

theorem helper_hTnCore_1684.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  TreeSequenceInitialSegment Tn P.replacementBase.core := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P n Tn
  by_cases hpe : P.corresponding.replacementETT.series.data.kind n =
      some TashkinovExtensionKind.PE
  · exact (P.replacementBase.parallel hpe).2.2.some.leftSegment
  · rw [P.replacementBase.nonparallel hpe]
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩

theorem helper_common_1702.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E),
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S W →
  TreeSequenceInitialSegment U W →
  S.length ≤ U.length →
  TreeSequenceInitialSegment S U := by
  classical
  intro V E G e0 trans S U W hSW hUW hlen
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    exact (hUW.2.1 (Fin.castLE (Nat.succ_le_succ hlen) i)).symm.trans (hSW.2.1 i)
  · intro i
    exact (hUW.2.2 (Fin.castLE hlen i)).symm.trans (hSW.2.2 i)

theorem helper_hfull_1715.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A →
  (2 : ℕ) ≤ T.length - A.length →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  HierarchyFullTailPrefix C (HierarchyFullTailLength C - (1 : ℕ)) = B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P old H A hAold htail hlenT B
  have hnum : min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length +
      (HierarchyFullTailLength C - 1)) T.length = T.length - 1 := by
    unfold HierarchyFullTailLength
    dsimp only
    rw [hAold]
    omega
  simp only [HierarchyFullTailPrefix, hnum]
  rfl

theorem helper_hsource_1746.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  B.length = T.length - (1 : ℕ) →
  X.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment Tn X →
  ∃ (S : TreeSequence G e0),
  S.length ≤ B.length ∧ TashkinovAugmentationSequence mu S T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P n Tn mu hlenT B X hBlength hXlength hTnX
  rcases P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu
    P.corresponding.replacementETT with ⟨hpe, hseq⟩ |
      ⟨hkind, edge, seed, hedges, hseed, hincident, hcontrol, hseq⟩
  · exact ⟨Tn, by have := hTnX.1; omega, hseq⟩
  · have hseedLen : seed.length = Tn.length + 1 := hseed.1
    exact ⟨seed, by have := hTnX.1; omega, hseq⟩

theorem helper_hzy_1763.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  Incident G y f →
  ∀ (beta : Fin k),
  mu f = some beta →
  ∀ z ∈ TreeSequenceVertexSet B,
  beta ∈ MissingColors G mu z →
  z ≠ y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P mu hlenT B r f y hyf beta hbetaF z hzB
      hbetaz he
  subst z
  have hnot : beta ∉ MissingColors G mu y := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun h => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hyf, hbetaF⟩)
  exact hnot hbetaz

theorem helper_hzX_1770.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (_ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  B.length = T.length - (1 : ℕ) →
  X.length = T.length - (2 : ℕ) →
  let y : V := B.vertex (Fin.last B.length);
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  ∀ z ∈ TreeSequenceVertexSet B,
  z ≠ y →
  z ∈ TreeSequenceVertexSet X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P trans hlenT B X hBlength hXlength y S
      hSBlen z hzB hzy
  obtain ⟨j, hj⟩ : ∃ j, B.vertex j = z := by simpa [TreeSequenceVertexSet] using hzB
  have hjlt : j.val < B.length := by
    by_contra hh
    have he : j = Fin.last B.length := Fin.ext
        (by simpa using Nat.le_antisymm (Nat.le_of_lt_succ j.isLt) (Nat.le_of_not_gt hh))
    exact hzy (hj.symm.trans (congrArg B.vertex he))
  let jX : Fin (X.length + 1) := ⟨j.val, by omega⟩
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨jX, hj⟩

theorem helper_hfe0_1788.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (_ : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  ∀ (beta : Fin k),
  alpha ≠ beta →
  f ≠ e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha trans hlenT B r f S hSBlen beta hab he
  have hh := T.edge_injective (he.trans T.first_edge.symm)
  have hv := congrArg Fin.val hh
  dsimp [r] at hv
  omega

theorem helper_hsone_1794.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), e ≠ f → sigma e = mu e) →
  f ≠ e0 →
  IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu hlenT r f sigma fixed hfe0
  refine ⟨?_, ?_⟩
  · rw [fixed e0 hfe0.symm]
    exact P.minimumContext.oneEdgeUncolored.1
  · intro e he
    by_cases hef : e = f
    · subst e; exact ⟨alpha, by simp [sigma]⟩
    · rw [fixed e hef]
      exact P.minimumContext.oneEdgeUncolored.2 e he

theorem helper_missingFixed_1810.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), TreeIncidentEdge X e → sigma e = mu e) →
  ∀ v ∈ TreeSequenceVertexSet X,
  MissingColors G sigma v = MissingColors G mu v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu trans hlenT X r f sigma
      incidentFixed v hv
  unfold MissingColors PresentColors
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨e, hi, hc⟩
  · exact ⟨e, hi, (incidentFixed e ⟨v, hv, hi⟩).symm.trans hc⟩
  · exact ⟨e, hi, (incidentFixed e ⟨v, hv, hi⟩).trans hc⟩

theorem helper_fixedB_2088.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  B.length = T.length - (1 : ℕ) →
  TreeSequenceInitialSegment B T →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0),
  S.length ≤ B.length →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), e ≠ f → sigma e = mu e) →
  ∀ (t : Fin B.length),
  sigma (B.edge t) = mu (B.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu trans hlenT B hBlength hBT r f S
      hSBlen sigma fixed t
  apply fixed
  intro he
  have hh := T.edge_injective ((hBT.2.2 t).trans he)
  have hh := congrArg Fin.val hh
  have ht := t.isLt
  change t.val = T.length - 1 at hh
  omega

theorem helper_stable_2096.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  TreeSequenceInitialSegment Tn X →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), TreeIncidentEdge X e → sigma e = mu e) →
  (∀ v ∈ TreeSequenceVertexSet X, MissingColors G sigma v = MissingColors G mu v) →
  StableColoring Tn (TashkinovStoredColors P.corresponding.replacementETT.series.data n)
    (P.corresponding.replacementETT.series.data.coloring n) sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha n Tn mu hlenT X hTnX r f sigma
      incidentFixed missingFixed
  rw [← P.corresponding.replacementETT.generatingColoring]
  refine ⟨?_, ?_⟩
  · intro e he _
    obtain ⟨v, hv, hi⟩ := he
    exact incidentFixed e ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnX hv, hi⟩
  · intro v hv
    exact missingFixed v (TreeSequenceInitialSegmentVertexSetSubset hTnX hv)

theorem helper_boundaryEq_2121.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  let w : V := T.vertex (Fin.last T.length);
  G.ends f = s(y, w) →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), TreeIncidentEdge X e → sigma e = mu e) →
  ∀ (U : TreeSequence G e0),
  TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X →
  ∀ (c : Fin k),
  BoundaryColorEdges G sigma (TreeSequenceVertexSet U) c =
    BoundaryColorEdges G mu (TreeSequenceVertexSet U) c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu hlenT B X r f y w hends sigma
      incidentFixed U hUX c
  apply Finset.filter_congr
  intro edge he
  obtain ⟨u, hu, v, hv, hends⟩ := by simpa [BoundaryEdges] using he
  have hi : TreeIncidentEdge X edge :=
    ⟨u, hUX hu, by rw [Incident, hends]; exact Sym2.mem_mk_left _ _⟩
  rw [incidentFixed edge hi]

theorem helper_lastPositive_2137.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  ∀ (S : TreeSequence G e0) (_ : S.length ≤ B.length),
  H.dividerCount ≠ (0 : ℕ) →
  A =
    H.stage
      (⟨H.dividerCount, by
          have := TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P old H A hlenT B S hSBlen hq
  unfold A HierarchyStarredStage
  obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
  · exact (hq (by simpa using congrArg Fin.val hz)).elim
  · rw [hi]
    simp only [Fin.cases_succ]
    congr 1
    exact Fin.ext (by simpa using (congrArg Fin.val hi).symm)

theorem helper_ordinaryA_2146.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  (∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))),
      (↑i : ℕ) ≤ j →
        TreeSequenceInitialSegment (H.stage i)
          (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
  TreeSequenceInitialSegment Tn A →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  ∀ (S : TreeSequence G e0) (_ : S.length ≤ B.length),
  (H.dividerCount ≠ (0 : ℕ) →
      A =
        H.stage
          (⟨H.dividerCount,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin (H.dividerCount + (2 : ℕ)))) →
  ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
  TreeSequenceInitialSegment (H.stage j.castSucc) A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P old H A n Tn chain hTnA hlenT B S hSBlen
      lastPositive j
  by_cases hq : H.dividerCount = 0
  · have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst j
    simpa only [Fin.castSucc_zero, H.baseStage] using hTnA
  · rw [lastPositive hq]
    exact chain H.dividerCount (by omega) j.castSucc
      (by change j.val ≤ H.dividerCount; have := j.isLt; omega)

theorem helper_closureBX_2180.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                by
                have := TreeSequence.positive T
                omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  TreeSequenceVertexSet baseB.core ⊆ TreeSequenceVertexSet X →
  EB.series.data.kind (Fin.last EB.rounds) = some TashkinovExtensionKind.PE →
  TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P mu hlenT B X positiveB aboveB strictB
      belowB generatingB baseB EB coreBX hpe
  obtain ⟨union⟩ := (baseB.parallel hpe).2.2
  intro v hv
  apply coreBX
  rw [union.vertexSet]
  exact Finset.mem_union_right _ hv

theorem helper_stageMissingEq_2235.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  TreeSequenceInitialSegment Tn X →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (U : TreeSequence G e0),
      TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X →
        TreeMissingColors sigma U = TreeMissingColors mu U) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                by
                have := TreeSequence.positive T
                omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
    (bs : HierarchyBase corr.replacementETT sigma)
    (baseStageK :
      HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc)
    (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
    (nestedK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
    (strictK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        (HB.stage j.castSucc).length < (HB.stage j.succ).length)
    (coreInsideK :
      TreeSequenceInitialSegment bs.core
        (HB.stage
          (⟨(1 : ℕ), by
              have := TreeSequence.positive T
              have := TreeSequence.positive B
              omega⟩ :
            Fin (HB.dividerCount + (2 : ℕ)))))
    (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
    (increasingK :
      ∀ (i j : Fin HB.dividerCount),
        (↑i : ℕ) < (↑j : ℕ) →
          (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
    (dividerStageK :
      ∀ (i : Fin HB.dividerCount),
        HB.stage
            (⟨(↑i : ℕ) + (1 : ℕ),
                by
                have := TreeSequence.positive T
                have := TreeSequence.positive B
                omega⟩ :
              Fin (HB.dividerCount + (2 : ℕ))) =
          TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
            (by
              have := TreeSequence.positive T
              have := TreeSequence.positive B
              omega)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
    { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
      terminalStage := terminalStageK, nested := nestedK, strict := strictK,
      dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
      dividerIncreasing := increasingK, dividerStage := dividerStageK,
      coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
      TreeSequenceInitialSegment (HB.stage j.castSucc) X) →
  corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
      Tn →
  ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
  HierarchyStageMissingColors KF j = HierarchyStageMissingColors HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha n Tn mu hlenT B X hTnX r f sigma
      missingTree positiveB aboveB strictB belowB generatingB baseB HB EB corr bs baseStageK
      terminalStageK nestedK strictK coreInsideK positiveK increasingK dividerStageK KF stageBX
      terminalTree j
  refine Fin.cases ?_ (fun i => ?_) j
  · change TreeMissingColors sigma
      (corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc) =
        TreeMissingColors mu Tn
    rw [terminalTree]
    exact missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnX)
  · exact missingTree _ (TreeSequenceInitialSegmentVertexSetSubset (stageBX i.succ))

theorem helper_earlyMissing_2244.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  B.length = T.length - (1 : ℕ) →
  X.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment X B →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  ∀ (S : TreeSequence G e0) (_ : S.length ≤ B.length) (beta : Fin k),
  alpha ≠ beta →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ v ∈ TreeSequenceVertexSet X, MissingColors G sigma v = MissingColors G mu v) →
  (H.dividerCount ≠ (0 : ℕ) →
      A =
        H.stage
          (⟨H.dividerCount,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin (H.dividerCount + (2 : ℕ)))) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                by
                have := TreeSequence.positive T
                omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (_ :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB)
    (j : Fin (B.length + (1 : ℕ))),
  (↑j : ℕ) < B.length →
  MissingColors G sigma (B.vertex j) = MissingColors G mu (B.vertex j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H A mu hlenT B X hBlength
      hXlength hXB r f S hSBlen beta hab sigma missingFixed lastPositive positiveB aboveB strictB
      belowB generatingB baseB HB j hj
  let i : Fin (X.length + 1) := ⟨j.val, by omega⟩
  have he : Fin.castLE (Nat.succ_le_succ hXB.1) i = j := Fin.ext rfl
  apply missingFixed
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, by rw [← he, hXB.2.1 i]⟩

theorem helper_segmentEq_2283.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                by
                have := TreeSequence.positive T
                omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
    (bs : HierarchyBase corr.replacementETT sigma)
    (baseStageK :
      HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc)
    (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
    (nestedK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
    (strictK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        (HB.stage j.castSucc).length < (HB.stage j.succ).length)
    (coreInsideK :
      TreeSequenceInitialSegment bs.core
        (HB.stage
          (⟨(1 : ℕ), by
              have := TreeSequence.positive T
              have := TreeSequence.positive B
              omega⟩ :
            Fin (HB.dividerCount + (2 : ℕ)))))
    (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
    (increasingK :
      ∀ (i j : Fin HB.dividerCount),
        (↑i : ℕ) < (↑j : ℕ) →
          (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
    (dividerStageK :
      ∀ (i : Fin HB.dividerCount),
        HB.stage
            (⟨(↑i : ℕ) + (1 : ℕ),
                by
                have := TreeSequence.positive T
                have := TreeSequence.positive B
                omega⟩ :
              Fin (HB.dividerCount + (2 : ℕ))) =
          TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
            (by
              have := TreeSequence.positive T
              have := TreeSequence.positive B
              omega)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
    { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
      terminalStage := terminalStageK, nested := nestedK, strict := strictK,
      dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
      dividerIncreasing := increasingK, dividerStage := dividerStageK,
      coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
      HierarchyStarredStage KF j = HierarchyStarredStage HB j) →
  (∀ (c : Fin k),
      HierarchyFirstMissingPosition sigma B c = HierarchyFirstMissingPosition mu B c) →
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))) (t : Fin (HB.stage j.succ).length),
      sigma ((HB.stage j.succ).edge t) = mu ((HB.stage j.succ).edge t)) →
  ∀ (j : Fin (HB.dividerCount + (1 : ℕ))) (c : Fin k),
  HierarchySegmentColors KF j c = HierarchySegmentColors HB j c := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu trans hlenT B r f sigma
      positiveB aboveB strictB belowB generatingB baseB HB EB corr bs baseStageK terminalStageK
      nestedK strictK coreInsideK positiveK increasingK dividerStageK KF starredEq firstEq
      stageFixed j c
  unfold HierarchySegmentColors
  dsimp only
  rw [starredEq j, firstEq c]
  apply Finset.filter_congr
  intro d _
  constructor <;> rintro ⟨r, hlo, hhi, hcol⟩
  · exact ⟨r, hlo, hhi, (stageFixed j r).symm.trans hcol⟩
  · exact ⟨r, hlo, hhi, (stageFixed j r).trans hcol⟩

theorem helper_branch_2341.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let n : Fin (P.corresponding.replacementETT.rounds + (1 : ℕ)) :=
    Fin.last P.corresponding.replacementETT.rounds;
  let Tn : TreeSequence G e0 :=
    P.corresponding.replacementETT.series.data.tree n.castSucc;
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  TreeSequenceInitialSegment Tn X →
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (U : TreeSequence G e0),
      TreeSequenceVertexSet U ⊆ TreeSequenceVertexSet X →
        TreeMissingColors sigma U = TreeMissingColors mu U) →
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                by
                have := TreeSequence.positive T
                omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB)
    (goodB : GoodHierarchy HB),
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  (EB.series.data.kind (Fin.last EB.rounds) = some TashkinovExtensionKind.PE →
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet X) →
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
    (bs : HierarchyBase corr.replacementETT sigma)
    (baseStageK :
      HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc)
    (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
    (nestedK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
    (strictK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        (HB.stage j.castSucc).length < (HB.stage j.succ).length)
    (coreInsideK :
      TreeSequenceInitialSegment bs.core
        (HB.stage
          (⟨(1 : ℕ), by
              have := TreeSequence.positive T
              have := TreeSequence.positive B
              omega⟩ :
            Fin (HB.dividerCount + (2 : ℕ)))))
    (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
    (increasingK :
      ∀ (i j : Fin HB.dividerCount),
        (↑i : ℕ) < (↑j : ℕ) →
          (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
    (dividerStageK :
      ∀ (i : Fin HB.dividerCount),
        HB.stage
            (⟨(↑i : ℕ) + (1 : ℕ),
                by
                have := TreeSequence.positive T
                have := TreeSequence.positive B
                omega⟩ :
              Fin (HB.dividerCount + (2 : ℕ))) =
          TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
            (by
              have := TreeSequence.positive T
              have := TreeSequence.positive B
              omega)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
    { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
      terminalStage := terminalStageK, nested := nestedK, strict := strictK,
      dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
      dividerIncreasing := increasingK, dividerStage := dividerStageK,
      coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
      Tn →
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
      HierarchyStoredColorsAt KF j = HierarchyStoredColorsAt HB j) →
  { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
            series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
            strictAbovePenultimate := strictB, belowFinal := belowB,
            generatingColoring := generatingB :
            ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
              mu }.series.data.kind
        (Fin.last
          { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
              series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
              strictAbovePenultimate := strictB, belowFinal := belowB,
              generatingColoring := generatingB :
              ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                mu }.rounds) =
      some TashkinovExtensionKind.PE →
  bs.closure = baseB.closure →
  (4 : ℕ) ≤
      ((TreeMissingColors mu
                ({ rounds := P.corresponding.replacementETT.rounds,
                      roundsPositive := positiveB,
                      series := P.corresponding.replacementETT.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := generatingB :
                      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                        mu }.series.data.tree
                  (Fin.last
                      { rounds := P.corresponding.replacementETT.rounds,
                          roundsPositive := positiveB,
                          series := P.corresponding.replacementETT.series,
                          abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                          belowFinal := belowB, generatingColoring := generatingB :
                          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B
                            mu }.rounds).castSucc) ∩
              TreeMissingColors mu baseB.closure :
            Finset (Fin k)) \
          (HierarchyStoredColorsAt HB (0 : Fin (HB.dividerCount + (1 : ℕ)))).biUnion
            (goodB.gamma (0 : Fin (HB.dividerCount + (1 : ℕ))))).card →
  (4 : ℕ) ≤
    ((TreeMissingColors sigma
              (corr.replacementETT.series.data.tree
                (Fin.last corr.replacementETT.rounds).castSucc) ∩
            TreeMissingColors sigma bs.closure :
          Finset (Fin k)) \
        (HierarchyStoredColorsAt KF (0 : Fin (KF.dividerCount + (1 : ℕ)))).biUnion
          (goodB.gamma (0 : Fin (KF.dividerCount + (1 : ℕ))))).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha n Tn mu hlenT B X hTnX r f sigma
      missingTree positiveB aboveB strictB belowB generatingB baseB HB goodB EB closureBX corr bs
      baseStageK terminalStageK nestedK strictK coreInsideK positiveK increasingK dividerStageK
      KF terminalTree storedEq hpB hcl hcard
  change 4 ≤ ((TreeMissingColors sigma
    (corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc) ∩
    TreeMissingColors sigma bs.closure) \
      (HierarchyStoredColorsAt KF 0).biUnion (goodB.gamma 0)).card
  rw [terminalTree, hcl, storedEq 0,
    missingTree Tn (TreeSequenceInitialSegmentVertexSetSubset hTnX),
    missingTree baseB.closure (closureBX hpB)]
  exact hcard

theorem helper_hbetaY_2355.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let mu : PartialEdgeColoring E k := P.coloring;
  HierarchyPathNumber H = HierarchyPathNumber C.hierarchy →
  (∀ {X Y Z : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
        TreeSequenceInitialSegment Y Z → TreeSequenceInitialSegment X Z) →
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  Incident G y f →
  ∀ (beta : Fin k),
  mu f = some beta →
  alpha ≠ beta →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ (e : E), e ≠ f → sigma e = mu e) →
  beta ∈ MissingColors G sigma y := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H mu hp trans hlenT B r f y hyf
      beta hbetaF hab sigma fixed
  simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
  intro hp
  obtain ⟨edge, hi, hc⟩ := (Finset.mem_filter.mp hp).2
  by_cases hef : edge = f
  · subst edge
    have he : alpha = beta := by simpa [sigma] using hc
    exact hab he
  · have hcOld : mu edge = some beta := (fixed edge hef).symm.trans hc
    exact P.minimumContext.proper hef ⟨y, hi, hyf⟩ hcOld hbetaF

theorem helper_hnotElementary_2365.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let X : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (2 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let y : V := B.vertex (Fin.last B.length);
  ∀ (beta : Fin k),
  ∀ z ∈ TreeSequenceVertexSet B,
  beta ∈ MissingColors G mu z →
  z ≠ y →
  z ∈ TreeSequenceVertexSet X →
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  (∀ v ∈ TreeSequenceVertexSet X, MissingColors G sigma v = MissingColors G mu v) →
  beta ∈ MissingColors G sigma y →
  ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu hlenT B X r f y beta z hzB
      hbetaz hzy hzX sigma missingFixed hbetaY he
  have hbetazS : beta ∈ MissingColors G sigma z := by rw [missingFixed z hzX]; exact hbetaz
  have hyB : y ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, rfl⟩
  exact Finset.disjoint_left.mp (he hzB hyB hzy) hbetazS hbetaY

theorem helper_lastStar_2378.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (alpha : Fin k),
  let old : HierarchyCounterexample P.replacementBase := P.counterexample;
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    old.hierarchy;
  let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (hlenT : (3 : ℕ) ≤ T.length),
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - (1 : ℕ))
      (by
        have := TreeSequence.positive T
        omega)
      (by
        have := TreeSequence.positive T
        omega);
  let r : Fin T.length :=
    (⟨T.length - (1 : ℕ),
        by
        have := TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let f : E := T.edge r;
  let sigma : PartialEdgeColoring E k := fun (e : E) ↦ if e = f then some alpha else mu e;
  ∀ (positiveB : (1 : ℕ) ≤ P.corresponding.replacementETT.rounds)
    (aboveB :
      TreeSequenceInitialSegment
        (P.corresponding.replacementETT.series.data.tree
          (⟨P.corresponding.replacementETT.rounds,
              by
              have := TreeSequence.positive T
              omega⟩ :
            Fin (P.corresponding.replacementETT.rounds + (2 : ℕ))))
        B)
    (strictB :
      (P.corresponding.replacementETT.series.data.tree
            (⟨P.corresponding.replacementETT.rounds,
                by
                have := TreeSequence.positive T
                omega⟩ :
              Fin (P.corresponding.replacementETT.rounds + (2 : ℕ)))).length <
        B.length)
    (belowB :
      TreeSequenceInitialSegment B
        (P.corresponding.replacementETT.series.data.tree
          (Fin.last (P.corresponding.replacementETT.rounds + (1 : ℕ)))))
    (generatingB :
      mu =
        P.corresponding.replacementETT.series.data.coloring
          (Fin.last P.corresponding.replacementETT.rounds))
    (baseB :
      HierarchyBase
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        mu)
    (HB :
      TashkinovHierarchy
        { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
          series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
          strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := generatingB :
          ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu }
        baseB)
    (hcountB : HB.dividerCount = H.dividerCount),
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
      HB.stage j.castSucc =
          H.stage
            (Fin.cast
                (by
                  have := TreeSequence.positive T
                  have := TreeSequence.positive B
                  omega)
                j).castSucc ∧
        HierarchyStarredStage HB j =
          HierarchyStarredStage H
            (Fin.cast
              (by
                have := TreeSequence.positive T
                have := TreeSequence.positive B
                omega)
              j)) →
  let EB : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu :=
    { rounds := P.corresponding.replacementETT.rounds, roundsPositive := positiveB,
      series := P.corresponding.replacementETT.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := generatingB :
      ExtendedTashkinovTree G k e0 P.corresponding.replacementInput B mu };
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 EB sigma B)
    (bs : HierarchyBase corr.replacementETT sigma)
    (baseStageK :
      HB.stage (0 : Fin (HB.dividerCount + (2 : ℕ))) =
        corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc)
    (terminalStageK : HB.stage (Fin.last (HB.dividerCount + (1 : ℕ))) = B)
    (nestedK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (HB.stage j.castSucc) (HB.stage j.succ))
    (strictK :
      ∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
        (HB.stage j.castSucc).length < (HB.stage j.succ).length)
    (coreInsideK :
      TreeSequenceInitialSegment bs.core
        (HB.stage
          (⟨(1 : ℕ), by
              have := TreeSequence.positive T
              have := TreeSequence.positive B
              omega⟩ :
            Fin (HB.dividerCount + (2 : ℕ)))))
    (positiveK : ∀ (i : Fin HB.dividerCount), (1 : ℕ) ≤ (↑(HB.dividerPosition i) : ℕ))
    (increasingK :
      ∀ (i j : Fin HB.dividerCount),
        (↑i : ℕ) < (↑j : ℕ) →
          (↑(HB.dividerPosition i) : ℕ) < (↑(HB.dividerPosition j) : ℕ))
    (dividerStageK :
      ∀ (i : Fin HB.dividerCount),
        HB.stage
            (⟨(↑i : ℕ) + (1 : ℕ),
                by
                have := TreeSequence.positive T
                have := TreeSequence.positive B
                omega⟩ :
              Fin (HB.dividerCount + (2 : ℕ))) =
          TreeSequencePrefix B (↑(HB.dividerPosition i) : ℕ) (positiveK i)
            (by
              have := TreeSequence.positive T
              have := TreeSequence.positive B
              omega)),
  let KF : TashkinovHierarchy corr.replacementETT bs :=
    { dividerCount := HB.dividerCount, stage := HB.stage, baseStage := baseStageK,
      terminalStage := terminalStageK, nested := nestedK, strict := strictK,
      dividerPosition := HB.dividerPosition, dividerPositive := positiveK,
      dividerIncreasing := increasingK, dividerStage := dividerStageK,
      coreInsideFirst := coreInsideK : TashkinovHierarchy corr.replacementETT bs };
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
      HierarchyStarredStage KF j = HierarchyStarredStage HB j) →
  HierarchyStarredStage KF (Fin.last KF.dividerCount) = A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H A mu hlenT B r f sigma
      positiveB aboveB strictB belowB generatingB baseB HB hcountB hstagesB EB corr bs baseStageK
      terminalStageK nestedK strictK coreInsideK positiveK increasingK dividerStageK KF starredEq
  rw [starredEq]
  have hh := (hstagesB (Fin.last HB.dividerCount)).2
  have hi : Fin.cast (congrArg (fun q => q + 1) hcountB)
      (Fin.last HB.dividerCount) = Fin.last H.dividerCount :=
    Fin.ext hcountB
  simpa only [hi] using hh

theorem helper_lastOrdinary_2387.{u_1, u_2} :
    helperLastOrdinary2387Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P old H mu hlenT B positiveB aboveB strictB
      belowB generatingB baseB HB hcountB hstagesB
  have hh := (hstagesB (Fin.last HB.dividerCount)).1
  have hi : Fin.cast (congrArg (fun q => q + 1) hcountB)
      (Fin.last HB.dividerCount) = Fin.last H.dividerCount :=
    Fin.ext hcountB
  simpa only [hi] using hh

alias helper_uniqueRefresh_4523 :=
  SharedFacts.ShorteningProofs.uniqueRefreshTransport

theorem helper_parallelBase_4547.{u_1, u_2} :
    helperParallelBase4547Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha old H n Tn mu hp hlenT B X hTnX r f
      sigma missingTree minusEq positiveB aboveB strictB belowB generatingB baseB HB goodB EB
      coreBX closureBX corr bs hcore hpe hclosure baseStageK terminalStageK nestedK strictK
      coreInsideK positiveK increasingK dividerStageK KF terminalTree storedEq
  dsimp only
  intro hp
  have hpB := hpe.mpr hp
  have hcl : bs.closure = baseB.closure := (hclosure hpB).symm
  obtain ⟨hnot, hcard⟩ := goodB.parallelBase hpB
  constructor
  · change ¬ TreeColorSetMinusClosed G sigma bs.core
      ((HierarchyStoredColorsAt KF 0).biUnion (goodB.gamma 0))
    rw [← hcore, storedEq 0, minusEq baseB.core coreBX]
    exact hnot
  · exact helper_branch_2341 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
      (@alpha) (@hlenT) (@hTnX) (@missingTree) (@positiveB) (@aboveB) (@strictB) (@belowB)
      (@generatingB) (@baseB) (@HB) (@goodB) (@closureBX) (@corr) (@bs) (@baseStageK)
      (@terminalStageK) (@nestedK) (@strictK) (@coreInsideK) (@positiveK) (@increasingK)
      (@dividerStageK) (@terminalTree) (@storedEq) (@hpB) (@hcl) (@hcard)

end EligibleIndexBound

end GoldbergSeymour

end
