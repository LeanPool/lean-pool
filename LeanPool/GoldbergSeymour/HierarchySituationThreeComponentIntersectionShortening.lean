/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.SharedFacts.ShorteningTransport

public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.HierarchyNonparallelFirstEdge
public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.TerminalRoute
public import LeanPool.GoldbergSeymour.ElementaryTerminalComponent
public import LeanPool.GoldbergSeymour.TashkinovSeriesNonParallelClosed

/-!
# Hierarchy Situation Three Component Intersection Shortening

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev componentIntersectionFromMissingColorsStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
  let H := P.counterexample.hierarchy;
  let R := P.corresponding.replacementETT;
  let mu := P.coloring;
  let n := Fin.last R.rounds;
  let Tn := R.series.data.tree n.castSucc;
  let q := Fin.last H.dividerCount;
  let A := HierarchyStarredStage H q;
  ∀ (j : ℕ),
  (
  let j := j;
  let X := HierarchyFullTailPrefix C (j - 1);
  ∃ u ∈ TreeSequenceVertexSet X,
   Sum.inl u ∈
    TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))) →
  HierarchyPathNumber C.hierarchy = j →
  2 ≤ j →
  j < HierarchyFullTailLength C →
  let ell := HierarchyFullTailLength C;
  let B := HierarchyFullTailPrefix C (j - 2);
  let X := HierarchyFullTailPrefix C (j - 1);
  let y := T.vertex (Fin.last T.length);
  (
  ∀ (S : TreeSequence G e0),
  TreeSequenceInitialSegment S S) →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeSequenceInitialSegment U W →
  TreeSequenceInitialSegment S W) →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S W →
  TreeSequenceInitialSegment U W →
  S.length ≤ U.length →
  TreeSequenceInitialSegment S U) →
  (
  ∀ {a b : ℕ} (s :
  Fin (a + 2) →
  TreeSequence G e0) (t :
  Fin (b + 2) →
  TreeSequence G e0)
      (u v : TreeSequence G e0),
  a = b →
  s ≍ t →
  u = v →
  Fin.cases (motive := fun _ => TreeSequence G e0) u (fun i ↦ s i.succ.castSucc)
    (Fin.last a) =
   Fin.cases (motive := fun _ => TreeSequence G e0) v (fun i ↦ t i.succ.castSucc)
    (Fin.last b)) →
  HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A →
  HierarchyPathNumber H = j →
  ell = T.length - A.length →
  2 ≤ j →
  j < ell →
  (
  ∀ (b : ℕ) (hb : b < H.dividerCount + 2) (a : Fin (H.dividerCount + 2)),
  ↑a ≤ b →
  TreeSequenceInitialSegment (H.stage a) (H.stage ⟨b, hb⟩)) →
  (
  ∀ (i : Fin (H.dividerCount + 1)),
  TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ)) →
  TreeSequenceInitialSegment A T →
  (
  H.dividerCount = 0 →
  A = P.replacementBase.core) →
  (
  H.dividerCount ≠ 0 →
  A = H.stage ⟨H.dividerCount, Decidable.byContradiction fun a ↦ (by omega)⟩) →
  TreeSequenceInitialSegment P.replacementBase.core A →
  TreeSequenceInitialSegment Tn P.replacementBase.core →
  TreeSequenceInitialSegment Tn A →
  (
  ∀ (r : ℕ),
  TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T) →
  (∀ r ≤ ell, (HierarchyFullTailPrefix C r).length = A.length + r) →
  B.length = A.length + (j - 2) →
  X.length = A.length + (j - 1) →
  TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - 2)) T →
  TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - 1)) T →
  TreeSequenceInitialSegment A B →
  TreeSequenceInitialSegment B X →
  TreeSequenceInitialSegment A X →
  TreeSequenceInitialSegment Tn B →
  TreeSequenceInitialSegment Tn X →
  X.length = B.length + 1 →
  X.length < T.length →
  y ∉ TreeSequenceVertexSet X →
  y ∉ TreeSequenceVertexSet B →
  alpha ∈
    MissingColors G P.coloring
     (T.vertex (Fin.last T.length)) →
  alpha ∈
    TreeMissingColors P.coloring
     (HierarchyFullTailPrefix C (j - 2)) →
  ((alpha ∉
     (HierarchyStoredColorsAt P.counterexample.hierarchy
         (Fin.last
          P.counterexample.hierarchy.dividerCount)).biUnion
       (P.counterexample.good.gamma
        (Fin.last
         P.counterexample.hierarchy.dividerCount)) ∪
      (TreeSequenceVertexSet P.replacementBase.core \
         TreeSequenceVertexSet
          (P.corresponding.replacementETT.series.data.tree
           (Fin.last
             P.corresponding.replacementETT.rounds).castSucc)).biUnion
       fun v ↦ MissingColors G P.coloring v) ∨
    ∃
     eta ∈
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount),
     alpha ∈
       P.counterexample.good.gamma
        (Fin.last P.counterexample.hierarchy.dividerCount)
        eta ∧
      ↑(HierarchyFirstMissingPosition P.coloring T eta) ≤
       (HierarchyFullTailPrefix C (j - 2)).length) →
  beta ≠ alpha →
  beta ∈
    TreeMissingColors P.coloring
     (HierarchyFullTailPrefix C (j - 2)) →
  beta ∉
    (HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last
        P.counterexample.hierarchy.dividerCount)).biUnion
     (P.counterexample.good.gamma
      (Fin.last
       P.counterexample.hierarchy.dividerCount)) →
  beta ∉
    (Finset.univ.filter fun c =>
     ∃ r : Fin T.length,
      (HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last
           P.counterexample.hierarchy.dividerCount)).length ≤
        ↑r ∧
       ↑r <
         (HierarchyStarredStage
            P.counterexample.hierarchy
            (Fin.last
             P.counterexample.hierarchy.dividerCount)).length +
          j ∧
        P.coloring (T.edge r) = some c) →
  beta ∉
     ((TreeSequenceVertexSet P.replacementBase.core \
         TreeSequenceVertexSet
          (P.corresponding.replacementETT.series.data.tree
           (Fin.last
             P.corresponding.replacementETT.rounds).castSucc)).biUnion
       fun v ↦ MissingColors G P.coloring v) ∪
      HierarchyStoredColorsAt
       P.counterexample.hierarchy
       (Fin.last
        P.counterexample.hierarchy.dividerCount) ∨
    beta ∈
      HierarchyStoredColorsAt
       P.counterexample.hierarchy
       (Fin.last
        P.counterexample.hierarchy.dividerCount) ∧
     Disjoint
      (P.counterexample.good.gamma
        (Fin.last
         P.counterexample.hierarchy.dividerCount)
        beta ∪
       { beta })
      (Finset.univ.filter fun c =>
       ∃ r : Fin T.length,
        (HierarchyStarredStage
            P.counterexample.hierarchy
            (Fin.last
             P.counterexample.hierarchy.dividerCount)).length ≤
          ↑r ∧
         ↑r <
           (HierarchyStarredStage
              P.counterexample.hierarchy
              (Fin.last
               P.counterexample.hierarchy.dividerCount)).length +
            j ∧
          P.coloring (T.edge r) = some c) →
  alpha ≠ beta →
  False

private abbrev componentIntersectionFromSpliceFactsStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
  let H := P.counterexample.hierarchy;
  let R := P.corresponding.replacementETT;
  let mu := P.coloring;
  let n := Fin.last R.rounds;
  let Tn := R.series.data.tree n.castSucc;
  let q := Fin.last H.dividerCount;
  let A := HierarchyStarredStage H q;
  ∀ (j : ℕ),
  (
  let j := j;
  let X := HierarchyFullTailPrefix C (j - 1);
  ∃ u ∈ TreeSequenceVertexSet X,
   Sum.inl u ∈
    TwoColorComponent G P.coloring alpha beta (Sum.inl (T.vertex (Fin.last T.length)))) →
  HierarchyPathNumber C.hierarchy = j →
  2 ≤ j →
  j < HierarchyFullTailLength C →
  let ell := HierarchyFullTailLength C;
  let B := HierarchyFullTailPrefix C (j - 2);
  let X := HierarchyFullTailPrefix C (j - 1);
  let y := T.vertex (Fin.last T.length);
  (
  ∀ (S : TreeSequence G e0),
  TreeSequenceInitialSegment S S) →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeSequenceInitialSegment U W →
  TreeSequenceInitialSegment S W) →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S W →
  TreeSequenceInitialSegment U W →
  S.length ≤ U.length →
  TreeSequenceInitialSegment S U) →
  (
  ∀ {a b : ℕ} (s :
  Fin (a + 2) →
  TreeSequence G e0) (t :
  Fin (b + 2) →
  TreeSequence G e0)
      (u v : TreeSequence G e0),
  a = b →
  s ≍ t →
  u = v →
  Fin.cases (motive := fun _ => TreeSequence G e0) u (fun i ↦ s i.succ.castSucc)
    (Fin.last a) =
   Fin.cases (motive := fun _ => TreeSequence G e0) v (fun i ↦ t i.succ.castSucc)
    (Fin.last b)) →
  HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A →
  HierarchyPathNumber H = j →
  ell = T.length - A.length →
  2 ≤ j →
  j < ell →
  (
  ∀ (b : ℕ) (hb : b < H.dividerCount + 2) (a : Fin (H.dividerCount + 2)),
  ↑a ≤ b →
  TreeSequenceInitialSegment (H.stage a) (H.stage ⟨b, hb⟩)) →
  (
  ∀ (i : Fin (H.dividerCount + 1)),
  TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ)) →
  TreeSequenceInitialSegment A T →
  (
  H.dividerCount = 0 →
  A = P.replacementBase.core) →
  (
  H.dividerCount ≠ 0 →
  A = H.stage ⟨H.dividerCount, Decidable.byContradiction fun a ↦ (by omega)⟩) →
  TreeSequenceInitialSegment P.replacementBase.core A →
  TreeSequenceInitialSegment Tn P.replacementBase.core →
  TreeSequenceInitialSegment Tn A →
  (
  ∀ (r : ℕ),
  TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T) →
  (∀ r ≤ ell, (HierarchyFullTailPrefix C r).length = A.length + r) →
  B.length = A.length + (j - 2) →
  X.length = A.length + (j - 1) →
  TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - 2)) T →
  TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - 1)) T →
  TreeSequenceInitialSegment A B →
  TreeSequenceInitialSegment B X →
  TreeSequenceInitialSegment A X →
  TreeSequenceInitialSegment Tn B →
  TreeSequenceInitialSegment Tn X →
  X.length = B.length + 1 →
  X.length < T.length →
  y ∉ TreeSequenceVertexSet X →
  y ∉ TreeSequenceVertexSet B →
  alpha ∈
    MissingColors G P.coloring
     (T.vertex (Fin.last T.length)) →
  alpha ∈
    TreeMissingColors P.coloring
     (HierarchyFullTailPrefix C (j - 2)) →
  ((alpha ∉
     (HierarchyStoredColorsAt P.counterexample.hierarchy
         (Fin.last
          P.counterexample.hierarchy.dividerCount)).biUnion
       (P.counterexample.good.gamma
        (Fin.last
         P.counterexample.hierarchy.dividerCount)) ∪
      (TreeSequenceVertexSet P.replacementBase.core \
         TreeSequenceVertexSet
          (P.corresponding.replacementETT.series.data.tree
           (Fin.last
             P.corresponding.replacementETT.rounds).castSucc)).biUnion
       fun v ↦ MissingColors G P.coloring v) ∨
    ∃
     eta ∈
      HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last P.counterexample.hierarchy.dividerCount),
     alpha ∈
       P.counterexample.good.gamma
        (Fin.last P.counterexample.hierarchy.dividerCount)
        eta ∧
      ↑(HierarchyFirstMissingPosition P.coloring T eta) ≤
       (HierarchyFullTailPrefix C (j - 2)).length) →
  beta ≠ alpha →
  beta ∈
    TreeMissingColors P.coloring
     (HierarchyFullTailPrefix C (j - 2)) →
  beta ∉
    (HierarchyStoredColorsAt P.counterexample.hierarchy
       (Fin.last
        P.counterexample.hierarchy.dividerCount)).biUnion
     (P.counterexample.good.gamma
      (Fin.last
       P.counterexample.hierarchy.dividerCount)) →
  beta ∉
    (Finset.univ.filter fun c =>
     ∃ r : Fin T.length,
      (HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last
           P.counterexample.hierarchy.dividerCount)).length ≤
        ↑r ∧
       ↑r <
         (HierarchyStarredStage
            P.counterexample.hierarchy
            (Fin.last
             P.counterexample.hierarchy.dividerCount)).length +
          j ∧
        P.coloring (T.edge r) = some c) →
  beta ∉
     ((TreeSequenceVertexSet P.replacementBase.core \
         TreeSequenceVertexSet
          (P.corresponding.replacementETT.series.data.tree
           (Fin.last
             P.corresponding.replacementETT.rounds).castSucc)).biUnion
       fun v ↦ MissingColors G P.coloring v) ∪
      HierarchyStoredColorsAt
       P.counterexample.hierarchy
       (Fin.last
        P.counterexample.hierarchy.dividerCount) ∨
    beta ∈
      HierarchyStoredColorsAt
       P.counterexample.hierarchy
       (Fin.last
        P.counterexample.hierarchy.dividerCount) ∧
     Disjoint
      (P.counterexample.good.gamma
        (Fin.last
         P.counterexample.hierarchy.dividerCount)
        beta ∪
       { beta })
      (Finset.univ.filter fun c =>
       ∃ r : Fin T.length,
        (HierarchyStarredStage
            P.counterexample.hierarchy
            (Fin.last
             P.counterexample.hierarchy.dividerCount)).length ≤
          ↑r ∧
         ↑r <
           (HierarchyStarredStage
              P.counterexample.hierarchy
              (Fin.last
               P.counterexample.hierarchy.dividerCount)).length +
            j ∧
          P.coloring (T.edge r) = some c) →
  alpha ≠ beta →
  (
  ∀ {S U : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeMissingColors mu S ⊆
   TreeMissingColors mu U) →
  alpha ∈ TreeMissingColors mu X →
  beta ∈ TreeMissingColors mu X →
  (
  ∀ {S U : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  S.length = U.length →
  S = U) →
  (
  ∀ (W : TreeSequence G e0) (c : Fin k)
   (i : Fin (W.length + 1)),
  c ∈ MissingColors G mu (W.vertex i) →
  ↑(HierarchyFirstMissingPosition mu W c) ≤
   ↑i) →
  (
  ∀ (W : TreeSequence G e0) (c : Fin k),
  ↑(HierarchyFirstMissingPosition mu W c) <
    W.length →
  c ∈
   MissingColors G mu
    (W.vertex
     (HierarchyFirstMissingPosition mu W
      c))) →
  (
  ∀ {W Z : TreeSequence G e0},
  TreeSequenceInitialSegment W Z →
  ∀ c ∈ TreeMissingColors mu W,
   ↑(HierarchyFirstMissingPosition mu Z c) ≤
    W.length) →
  (
  ∀ (W : TreeSequence G e0)
   (D : Finset (Fin k))
   (rho sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G rho →
  IsOneEdgeUncolored rho e0 →
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring W D rho sigma →
  ColoredVertexSetClosed G rho
    (TreeSequenceVertexSet W) →
  ColoredVertexSetClosed G sigma
   (TreeSequenceVertexSet W)) →
  (
  R.series.data.kind n ≠
    some TashkinovExtensionKind.PE →
  ColoredVertexSetClosed G mu
   (TreeSequenceVertexSet Tn)) →
  ModColoring R mu →
  (
  H.dividerCount = 0 →
  j = 2 →
  R.series.data.kind n ≠
    some TashkinovExtensionKind.PE →
  ¬∃ u ∈ TreeSequenceVertexSet B,
    Sum.inl u ∈
     TwoColorComponent G mu alpha beta
      (Sum.inl y)) →
  False

private abbrev helperContinuation2763Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
   P.counterexample.hierarchy;
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
   P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (j : ℕ) (hpathLower : (2 : ℕ) ≤ j),
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  let y : V := T.vertex (Fin.last T.length);
  ∀
   (trans :
  ∀ {S U W : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U)
   (hUW : TreeSequenceInitialSegment U W),
  TreeSequenceInitialSegment S W)
   (hpOld : HierarchyPathNumber H = j) (hjlow : (2 : ℕ) ≤ j)
   (coreA : TreeSequenceInitialSegment P.replacementBase.core A)
   (hBLen : B.length = A.length + (j - (2 : ℕ))) (hXLen : X.length = A.length + (j - (1 : ℕ)))
   (hBT : TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - (2 : ℕ))) T)
   (hBXLen : X.length = B.length + (1 : ℕ)) (hXshort : X.length < T.length)
   (hyB : y ∉ TreeSequenceVertexSet B)
   (hay : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)))
   (haB : alpha ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C (j - (2 : ℕ))))
   (haChoice :
    (alpha ∉
      (HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount)).biUnion
        (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)) ∪
       (TreeSequenceVertexSet P.replacementBase.core \
          TreeSequenceVertexSet
           (P.corresponding.replacementETT.series.data.tree
            (Fin.last P.corresponding.replacementETT.rounds).castSucc)).biUnion
        fun (v : V) ↦ MissingColors G P.coloring v) ∨
     ∃
      eta ∈
       HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount),
      alpha ∈ P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount) eta ∧
       (↑(HierarchyFirstMissingPosition P.coloring T eta) : ℕ) ≤
        (HierarchyFullTailPrefix C (j - (2 : ℕ))).length)
   (hba : beta ≠ alpha)
   (hbGamma :
    beta ∉
     (HierarchyStoredColorsAt P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)).biUnion
      (P.counterexample.good.gamma (Fin.last P.counterexample.hierarchy.dividerCount)))
   (hab : alpha ≠ beta)
   (firstMem :
  ∀ (W : TreeSequence G e0) (c : Fin k)
   (hlt : (↑(HierarchyFirstMissingPosition mu W c) : ℕ) < W.length),
  c ∈ MissingColors G mu (W.vertex (HierarchyFirstMissingPosition mu W c)))
   (firstBound :
  ∀ {W Z : TreeSequence G e0} (hWT : TreeSequenceInitialSegment W Z) (c : Fin k)
   (hc : c ∈ TreeMissingColors mu W),
  (↑(HierarchyFirstMissingPosition mu Z c) : ℕ) ≤ W.length)
   (exceptional :
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  ¬∃ u ∈ TreeSequenceVertexSet B, Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y))
   (S U : TreeSequence G e0) (hBS : TreeSequenceInitialSegment B S)
   (hSU : TreeSequenceInitialSegment S U) (hSUstrict : S.length < U.length)
   (hUlast : U.vertex (Fin.last U.length) = y)
   (hUcolors :
  ∀ (r : Fin U.length),
  S.length ≤ (↑r : ℕ) →
  mu (U.edge r) = some alpha ∨ mu (U.edge r) = some beta)
   (hUpath :
  ∀ (r : Fin U.length),
  X.length ≤ (↑r : ℕ) →
  G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ))
   (hScorner :
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  S = X)
   (hST : TreeSequenceInitialSegment S T) (hAU : TreeSequenceInitialSegment A U)
   (hBU : TreeSequenceInitialSegment B U) (hAUstrict : A.length < U.length)
   (newInput : PartialEdgeColoring E k) (newSeries : TashkinovSeries G k R.rounds e0 newInput)
   (hgen : mu = newSeries.data.coloring (Fin.last R.rounds))
   (htrees :
  ∀ (i : Fin R.rounds),
  newSeries.data.tree i.succ.castSucc = R.series.data.tree i.succ.castSucc)
   (hstored :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  newSeries.data.stored i = R.series.data.stored i)
   (hedges :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  newSeries.data.connectingEdges i = R.series.data.connectingEdges i)
   (hkinds :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  newSeries.data.kind i = R.series.data.kind i)
   (hproper :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  IsProperEdgeColoring G (newSeries.data.coloring i))
   (hone :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  IsOneEdgeUncolored (newSeries.data.coloring i) e0)
   (hstable :
  ∀ (i : Fin R.rounds),
  StableColoring (R.series.data.tree i.succ.castSucc)
   (TashkinovStoredColors R.series.data i.succ) (R.series.data.coloring i.succ)
   (newSeries.data.coloring i.succ))
   (roundsPositive : (1 : ℕ) ≤ R.1)
   (above :
    TreeSequenceInitialSegment (newSeries.data.tree (⟨R.1, by omega⟩ : Fin (R.1 + (2 : ℕ)))) U)
   (strict : (newSeries.data.tree (⟨R.1, by omega⟩ : Fin (R.1 + (2 : ℕ)))).length < U.length)
   (below : TreeSequenceInitialSegment U (newSeries.data.tree (Fin.last (R.1 + (1 : ℕ)))))
   (generating : mu = newSeries.data.coloring (Fin.last R.1))
   (hseries :
    {
     rounds := R.1, roundsPositive := roundsPositive, series := newSeries,
       abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
       generatingColoring := generating : ExtendedTashkinovTree G k e0 newInput U mu }.series ≍
     newSeries),
  let RU : ExtendedTashkinovTree G k e0 newInput U mu :=
   {
    rounds := R.rounds, roundsPositive := roundsPositive, series := newSeries,
    abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
    generatingColoring := generating : ExtendedTashkinovTree G k e0 newInput U mu };
  ∀ (baseU : HierarchyBase RU mu) (hcore : baseU.core = P.replacementBase.core)
   (hclosure : baseU.closure = P.replacementBase.closure) (hMP : MaximumProperty RU)
   (hTnEq : newSeries.data.tree n.castSucc = Tn)
   (hstoredEq : TashkinovStoredColors newSeries.data n = TashkinovStoredColors R.series.data n)
   (stageA :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  TreeSequenceInitialSegment (H.stage i.castSucc) A)
   (stageU :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  TreeSequenceInitialSegment (H.stage i.castSucc) U)
   (stageB :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  TreeSequenceInitialSegment (H.stage i.castSucc) B)
   (hdivB :
  ∀ (i : Fin H.dividerCount),
  (↑(H.dividerPosition i) : ℕ) ≤ B.length)
   (prefixEq :
  ∀ (p : ℕ) (hp : (1 : ℕ) ≤ p) (hpB : p ≤ B.length),
  TreeSequencePrefix U p hp (LE.le.trans hpB hBU.1) =
   TreeSequencePrefix T p hp (LE.le.trans hpB hBT.1)),
  let newStage :
  Fin (H.dividerCount + (2 : ℕ)) →
  TreeSequence G e0 :=
   fun (i : Fin (H.dividerCount + (2 : ℕ))) ↦
   if (↑i : ℕ) = H.dividerCount + (1 : ℕ) then U else H.stage i;
  ∀
   (newStageOld :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  newStage i.castSucc = H.stage i.castSucc)
   (newStageLast : newStage (Fin.last (H.dividerCount + (1 : ℕ))) = U)
   (newStageAt :
  ∀ (i : Fin (H.dividerCount + (2 : ℕ))) (hi : (↑i : ℕ) ≤ H.dividerCount),
  newStage i = H.stage i),
  False

private noncomputable abbrev helperK2280.{u_1, u_2} :
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
  let H :
    TashkinovHierarchy P.corresponding.replacementETT
      P.replacementBase :=
    P.counterexample.hierarchy;
  let R :
    ExtendedTashkinovTree G k e0
      P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
  let q : Fin (H.dividerCount + (1 : ℕ)) :=
    Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  (j : ℕ) →
  let B : TreeSequence G e0 :=
    HierarchyFullTailPrefix C (j - (2 : ℕ));
  (trans :
  ∀ {S U W : TreeSequence G e0}
    (_ : TreeSequenceInitialSegment S U)
    (_ : TreeSequenceInitialSegment U W),
  TreeSequenceInitialSegment S W) →
  (coreA :
      TreeSequenceInitialSegment P.replacementBase.core
        A) →
  (hBT :
      TreeSequenceInitialSegment
        (HierarchyFullTailPrefix C (j - (2 : ℕ))) T) →
  (S U : TreeSequence G e0) →
  (hAU : TreeSequenceInitialSegment A U) →
  (hBU : TreeSequenceInitialSegment B U) →
  (newInput : PartialEdgeColoring E k) →
  (newSeries :
      TashkinovSeries G k R.rounds e0
        newInput) →
  (roundsPositive : (1 : ℕ) ≤ R.rounds) →
  (above :
      TreeSequenceInitialSegment
        (newSeries.data.tree
          (⟨R.rounds, by omega⟩ :
            Fin (R.rounds + (2 : ℕ))))
        U) →
  (strict :
      (newSeries.data.tree
            (⟨R.rounds, by omega⟩ :
              Fin
                (R.rounds +
                  (2 : ℕ)))).length <
        U.length) →
  (below :
      TreeSequenceInitialSegment U
        (newSeries.data.tree
          (Fin.last
            (R.rounds + (1 : ℕ))))) →
  (generating :
      mu =
        newSeries.data.coloring
          (Fin.last R.rounds)) →
  let RU :
    ExtendedTashkinovTree G k e0
      newInput U mu :=
    { rounds := R.rounds,
      roundsPositive :=
        roundsPositive,
      series := newSeries,
      abovePenultimate := above,
      strictAbovePenultimate :=
        strict,
      belowFinal := below,
      generatingColoring :=
        generating :
      ExtendedTashkinovTree G k e0
        newInput U mu };
  (baseU : HierarchyBase RU mu) →
  (hcore :
      baseU.core =
        P.replacementBase.core) →
  (hTnEq :
      newSeries.data.tree
          n.castSucc =
        Tn) →
  (hdivB :
  ∀
    (i :
      Fin
        H.dividerCount),
  (↑(H.dividerPosition
          i) :
      ℕ) ≤
    B.length) →
  (prefixEq :
  ∀ (p : ℕ)
    (hp : (1 : ℕ) ≤ p)
    (hpB :
      p ≤ B.length),
  TreeSequencePrefix
      U p hp
      (LE.le.trans
        hpB hBU.1) =
    TreeSequencePrefix
      T p hp
      (LE.le.trans
        hpB
        hBT.1)) →
  let newStage :
  Fin
      (H.dividerCount +
        (2 : ℕ)) →
  TreeSequence G
    e0 :=
    fun
      (i :
        Fin
          (H.dividerCount +
            (2 : ℕ))) ↦
    if
        (↑i : ℕ) =
          H.dividerCount +
            (1 : ℕ) then
      U
    else H.stage i;
  (newStageLast :
      newStage
          (Fin.last
            (H.dividerCount +
              (1 :
                ℕ))) =
        U) →
  (newStageAt :
  ∀
    (i :
      Fin
        (H.dividerCount +
          (2 :
            ℕ)))
    (_ :
      (↑i : ℕ) ≤
        H.dividerCount),
  newStage i =
    H.stage i) →
  (newNested :
  ∀
    (i :
      Fin
        (H.dividerCount +
          (1 :
            ℕ))),
  TreeSequenceInitialSegment
    (newStage
      i.castSucc)
    (newStage
      i.succ)) →
  (newStrict :
  ∀
    (i :
      Fin
        (H.dividerCount +
          (1 :
            ℕ))),
  (newStage
        i.castSucc).length <
    (newStage
        i.succ).length) →
  TashkinovHierarchy
    RU baseU := by
  classical
  intro V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett base C ctx P H R mu n Tn q A j B trans
      coreA hBT S U hAU hBU newInput newSeries roundsPositive above strict below generating RU baseU
      hcore hTnEq hdivB prefixEq newStage newStageLast newStageAt newNested newStrict
  exact {
    dividerCount := H.dividerCount
    stage := newStage
    baseStage := by
      rw [show newStage 0 = H.stage 0 by simp [newStage], H.baseStage]
      exact hTnEq.symm
    terminalStage := newStageLast
    nested := newNested
    strict := newStrict
    dividerPosition := fun i => ⟨(H.dividerPosition i).val,
      Nat.lt_succ_of_le ((hdivB i).trans hBU.1)⟩
    dividerPositive := H.dividerPositive
    dividerIncreasing := H.dividerIncreasing
    dividerStage := by
      intro i
      rw [newStageAt ⟨i.val + 1, by omega⟩ (Nat.succ_le_of_lt i.isLt)]
      rw [prefixEq (H.dividerPosition i).val (H.dividerPositive i) (hdivB i)]
      exact H.dividerStage i
    coreInsideFirst := by
      rw [hcore]
      by_cases hz : H.dividerCount = 0
      · rw [show newStage ⟨1, by omega⟩ = U by simp [newStage, hz]]
        exact trans coreA hAU
      · rw [newStageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hz)]
        exact H.coreInsideFirst };

private abbrev helperContinuation2608Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) (alpha beta : Fin k),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
   P.counterexample.hierarchy;
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
   P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (j : ℕ) (hpathLower : (2 : ℕ) ≤ j),
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  let y : V := T.vertex (Fin.last T.length);
  ∀
   (trans :
  ∀ {S U W : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U)
   (hUW : TreeSequenceInitialSegment U W),
  TreeSequenceInitialSegment S W)
   (hpOld : HierarchyPathNumber H = j) (hjlow : (2 : ℕ) ≤ j)
   (coreA : TreeSequenceInitialSegment P.replacementBase.core A)
   (hBLen : B.length = A.length + (j - (2 : ℕ))) (hXLen : X.length = A.length + (j - (1 : ℕ)))
   (hBT : TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - (2 : ℕ))) T)
   (hyB : y ∉ TreeSequenceVertexSet B)
   (hay : alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)))
   (haB : alpha ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C (j - (2 : ℕ))))
   (hba : beta ≠ alpha) (hab : alpha ≠ beta)
   (exceptional :
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  ¬∃ u ∈ TreeSequenceVertexSet B, Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y))
   (S U : TreeSequence G e0) (hBS : TreeSequenceInitialSegment B S)
   (hSUstrict : S.length < U.length) (hUlast : U.vertex (Fin.last U.length) = y)
   (hUpath :
  ∀ (r : Fin U.length),
  X.length ≤ (↑r : ℕ) →
  G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ))
   (hScorner :
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  S = X)
   (hAU : TreeSequenceInitialSegment A U) (hBU : TreeSequenceInitialSegment B U)
   (newInput : PartialEdgeColoring E k) (newSeries : TashkinovSeries G k R.rounds e0 newInput)
   (hgen : mu = newSeries.data.coloring (Fin.last R.rounds))
   (htrees :
  ∀ (i : Fin R.rounds),
  newSeries.data.tree i.succ.castSucc = R.series.data.tree i.succ.castSucc)
   (hstored :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  newSeries.data.stored i = R.series.data.stored i)
   (hedges :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  newSeries.data.connectingEdges i = R.series.data.connectingEdges i)
   (hkinds :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  newSeries.data.kind i = R.series.data.kind i)
   (hproper :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  IsProperEdgeColoring G (newSeries.data.coloring i))
   (hone :
  ∀ (i : Fin (R.rounds + (1 : ℕ))),
  IsOneEdgeUncolored (newSeries.data.coloring i) e0)
   (hstable :
  ∀ (i : Fin R.rounds),
  StableColoring (R.series.data.tree i.succ.castSucc)
   (TashkinovStoredColors R.series.data i.succ) (R.series.data.coloring i.succ)
   (newSeries.data.coloring i.succ))
   (roundsPositive : (1 : ℕ) ≤ R.1)
   (above :
    TreeSequenceInitialSegment (newSeries.data.tree (⟨R.1, by omega⟩ : Fin (R.1 + (2 : ℕ)))) U)
   (strict : (newSeries.data.tree (⟨R.1, by omega⟩ : Fin (R.1 + (2 : ℕ)))).length < U.length)
   (below : TreeSequenceInitialSegment U (newSeries.data.tree (Fin.last (R.1 + (1 : ℕ)))))
   (generating : mu = newSeries.data.coloring (Fin.last R.1))
   (hseries :
    {
     rounds := R.1, roundsPositive := roundsPositive, series := newSeries,
       abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
       generatingColoring := generating : ExtendedTashkinovTree G k e0 newInput U mu }.series ≍
     newSeries),
  let RU : ExtendedTashkinovTree G k e0 newInput U mu :=
   {
    rounds := R.rounds, roundsPositive := roundsPositive, series := newSeries,
    abovePenultimate := above, strictAbovePenultimate := strict, belowFinal := below,
    generatingColoring := generating : ExtendedTashkinovTree G k e0 newInput U mu };
  ∀ (baseU : HierarchyBase RU mu) (hcore : baseU.core = P.replacementBase.core)
   (hclosure : baseU.closure = P.replacementBase.closure) (hMP : MaximumProperty RU)
   (hTnEq : newSeries.data.tree n.castSucc = Tn)
   (stageB :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  TreeSequenceInitialSegment (H.stage i.castSucc) B)
   (hdivB :
  ∀ (i : Fin H.dividerCount),
  (↑(H.dividerPosition i) : ℕ) ≤ B.length)
   (prefixEq :
  ∀ (p : ℕ) (hp : (1 : ℕ) ≤ p) (hpB : p ≤ B.length),
  TreeSequencePrefix U p hp (LE.le.trans hpB hBU.1) =
   TreeSequencePrefix T p hp (LE.le.trans hpB hBT.1)),
  let newStage :
  Fin (H.dividerCount + (2 : ℕ)) →
  TreeSequence G e0 :=
   fun (i : Fin (H.dividerCount + (2 : ℕ))) ↦
   if (↑i : ℕ) = H.dividerCount + (1 : ℕ) then U else H.stage i;
  ∀ (newStageLast : newStage (Fin.last (H.dividerCount + (1 : ℕ))) = U)
   (newStageAt :
  ∀ (i : Fin (H.dividerCount + (2 : ℕ))) (hi : (↑i : ℕ) ≤ H.dividerCount),
  newStage i = H.stage i)
   (newNested :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  TreeSequenceInitialSegment (newStage i.castSucc) (newStage i.succ))
   (newStrict :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  (newStage i.castSucc).length < (newStage i.succ).length),
  let K : TashkinovHierarchy RU baseU := by
   exact
    @helperK2280 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G) (@k)
     (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@j) (@trans) (@coreA) (@hBT)
     (@S) (@U) (@hAU) (@hBU) (@newInput) (@newSeries) (@roundsPositive) (@above) (@strict)
     (@below) (@generating) (@baseU) (@hcore) (@hTnEq) (@hdivB) (@prefixEq) (@newStageLast)
     (@newStageAt) (@newNested) (@newStrict)
  ∀ (stageEq :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  K.stage i.castSucc = H.stage i.castSucc)
   (starredEq :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  HierarchyStarredStage K i = HierarchyStarredStage H i)
   (storedEq :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  HierarchyStoredColorsAt K i = HierarchyStoredColorsAt H i)
   (missingEq :
  ∀ (i : Fin (H.dividerCount + (1 : ℕ))),
  HierarchyStageMissingColors K i = HierarchyStageMissingColors H i)
   (cutoffEq :
  ∀ (c : Fin k) (p : ℕ) (hp : p ≤ S.length),
  min (↑(HierarchyFirstMissingPosition mu U c) : ℕ) p =
   min (↑(HierarchyFirstMissingPosition mu T c) : ℕ) p)
   (lastAvoidance :
  ∀ (eta : Fin k) (heta : eta ∈ HierarchyStoredColorsAt H q) (c : Fin k)
   (hc : c ∈ P.counterexample.good.gamma q eta),
  c ∉ HierarchySegmentColors K q eta),
  False

private theorem helper_branch_221.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  (
  ∀ (S : TreeSequence G e0),
  TreeSequenceInitialSegment S S) →
  ∀ (hb : (0 : ℕ) < H.dividerCount + (2 : ℕ)) (a : Fin (H.dividerCount + (2 : ℕ))),
  (↑a : ℕ) ≤ (0 : ℕ) →
  TreeSequenceInitialSegment (H.stage a)
    (H.stage (⟨(0 : ℕ), hb⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H reflSeg hb a ha
  have he : a = 0 := Fin.ext (Nat.eq_zero_of_le_zero ha)
  subst a
  exact reflSeg _

private theorem helper_branch_226.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  (
  ∀ (S : TreeSequence G e0),
  TreeSequenceInitialSegment S S) →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeSequenceInitialSegment U W →
  TreeSequenceInitialSegment S W) →
  ∀ (b : ℕ),
  (
  ∀ (hb : b < H.dividerCount + (2 : ℕ)) (a : Fin (H.dividerCount + (2 : ℕ))),
  (↑a : ℕ) ≤ b →
  TreeSequenceInitialSegment (H.stage a)
    (H.stage (⟨b, hb⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
  ∀ (hb : b + (1 : ℕ) < H.dividerCount + (2 : ℕ)) (a : Fin (H.dividerCount + (2 : ℕ))),
  (↑a : ℕ) ≤ b + (1 : ℕ) →
  TreeSequenceInitialSegment (H.stage a)
    (H.stage (⟨b + (1 : ℕ), hb⟩ : Fin (H.dividerCount + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H reflSeg trans b ih hb a ha
  by_cases he : a.val = b + 1
  · have heq : a = ⟨b + 1, hb⟩ := Fin.ext he
    subst a
    exact reflSeg _
  · exact trans (ih (by omega) a (by omega)) (H.nested ⟨b, by omega⟩)

private theorem helper_lastPositive_240.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (_ : ℕ),
  H.dividerCount ≠ (0 : ℕ) →
  A =
    H.stage
      (⟨H.dividerCount, by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q A j hz
  unfold A HierarchyStarredStage
  obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
  · have hv := congrArg Fin.val hzero
    simp only [q, Fin.val_last, Fin.val_zero] at hv
    contradiction
  · rw [hi]
    simp only [Fin.cases_succ]
    congr 1
    apply Fin.ext
    simpa [q] using (congrArg Fin.val hi).symm

private theorem helper_branch_317.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      {U : TreeSequence G e0} (sl : ℕ) (sp : (1 : ℕ) ≤ sl) (sv :
  Fin (sl + (1 : ℕ)) →
  V)
      (se :
  Fin sl →
  E) (svi : Function.Injective sv) (sei : Function.Injective se)
      (sf : se (⟨(0 : ℕ), sp⟩ : Fin sl) = e0)
      (sa :
  ∀ (j : Fin sl),
  ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
    G.ends (se j) = s(sv j.succ, sv (i.castLT (by omega)))),
  TreeSequenceInitialSegment
      { length := sl, positive := sp, vertex := sv, edge := se, vertex_injective := svi,
        edge_injective := sei, first_edge := sf, attaches := sa : TreeSequence G e0 }
      U →
  { length := sl, positive := sp, vertex := sv, edge := se, vertex_injective := svi,
          edge_injective := sei, first_edge := sf, attaches := sa :
          TreeSequence G e0 }.length =
      U.length →
  { length := sl, positive := sp, vertex := sv, edge := se, vertex_injective := svi,
      edge_injective := sei, first_edge := sf, attaches := sa : TreeSequence G e0 } =
    U := by
  classical
  intro V E G e0 U sl sp sv se svi sei sf sa hSU hlen
  cases U with
  | mk ul up uv ue uvi uei uf ua =>
    dsimp only at hlen
    subst ul
    have hv : uv = sv := funext hSU.2.1
    have he : ue = se := funext hSU.2.2
    subst uv
    subst ue
    rfl

private theorem helper_branch_397.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
  n = (0 : Fin (R.rounds + (1 : ℕ))) →
  ColoredVertexSetClosed G mu (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P R mu n Tn hn
  have hv := congrArg Fin.val hn
  simp only [n, Fin.val_last, Fin.val_zero] at hv
  have := R.roundsPositive
  omega

private theorem helper_branch_402.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
  (
  ∀ (W : TreeSequence G e0) (D : Finset (Fin k)) (rho sigma : PartialEdgeColoring E k),
  IsProperEdgeColoring G rho →
  IsOneEdgeUncolored rho e0 →
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  StableColoring W D rho sigma →
  ColoredVertexSetClosed G rho (TreeSequenceVertexSet W) →
  ColoredVertexSetClosed G sigma (TreeSequenceVertexSet W)) →
  ∀ (i : Fin R.rounds),
  IsProperEdgeColoring G (R.series.data.coloring i.castSucc) →
  IsOneEdgeUncolored (R.series.data.coloring i.castSucc) e0 →
  ColoredVertexSetClosed G (R.series.data.coloring i.castSucc)
      (TreeSequenceVertexSet (R.series.data.tree i.succ.castSucc)) →
  ∀
    (choice :
      MaximumDefectiveChoice G e0 (R.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors R.series.data i.castSucc)
        (R.series.data.coloring i.castSucc)),
  R.series.data.coloring i.succ = choice.selected →
  n = i.succ →
  ColoredVertexSetClosed G mu (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P R mu n Tn stableClosed i hp ho hc choice
      hcol hn
  have hin : i.succ = n := hn.symm
  have hm : mu = choice.selected := by
    have hg : mu = R.series.data.coloring n := R.generatingColoring
    rw [← hin, hcol] at hg
    exact hg
  rw [hm]
  have htree : Tn = R.series.data.tree i.succ.castSucc := by rw [hin]
  rw [htree]
  exact @stableClosed _ _ _ _ hp ho choice.selectedProper
    choice.selectedOneUncolored choice.selectedStable @hc

private theorem helper_branch_419.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
  ∀ (i : Fin R.rounds),
  ColoredVertexSetClosed G (R.series.data.coloring i.castSucc)
      (TreeSequenceVertexSet (R.series.data.tree i.succ.castSucc)) →
  R.series.data.coloring i.succ = R.series.data.coloring i.castSucc →
  n = i.succ →
  ColoredVertexSetClosed G mu (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P R mu n Tn i hc hcol hn
  have hin : i.succ = n := hn.symm
  have hm : mu = R.series.data.coloring i.castSucc := by
    have hg : mu = R.series.data.coloring n := R.generatingColoring
    rw [← hin, hcol] at hg
    exact hg
  rw [hm, show Tn = R.series.data.tree i.succ.castSucc by rw [hin]]
  exact @hc

private theorem helper_exceptional_436.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
  (alpha beta : Fin k),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (j : ℕ),
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  let y : V := T.vertex (Fin.last T.length);
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeSequenceInitialSegment U W →
  TreeSequenceInitialSegment S W) →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S W →
  TreeSequenceInitialSegment U W →
  S.length ≤ U.length →
  TreeSequenceInitialSegment S U) →
  HierarchyPathNumber H = j →
  TreeSequenceInitialSegment A T →
  (
  H.dividerCount = (0 : ℕ) →
  A = P.replacementBase.core) →
  B.length = A.length + (j - (2 : ℕ)) →
  X.length = A.length + (j - (1 : ℕ)) →
  TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - (2 : ℕ))) T →
  TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - (1 : ℕ))) T →
  TreeSequenceInitialSegment A B →
  X.length = B.length + (1 : ℕ) →
  X.length < T.length →
  y ∉ TreeSequenceVertexSet B →
  alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) →
  alpha ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C (j - (2 : ℕ))) →
  beta ≠ alpha →
  beta ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C (j - (2 : ℕ))) →
  alpha ≠ beta →
  (
  ∀ {S U : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeMissingColors mu S ⊆ TreeMissingColors mu U) →
  (
  ∀ {S U : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  S.length = U.length →
  S = U) →
  (
  ∀ (W : TreeSequence G e0) (c : Fin k),
  (↑(HierarchyFirstMissingPosition mu W c) : ℕ) < W.length →
  c ∈ MissingColors G mu (W.vertex (HierarchyFirstMissingPosition mu W c))) →
  (
  ∀ {W Z : TreeSequence G e0},
  TreeSequenceInitialSegment W Z →
  ∀ c ∈ TreeMissingColors mu W,
    (↑(HierarchyFirstMissingPosition mu Z c) : ℕ) ≤ W.length) →
  (
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  ColoredVertexSetClosed G mu (TreeSequenceVertexSet Tn)) →
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  ¬∃ u ∈ TreeSequenceVertexSet B,
      Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H R mu n Tn q A j B X y trans
      common hpOld hAT lastZero hBLen hXLen hBT hXT hAB hBXLen hXshort hyB hay haB hba hbB hab
      missingMono equalSeg firstMem firstBound nonparallelClosed hz hj hk hmeet
  have hABeq : A = B := equalSeg hAB (by omega)
  have hATneq : A = Tn := (lastZero hz).trans (P.replacementBase.nonparallel hk)
  have hBTneq : B = Tn := hABeq.symm.trans hATneq
  have haA : alpha ∈ TreeMissingColors mu A := by rw [hABeq]; exact haB
  have hbA : beta ∈ TreeMissingColors mu A := by rw [hABeq]; exact hbB
  have haclosed : TreeColorSetClosed G mu A {alpha} := by
    intro c hc
    have he : c = alpha := Finset.mem_singleton.mp hc
    subst c
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    simp only [BoundaryColorEdges, Finset.mem_filter] at hf
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp haA
    have hclosed : ColoredVertexSetClosed G mu (TreeSequenceVertexSet A) := by
      rw [hATneq]
      exact nonparallelClosed hk
    exact hclosed hf.1 hv hf.2 hm
  have helem : ColoredVertexSetElementary G mu (TreeSequenceVertexSet
      (HierarchyFullTailPrefix P.counterexample
        (HierarchyFullTailLength P.counterexample - 1))) :=
    HierarchyCounterexamplePenultimateElementary
    G k e0 P.corresponding.replacementInput T mu R P.replacementBase
    P.counterexample P.minimumContext.proper P.minimumContext.oneEdgeUncolored
    P.minimumContext.lowerRung P.minimumContext.fewerDividers
    P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
  have missingPen :
      let Z := HierarchyFullTailPrefix P.counterexample
        (HierarchyFullTailLength P.counterexample - 1)
      alpha ∈ TreeMissingColors mu Z ∧ beta ∈ TreeMissingColors mu Z := by
    let Z := HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - 1)
    have hZT : TreeSequenceInitialSegment Z T :=
      ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
    have hZLen : Z.length = T.length - 1 := by
      change min (A.length + ((T.length - A.length) - 1)) T.length = T.length - 1
      omega
    have hBZ : TreeSequenceInitialSegment B Z := common hBT hZT (by omega)
    exact ⟨missingMono hBZ haB, missingMono hBZ hbB⟩
  have change := ChangeLemma G k e0 P.corresponding.replacementInput T mu R
    P.replacementBase P.counterexample P.minimumContext.proper
    P.minimumContext.oneEdgeUncolored P.minimumContext.lowerRung
    P.minimumContext.fewerDividers P.minimumContext.lexicographicMinimality
    helem P.minimumContext.largeMissingSet alpha beta hab missingPen
    (by
      dsimp only
      exact fun h => False.elim (h.elim (fun ha => ha haA) (fun hb => hb hbA)))
  obtain ⟨hsame, hinter⟩ := change.2.2 ⟨haA, haclosed⟩
  let va := T.vertex (HierarchyFirstMissingPosition mu T alpha)
  let vb := T.vertex (HierarchyFirstMissingPosition mu T beta)
  have vaB : va ∈ TreeSequenceVertexSet B := by
    let ia : Fin (B.length + 1) :=
      ⟨(HierarchyFirstMissingPosition mu T alpha).val,
        Nat.lt_succ_of_le (firstBound hBT alpha haB)⟩
    have hi : Fin.castLE (Nat.succ_le_succ hBT.1) ia =
        HierarchyFirstMissingPosition mu T alpha := Fin.ext rfl
    rw [show va = B.vertex ia by rw [← hBT.2.1 ia, hi]]
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨ia, rfl⟩
  have vbB : vb ∈ TreeSequenceVertexSet B := by
    let ib : Fin (B.length + 1) :=
      ⟨(HierarchyFirstMissingPosition mu T beta).val,
        Nat.lt_succ_of_le (firstBound hBT beta hbB)⟩
    have hi : Fin.castLE (Nat.succ_le_succ hBT.1) ib =
        HierarchyFirstMissingPosition mu T beta := Fin.ext rfl
    rw [show vb = B.vertex ib by rw [← hBT.2.1 ib, hi]]
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨ib, rfl⟩
  have hva : alpha ∈ MissingColors G mu va :=
    firstMem T alpha (lt_of_le_of_lt (firstBound hBT alpha haB)
      (lt_of_lt_of_le (by omega : B.length < X.length) hXT.1))
  have hvb : beta ∈ MissingColors G mu vb :=
    firstMem T beta (lt_of_le_of_lt (firstBound hBT beta hbB)
      (lt_of_lt_of_le (by omega : B.length < X.length) hXT.1))
  have elemA : ColoredVertexSetElementary G mu (TreeSequenceVertexSet A) := by
    intro v hv w hw hne
    have hZT : TreeSequenceInitialSegment
        (HierarchyFullTailPrefix P.counterexample
          (HierarchyFullTailLength P.counterexample - 1)) T :=
      ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
    have hAZ : TreeSequenceInitialSegment A
        (HierarchyFullTailPrefix P.counterexample
          (HierarchyFullTailLength P.counterexample - 1)) :=
      common hAT hZT (by
        change A.length ≤ min (A.length + ((T.length - A.length) - 1)) T.length
        omega)
    exact helem (TreeSequenceInitialSegmentVertexSetSubset hAZ hv)
      (TreeSequenceInitialSegmentVertexSetSubset hAZ hw) hne
  have vaA : va ∈ TreeSequenceVertexSet A := by rw [hABeq]; exact vaB
  have vbA : vb ∈ TreeSequenceVertexSet A := by rw [hABeq]; exact vbB
  obtain ⟨hdis, hyPath, hswap⟩ := P2905_T2_ElementaryTerminalComponent
    G mu alpha beta hab P.minimumContext.proper (TreeSequenceVertexSet A)
    elemA va vb y vaA vbA (fun he => hyB (he ▸ vaB))
    (fun he => hyB (he ▸ vbB)) hva hvb (Or.inl hay) hsame
  have vaPath : TwoColorPathComponent G mu alpha beta (Sum.inl va) := by
    exact TwoColorPathComponent.of_missing P.minimumContext.proper hab hva
  have hmeetA : ∃ u ∈ TreeSequenceVertexSet A,
      Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y) := by
    rw [hABeq]
    exact hmeet
  have heq := hinter (Sum.inl y) (Sum.inl va) hyPath vaPath hmeetA
    ⟨va, vaA, by rfl⟩
  exact Set.disjoint_left.mp hdis (heq.symm ▸ (show
    Sum.inl va ∈ TwoColorComponent G mu alpha beta (Sum.inl va) by rfl)) (by rfl)

private theorem helper_branch_567.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
  (alpha beta : Fin k),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (j : ℕ),
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  let y : V := T.vertex (Fin.last T.length);
  (
  ∀ (S : TreeSequence G e0),
  TreeSequenceInitialSegment S S) →
  B.length = A.length + (j - (2 : ℕ)) →
  X.length = A.length + (j - (1 : ℕ)) →
  TreeSequenceInitialSegment B X →
  X.length = B.length + (1 : ℕ) →
  y ∉ TreeSequenceVertexSet B →
  alpha ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C (j - (2 : ℕ))) →
  beta ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C (j - (2 : ℕ))) →
  alpha ≠ beta →
  (
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  ¬∃ u ∈ TreeSequenceVertexSet B,
      Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y)) →
  (∃ u ∈ TreeSequenceVertexSet B,
      Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y)) →
  ∃ (S : TreeSequence G e0) (U : TreeSequence G e0),
  TreeSequenceInitialSegment B S ∧
    TreeSequenceInitialSegment S X ∧
      TreeSequenceInitialSegment S U ∧
        S.length < U.length ∧
          TashkinovAugmentationSequence mu S U ∧
            U.vertex (Fin.last U.length) = y ∧
              (
  ∀ (r : Fin U.length),
  S.length ≤ (↑r : ℕ) →
  mu (U.edge r) = some alpha ∨ mu (U.edge r) = some beta) ∧
                (
  ∀ (r : Fin U.length),
  X.length ≤ (↑r : ℕ) →
  G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ)) ∧
                  (
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  S = X) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H R mu n q A j B X y reflSeg
      hBLen hXLen hBX hBXLen hyB haB hbB hab exceptional hmeet
  obtain ⟨u, U, hu, huQ, hBU, hlen, haug, hlast, hnew⟩ :=
    TwoColorComponentTashkinovSplice G mu B alpha beta y
      P.minimumContext.proper hab haB hbB hyB hmeet
  refine ⟨B, U, reflSeg _, hBX, hBU, hlen, haug, hlast,
    fun r hr => (hnew r hr).2.2.2.1, ?_, ?_⟩
  · intro r hr
    have hn := (hnew r (by omega)).2.2.2.2
    rw [ite_eq_right (by omega)] at hn
    exact hn
  · intro hz hj hk
    exact False.elim (exceptional hz hj hk hmeet)

private theorem helper_branch_578.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
  (alpha beta : Fin k),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  ∀ (j : ℕ),
  (
  let j : ℕ := j;
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  ∃ u ∈ TreeSequenceVertexSet X,
    Sum.inl u ∈
      TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))) →
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  let y : V := T.vertex (Fin.last T.length);
  (
  ∀ (S : TreeSequence G e0),
  TreeSequenceInitialSegment S S) →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeSequenceInitialSegment U W →
  TreeSequenceInitialSegment S W) →
  TreeSequenceInitialSegment B X →
  X.length = B.length + (1 : ℕ) →
  y ∉ TreeSequenceVertexSet X →
  alpha ≠ beta →
  alpha ∈ TreeMissingColors mu X →
  beta ∈ TreeMissingColors mu X →
  (¬∃ u ∈ TreeSequenceVertexSet B,
        Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y)) →
  ∃ (S : TreeSequence G e0) (U : TreeSequence G e0),
  TreeSequenceInitialSegment B S ∧
    TreeSequenceInitialSegment S X ∧
      TreeSequenceInitialSegment S U ∧
        S.length < U.length ∧
          TashkinovAugmentationSequence mu S U ∧
            U.vertex (Fin.last U.length) = y ∧
              (
  ∀ (r : Fin U.length),
  S.length ≤ (↑r : ℕ) →
  mu (U.edge r) = some alpha ∨ mu (U.edge r) = some beta) ∧
                (
  ∀ (r : Fin U.length),
  X.length ≤ (↑r : ℕ) →
  G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ)) ∧
                  (
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  S = X) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H R mu n j hintersection B X y
      reflSeg trans hBX hBXLen hyX hab haX hbX hmeet
  obtain ⟨u, U, hu, huQ, hXU, hlen, haug, hlast, hnew⟩ :=
    TwoColorComponentTashkinovSplice G mu X alpha beta y
      P.minimumContext.proper hab haX hbX hyX hintersection
  have huLast : u = X.vertex (Fin.last X.length) := by as_aux_lemma =>
    clear * - hmeet hBX hBXLen hu huQ
    obtain ⟨i, hi⟩ : ∃ i, X.vertex i = u := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hu
    by_cases hh : i.val ≤ B.length
    · have hb : u ∈ TreeSequenceVertexSet B := by
        let ib : Fin (B.length + 1) := ⟨i.val, by omega⟩
        have hc : Fin.castLE (Nat.succ_le_succ hBX.1) ib = i := Fin.ext rfl
        rw [← hi, ← hc, hBX.2.1 ib]
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨ib, rfl⟩
      exact False.elim (hmeet ⟨u, hb, huQ⟩)
    · have he : i = Fin.last X.length := Fin.ext (by
        change i.val = X.length
        have := i.isLt
        omega)
      exact hi.symm.trans (congrArg X.vertex he)
  refine ⟨X, U, hBX, reflSeg _, hXU, hlen, haug, hlast,
    fun r hr => (hnew r hr).2.2.2.1, ?_, fun _ _ _ => rfl⟩
  intro r hr
  have hn := (hnew r hr).2.2.2.2
  by_cases he : r.val = X.length
  · rw [ite_eq_left he, huLast] at hn
    have hv : U.vertex r.castSucc = X.vertex (Fin.last X.length) := by
      have hi : Fin.castLE (Nat.succ_le_succ hXU.1) (Fin.last X.length) =
          r.castSucc := Fin.ext he.symm
      rw [← hi, hXU.2.1]
    rw [hv]
    exact hn
  · rw [ite_eq_right he] at hn
    exact hn

private theorem helper_branch_636.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
  (alpha beta : Fin k),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let mu : PartialEdgeColoring E k := P.coloring;
  let n : Fin (R.rounds + (1 : ℕ)) := Fin.last R.rounds;
  let Tn : TreeSequence G e0 := R.series.data.tree n.castSucc;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (j : ℕ),
  (2 : ℕ) ≤ j →
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  let y : V := T.vertex (Fin.last T.length);
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeSequenceInitialSegment U W →
  TreeSequenceInitialSegment S W) →
  (
  ∀ {S U W : TreeSequence G e0},
  TreeSequenceInitialSegment S W →
  TreeSequenceInitialSegment U W →
  S.length ≤ U.length →
  TreeSequenceInitialSegment S U) →
  HierarchyPathNumber H = j →
  (
  ∀ (b : ℕ) (hb : b < H.dividerCount + (2 : ℕ)) (a : Fin (H.dividerCount + (2 : ℕ))),
  (↑a : ℕ) ≤ b →
  TreeSequenceInitialSegment (H.stage a)
    (H.stage (⟨b, hb⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
  (
  H.dividerCount = (0 : ℕ) →
  A = P.replacementBase.core) →
  (
  H.dividerCount ≠ (0 : ℕ) →
  A =
    H.stage
      (⟨H.dividerCount,
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin (H.dividerCount + (2 : ℕ)))) →
  B.length = A.length + (j - (2 : ℕ)) →
  X.length = A.length + (j - (1 : ℕ)) →
  X.length = B.length + (1 : ℕ) →
  beta ≠ alpha →
  alpha ≠ beta →
  (
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  ¬∃ u ∈ TreeSequenceVertexSet B,
      Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y)) →
  ∀ (S U : TreeSequence G e0),
  TreeSequenceInitialSegment B S →
  TashkinovAugmentationSequence mu S U →
  (
  H.dividerCount = (0 : ℕ) →
  j = (2 : ℕ) →
  R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
  S = X) →
  TreeSequenceInitialSegment S T →
  TreeSequenceInitialSegment A S →
  R.series.data.kind (Fin.last R.rounds) = some TashkinovExtensionKind.SE ∨
      R.series.data.kind (Fin.last R.rounds) = some TashkinovExtensionKind.RE →
  ∀ (f : E) (seed : TreeSequence G e0),
  R.series.data.connectingEdges (Fin.last R.rounds) = ({ f } : Finset E) →
  TreeSequenceAdjoinEdge (R.series.data.tree (Fin.last R.rounds).castSucc) f seed →
  TashkinovAugmentationSequence mu seed T →
  R.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence mu Tn U ∨
    (R.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (seed : TreeSequence G e0),
        R.series.data.connectingEdges n = ({ f } : Finset E) ∧
          TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence mu seed U := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H R mu n Tn q A j hpathLower B
      X y trans common hpOld chain lastZero lastPositive hBLen hXLen hBXLen hba hab exceptional S
      U hBS hSUaug hScorner hST hAS hkind f seed hedges hadjoin haug
  have hnonpe : R.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
    rcases hkind with h | h <;> rw [h] <;> decide
  have hseedT := TashkinovAugmentationSequenceInitialSegment mu seed T haug
  have hseedLen : seed.length = Tn.length + 1 := hadjoin.1
  have hseedS : TreeSequenceInitialSegment seed S := by
    apply common hseedT hST
    by_cases hz : H.dividerCount = 0
    · have hAeq : A = Tn := (lastZero hz).trans (P.replacementBase.nonparallel hnonpe)
      have hAlem : A.length = Tn.length := congrArg TreeSequence.length hAeq
      by_cases hj : j = 2
      · have hseq := hScorner hz hj hnonpe
        rw [hseq]
        omega
      · have hbs := hBS.1
        omega
    · obtain ⟨r, hr, he⟩ := HierarchyNonparallelFirstEdge H f hkind hedges
      change r.val = Tn.length at hr
      have hfirstA : TreeSequenceInitialSegment (H.stage ⟨1, by omega⟩) A := by
        rw [lastPositive hz]
        exact chain H.dividerCount (by omega) ⟨1, by omega⟩
          (by change 1 ≤ H.dividerCount; omega)
      have hf := r.isLt
      have hfa := hfirstA.1
      have has := hAS.1
      omega
  exact Or.inr ⟨hkind, f, seed, hedges, hadjoin,
    (TashkinovAugmentationSequenceRestrict mu seed S T haug hseedS hST).trans hSUaug⟩

private theorem helper_branch_850.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  let mu : PartialEdgeColoring E k := P.coloring;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let _ : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (S U : TreeSequence G e0),
  TreeSequenceInitialSegment S U →
  TreeSequenceInitialSegment S T →
  (
  ∀ (c : Fin k),
  ∀ p ≤ S.length,
    min (↑(HierarchyFirstMissingPosition mu U c) : ℕ) p =
      min (↑(HierarchyFirstMissingPosition mu T c) : ℕ) p) →
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  ∀ c ∈ P.counterexample.good.gamma q eta,
  ∀ (r : Fin U.length),
  (HierarchyStarredStage H q).length ≤ (↑r : ℕ) →
  (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition mu U eta) : ℕ) U.length →
  mu (U.edge r) = some c →
  (↑r : ℕ) < S.length →
  False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H mu q A S U hSU hST cutoffEq eta heta c
      hc r hrA hrp hrc hrS
  let rs : Fin S.length := ⟨r.val, hrS⟩
  let rt : Fin T.length := Fin.castLE hST.1 rs
  have hrU : Fin.castLE hSU.1 rs = r := Fin.ext rfl
  have hcol : mu (T.edge rt) = some c := by
    rw [hST.2.2 rs, ← hSU.2.2 rs, hrU]
    exact hrc
  have hcut := cutoffEq eta S.length le_rfl
  have hrnew : r.val < min (HierarchyFirstMissingPosition mu U eta).val S.length :=
    lt_min (lt_min_iff.mp hrp).1 hrS
  rw [hcut] at hrnew
  have hold : c ∈ HierarchySegmentColors H q eta := by
    change c ∈ Finset.univ.filter (fun c => ∃ t : Fin (H.stage q.succ).length,
      A.length ≤ t.val ∧
        t.val < min (HierarchyFirstMissingPosition mu T eta).val
          (H.stage q.succ).length ∧ mu ((H.stage q.succ).edge t) = some c)
    rw [show H.stage q.succ = T by exact H.terminalStage]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rt, hrA,
      lt_min (lt_min_iff.mp hrnew).1 rt.isLt, hcol⟩
  exact (Finset.mem_sdiff.mp (P.counterexample.good.avoidance q eta heta hc)).2 hold

private theorem helper_hnotElementary_940.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
  (alpha : Fin k),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (j : ℕ),
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let y : V := T.vertex (Fin.last T.length);
  y ∉ TreeSequenceVertexSet B →
  alpha ∈ MissingColors G P.coloring (T.vertex (Fin.last T.length)) →
  alpha ∈ TreeMissingColors P.coloring (HierarchyFullTailPrefix C (j - (2 : ℕ))) →
  ∀ (U : TreeSequence G e0),
  U.vertex (Fin.last U.length) = y →
  TreeSequenceInitialSegment B U →
  ¬ColoredVertexSetElementary G mu (TreeSequenceVertexSet U) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha mu j B y hyB hay haB U hUlast hBU
      helem
  obtain ⟨v, hv, hmissing⟩ := Finset.mem_biUnion.mp haB
  have hvU := TreeSequenceInitialSegmentVertexSetSubset hBU hv
  have hyU : y ∈ TreeSequenceVertexSet U := by
    rw [← hUlast]
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last U.length, rfl⟩
  have hne : v ≠ y := by
    intro he
    exact hyB (he ▸ hv)
  exact Finset.disjoint_left.mp (helem hvU hyU hne) hmissing hay

private theorem helper_hm_964.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
  (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
    P.counterexample.hierarchy;
  let R : ExtendedTashkinovTree G k e0 P.corresponding.replacementInput T P.coloring :=
    P.corresponding.replacementETT;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (j : ℕ),
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  (2 : ℕ) ≤ j →
  B.length = A.length + (j - (2 : ℕ)) →
  X.length = A.length + (j - (1 : ℕ)) →
  ∀ (S U : TreeSequence G e0),
  TreeSequenceInitialSegment B S →
  S.length < U.length →
  (
  ∀ (r : Fin U.length),
  X.length ≤ (↑r : ℕ) →
  G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ)) →
  ∀ (newInput : PartialEdgeColoring E k) (_ : TashkinovSeries G k R.rounds e0 newInput),
  let candidates : Finset ℕ :=
    ({i ∈ Finset.Icc (1 : ℕ) (U.length - A.length) |
  ∀ (r : Fin U.length),
  A.length + i ≤ (↑r : ℕ) →
  G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ)} :
      Finset ℕ);
  j - (1 : ℕ) ∈ candidates := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H R q A j B X hjlow hBLen hXLen S U hBS
      hSUstrict hUpath newInput newSeries candidates
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
  · have hbs := hBS.1
    omega
  · intro r hr
    exact hUpath r (by omega)

private theorem helper_sameLast_1457.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) {a b : ℕ}
      (s :
  Fin (a + (2 : ℕ)) →
  TreeSequence G e0)
      (t :
  Fin (b + (2 : ℕ)) →
  TreeSequence G e0) (u v : TreeSequence G e0),
  a = b →
  s ≍ t →
  u = v →
  (Fin.cases u (fun (i : Fin a) ↦ s i.succ.castSucc) (Fin.last a) : TreeSequence G e0) =
    (Fin.cases v (fun (i : Fin b) ↦ t i.succ.castSucc) (Fin.last b) : TreeSequence G e0) := by
  classical
  intro V E G e0 a b s t u v hab hst huv
  cases hab
  cases eq_of_heq hst
  cases huv
  rfl

private theorem helper_equalSeg_2078.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) {S U : TreeSequence G e0}
  (_ : TreeSequenceInitialSegment S U) (_ : S.length = U.length),
  S = U := by
  classical
  intro V E G e0 S U hSU hlen
  cases S with
  | mk sl sp sv se svi sei sf sa =>
      exact @helper_branch_317 (@V) (@E) (@G) (@e0) (@U) (@sl) (@sp) (@sv) (@se) (@svi)
          (@sei) (@sf) (@sa) (@hSU) (@hlen)

private theorem helper_ownerBound_2434.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E
      k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
      input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ (j : ℕ),
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (2 : ℕ));
  let X : TreeSequence G e0 := HierarchyFullTailPrefix C (j - (1 : ℕ));
  ∀ (_ : TreeSequenceInitialSegment (HierarchyFullTailPrefix C (j - (2 : ℕ))) T)
    (_ : X.length = B.length + (1 : ℕ)) (_ : X.length < T.length)
    (_ :
  ∀ (W : TreeSequence G e0) (c : Fin k) (_ : (↑(HierarchyFirstMissingPosition mu W c) : ℕ)
      < W.length),
  c ∈ MissingColors G mu (W.vertex (HierarchyFirstMissingPosition mu W c)))
    (_ :
  ∀ {W Z : TreeSequence G e0} (_ : TreeSequenceInitialSegment W Z) (c : Fin k)
    (_ : c ∈ TreeMissingColors mu W),
  (↑(HierarchyFirstMissingPosition mu Z c) : ℕ) ≤
    W.length)
    (U : TreeSequence G e0) (_ : TreeSequenceInitialSegment B U) (eta : Fin k)
    (_ : (↑(HierarchyFirstMissingPosition mu T eta) : ℕ) ≤ B.length),
  (↑(HierarchyFirstMissingPosition mu U eta) : ℕ) ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P mu j B X hBT hBXLen hXshort firstMem
      firstBound U hBU eta he
  let i : Fin (B.length + 1) :=
    ⟨(HierarchyFirstMissingPosition mu T eta).val, Nat.lt_succ_of_le he⟩
  have hi : Fin.castLE (Nat.succ_le_succ hBT.1) i =
      HierarchyFirstMissingPosition mu T eta := Fin.ext rfl
  have hm : eta ∈ MissingColors G mu (B.vertex i) := by
    rw [← hBT.2.1 i, hi]
    apply firstMem T eta
    omega
  apply firstBound hBU eta
  apply Finset.mem_biUnion.mpr
  refine ⟨B.vertex i, ?_, hm⟩
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩

private theorem helper_prefixLen_2218.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E
      k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
      input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
      P.counterexample.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  ∀ (_ : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A)
    (_ : ell = T.length - A.length) (_ : TreeSequenceInitialSegment A T) (r : ℕ) (_ : r ≤ ell),
  (HierarchyFullTailPrefix C r).length = A.length + r := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q A ell hAold hell hAT r hr
  change min ((HierarchyStarredStage C.hierarchy
    (Fin.last C.hierarchy.dividerCount)).length + r) T.length = _
  rw [hAold]
  apply Nat.min_eq_left
  have hlen := hAT.1
  omega

private theorem helper_missingMono_2274.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E
      k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
      input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let mu : PartialEdgeColoring E k := P.coloring;
  ∀ {S U : TreeSequence G e0} (_ : TreeSequenceInitialSegment S U),
  TreeMissingColors mu S ⊆
    TreeMissingColors mu U := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P mu S U hSU c hc
  obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
  exact Finset.mem_biUnion.mpr
    ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSU hv, hm⟩

private theorem helper_hAold_2232.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
  [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E
      k)
  (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
      input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy P.corresponding.replacementETT P.replacementBase :=
      P.counterexample.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (j : ℕ) (_ : HierarchyPathNumber C.hierarchy = j)
    (_ : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A),
  HierarchyPathNumber H = j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P H q A j hjdef hAold
  rw [← hjdef]
  unfold HierarchyPathNumber
  dsimp only
  rw [hAold]

private theorem helper_continuation_2608.{u_1, u_2} :
    helperContinuation2608Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H R mu n Tn q A j hpathLower B X
      y trans hpOld hjlow coreA hBLen hXLen hBT hyB hay haB hba hab exceptional S U hBS hSUstrict
      hUlast hUpath hScorner hAU hBU newInput newSeries hgen htrees hstored hedges hkinds hproper
      hone hstable roundsPositive above strict below generating hseries RU baseU hcore hclosure hMP
      hTnEq stageB hdivB prefixEq newStage newStageLast newStageAt newNested newStrict K stageEq
      starredEq storedEq missingEq cutoffEq lastAvoidance
  have earlierSegment (i : Fin (H.dividerCount + 1)) (hi : i.val < H.dividerCount)
      (eta : Fin k) : HierarchySegmentColors K i eta = HierarchySegmentColors H i eta := by
    have hnext : K.stage i.succ = H.stage i.succ :=
      newStageAt i.succ (by change i.val + 1 ≤ H.dividerCount; omega)
    have hnextB : (H.stage i.succ).length ≤ B.length := by
      have he : i.succ = (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 1)).castSucc :=
        Fin.ext rfl
      rw [he]
      exact (stageB _).1
    have hcut := cutoffEq eta (H.stage i.succ).length (hnextB.trans hBS.1)
    unfold HierarchySegmentColors
    dsimp only
    rw [starredEq i, hnext, hcut]
  let goodU : GoodHierarchy K := by
    exact {
      gamma := P.counterexample.good.gamma
      twoColors := by
        intro i eta heta
        exact P.counterexample.good.twoColors i eta (by rw [← storedEq i]; exact heta)
      avoidance := by
        intro i eta heta c hc
        have hstored := (storedEq i) ▸ heta
        have hold := P.counterexample.good.avoidance i eta hstored hc
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · rw [missingEq]
          exact (Finset.mem_sdiff.mp hold).1
        · by_cases hi : i.val = H.dividerCount
          · have he : i = q := Fin.ext hi
            subst i
            exact lastAvoidance eta hstored c hc
          · rw [earlierSegment i (by omega)]
            exact (Finset.mem_sdiff.mp hold).2
      disjointPairs := by
        intro i eta theta heta htheta hne
        exact P.counterexample.good.disjointPairs i eta theta
          ((storedEq i) ▸ heta) ((storedEq i) ▸ htheta) hne
      uniqueRefresh := by
        intro i
        rw [stageEq i.succ, starredEq i.castSucc, storedEq i.succ]
        exact P.counterexample.good.uniqueRefresh i
      parallelBase := by
        change newSeries.data.kind n = some TashkinovExtensionKind.PE → _
        rw [hkinds n]
        intro hpe
        change ¬ TreeColorSetMinusClosed G mu baseU.core
            ((HierarchyStoredColorsAt K 0).biUnion (P.counterexample.good.gamma 0)) ∧ _
        rw [hcore, hclosure, storedEq 0, hTnEq]
        exact P.counterexample.good.parallelBase hpe
      minusClosed := by
        intro i
        rw [stageEq i.succ, storedEq i.succ]
        exact P.counterexample.good.minusClosed i }
  have hnotElementary : ¬ ColoredVertexSetElementary G mu (TreeSequenceVertexSet U) := by
    exact @helper_hnotElementary_940 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
        (@alpha) (@j) (@hyB) (@hay) (@haB) (@U) (@hUlast) (@hBU)
  let CU : HierarchyCounterexample baseU :=
    { positive := P.counterexample.positive
      hierarchy := K
      good := goodU
      maximum := hMP
      notElementary := hnotElementary }
  -- The possibly internal first attachment lies before this candidate suffix.
  have hpU : HierarchyPathNumber K ≤ j - 1 := by as_aux_lemma =>
    clear * - K starredEq hUpath hXLen hBLen hSUstrict hBS hjlow
    let candidates := (Finset.Icc 1 (U.length - A.length)).filter fun i =>
      ∀ r : Fin U.length, A.length + i ≤ r.val →
        G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ)
    have hm : j - 1 ∈ candidates := by
      exact @helper_hm_964 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@j) (@hjlow)
          (@hBLen) (@hXLen) (@S) (@U) (@hBS) (@hSUstrict) (@hUpath) (@newInput) (@newSeries)
    have hn : candidates.Nonempty := ⟨j - 1, hm⟩
    unfold HierarchyPathNumber
    dsimp only
    rw [starredEq (Fin.last H.dividerCount)]
    change (if h : candidates.Nonempty then candidates.min' h else U.length - A.length) ≤ j - 1
    rw [dite_eq_left hn]
    exact Finset.min'_le candidates (j - 1) hm
  have hless : HierarchyCounterexampleLess (HierarchyCounterexampleMeasure CU)
      (HierarchyCounterexampleMeasure P.counterexample) := by
    apply Or.inl
    change HierarchyPathNumber K < HierarchyPathNumber H
    rw [hpOld]
    omega
  exact P.minimumContext.lexicographicMinimality CU rfl rfl hless

private theorem helper_continuation_2763.{u_1, u_2} :
    helperContinuation2763Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx P alpha beta H R mu n Tn q A j hpathLower B X
      y trans hpOld hjlow coreA hBLen hXLen hBT hBXLen hXshort hyB hay haB haChoice hba hbGamma hab
      firstMem firstBound exceptional S U hBS hSU hSUstrict hUlast hUcolors hUpath hScorner hST hAU
      hBU hAUstrict newInput newSeries hgen htrees hstored hedges hkinds hproper hone hstable
      roundsPositive above strict below generating hseries RU baseU hcore hclosure hMP hTnEq
      hstoredEq stageA stageU stageB hdivB prefixEq newStage newStageOld newStageLast newStageAt
  have newNested : ∀ i : Fin (H.dividerCount + 1),
      TreeSequenceInitialSegment (newStage i.castSucc) (newStage i.succ) := by
    intro i
    by_cases hi : i.val = H.dividerCount
    · have he : i = q := Fin.ext hi
      rw [he, newStageOld, show q.succ = Fin.last (H.dividerCount + 1) from rfl,
        newStageLast]
      exact stageU q
    · rw [newStageOld, newStageAt i.succ (by change i.val + 1 ≤ H.dividerCount; omega)]
      exact H.nested i
  have newStrict : ∀ i : Fin (H.dividerCount + 1),
      (newStage i.castSucc).length < (newStage i.succ).length := by
    intro i
    by_cases hi : i.val = H.dividerCount
    · have he : i = q := Fin.ext hi
      rw [he, newStageOld, show q.succ = Fin.last (H.dividerCount + 1) from rfl,
        newStageLast]
      exact lt_of_le_of_lt (stageA q).1 hAUstrict
    · rw [newStageOld, newStageAt i.succ (by change i.val + 1 ≤ H.dividerCount; omega)]
      exact H.strict i
  let K : TashkinovHierarchy RU baseU := by
    exact {
      dividerCount := H.dividerCount
      stage := newStage
      baseStage := by
        rw [show newStage 0 = H.stage 0 by simp [newStage], H.baseStage]
        exact hTnEq.symm
      terminalStage := newStageLast
      nested := newNested
      strict := newStrict
      dividerPosition := fun i => ⟨(H.dividerPosition i).val,
        Nat.lt_succ_of_le ((hdivB i).trans hBU.1)⟩
      dividerPositive := H.dividerPositive
      dividerIncreasing := H.dividerIncreasing
      dividerStage := by
        intro i
        rw [newStageAt ⟨i.val + 1, by omega⟩ (Nat.succ_le_of_lt i.isLt)]
        rw [prefixEq (H.dividerPosition i).val (H.dividerPositive i) (hdivB i)]
        exact H.dividerStage i
      coreInsideFirst := by
        rw [hcore]
        by_cases hz : H.dividerCount = 0
        · rw [show newStage ⟨1, by omega⟩ = U by simp [newStage, hz]]
          exact trans coreA hAU
        · rw [newStageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hz)]
          exact H.coreInsideFirst }
  have stageEq (i : Fin (H.dividerCount + 1)) : K.stage i.castSucc = H.stage i.castSucc :=
    newStageOld i
  have starredEq (i : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage K i = HierarchyStarredStage H i := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hcore
    · exact stageEq i.succ
  have storedEq (i : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt K i = HierarchyStoredColorsAt H i := by
    change TashkinovStoredColors newSeries.data n \
        TreeMissingColors mu (HierarchyStarredStage K i) = _
    rw [hstoredEq, starredEq]
    rfl
  have missingEq (i : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors K i = HierarchyStageMissingColors H i := by
    refine Fin.cases ?_ (fun i => ?_) i
    · change TreeMissingColors mu (newSeries.data.tree n.castSucc) = _
      rw [hTnEq]
      rfl
    · change TreeMissingColors mu (K.stage i.succ.castSucc) = _
      rw [stageEq]
      rfl
  have cutoffEq (c : Fin k) (p : ℕ) (hp : p ≤ S.length) :
      min (HierarchyFirstMissingPosition mu U c).val p =
        min (HierarchyFirstMissingPosition mu T c).val p :=
    (HierarchyFirstMissingPositionPrefixCutoff mu S U hSU c p hp).symm.trans
      (HierarchyFirstMissingPositionPrefixCutoff mu S T hST c p hp)
  have ownerBound (eta : Fin k)
      (he : (HierarchyFirstMissingPosition mu T eta).val ≤ B.length) :
      (HierarchyFirstMissingPosition mu U eta).val ≤ B.length := by as_aux_lemma =>
    exact @helper_ownerBound_2434 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@j) (@hBT) (@hBXLen)
        (@hXshort) (@firstMem) (@firstBound) (@U) (@hBU) (@eta) (@he)
  -- Old edges retain their cutoff; appended colors are excluded from each pair.
  have lastAvoidance (eta : Fin k) (heta : eta ∈ HierarchyStoredColorsAt H q)
      (c : Fin k) (hc : c ∈ P.counterexample.good.gamma q eta) :
      c ∉ HierarchySegmentColors K q eta := by as_aux_lemma =>
    clear * - heta hc hUcolors hSU hST hBS hBLen hXLen hXshort hBT
      haChoice hbGamma ownerBound cutoffEq starredEq K H q A mu T U S B
    intro hseg
    unfold HierarchySegmentColors at hseg
    dsimp only at hseg
    rw [show K.stage q.succ = U from K.terminalStage] at hseg
    obtain ⟨r, hrA, hrp, hrc⟩ := (Finset.mem_filter.mp hseg).2
    rw [starredEq q] at hrA
    by_cases hrS : r.val < S.length
    · exact @helper_branch_850 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@S)
        (@U) (@hSU) (@hST) (@cutoffEq) (@eta) (@heta) (@c) (@hc) (@r) (@hrA) (@hrp) (@hrc) (@hrS)
    · have hcolors := hUcolors r (by omega)
      have he : c = alpha ∨ c = beta := by
        rcases hcolors with h | h
        · exact Or.inl (Option.some.inj (hrc.symm.trans h))
        · exact Or.inr (Option.some.inj (hrc.symm.trans h))
      rcases he with he | he
      · subst c
        rcases haChoice with hfree | ⟨theta, htheta, hatheta, hpos⟩
        · exact hfree (Finset.mem_union_left _
            (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩))
        · by_cases het : eta = theta
          · subst theta
            have hb := ownerBound eta hpos
            have hbs := hBS.1
            have hrbefore := (lt_min_iff.mp hrp).1
            omega
          · exact Finset.disjoint_left.mp
              (P.counterexample.good.disjointPairs q eta theta heta htheta het) hc hatheta
      · subst c
        exact hbGamma (Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩)
  exact @helper_continuation_2608 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta) (@j)
      (@hpathLower) (@trans) (@hpOld) (@hjlow) (@coreA) (@hBLen) (@hXLen) (@hBT) (@hyB) (@hay)
      (@haB) (@hba) (@hab) (@exceptional) (@S) (@U) (@hBS) (@hSUstrict) (@hUlast) (@hUpath)
      (@hScorner) (@hAU) (@hBU) (@newInput) (@newSeries) (@hgen) (@htrees) (@hstored) (@hedges)
      (@hkinds) (@hproper) (@hone) (@hstable) (@roundsPositive) (@above) (@strict) (@below)
      (@generating) (@hseries) (@baseU) (@hcore) (@hclosure) (@hMP) (@hTnEq) (@stageB) (@hdivB)
      (@prefixEq) (@newStageLast) (@newStageAt) (@newNested) (@newStrict) (@stageEq) (@starredEq)
      (@storedEq) (@missingEq) (@cutoffEq) (@lastAvoidance)

private theorem componentIntersectionFromSpliceFacts.{u_1, u_2} :
    componentIntersectionFromSpliceFactsStatement.{u_1, u_2} := by
  classical
  open scoped Sym2 in
    intro «V» «E» «inst» «inst» «inst» «inst» «G» «k» «e0» «input» «T» «phi» «ett» «base» «C» «ctx»
        «P» «alpha» «beta» «H» «R» «mu» «n» «Tn» «q» «A» «j» «hintersection» «hjdef» «hpathLower»
        «hpathUpper» «ell» «B» «X» «y» «reflSeg» «trans» «common» «sameLast» «hAold» «hpOld» «hell»
        «hjlow» «hjhigh» «chain» «starNext» «hAT» «lastZero» «lastPositive» «coreA» «hTnCore» «hTnA»
        «prefixT» «prefixLen» «hBLen» «hXLen» «hBT» «hXT» «hAB» «hBX» «hAX» «hTnB» «hTnX» «hBXLen»
        «hXshort» «hyX» «hyB» «hay» «haB» «haChoice» «hba» «hbB» «hbGamma» «hbUnused» «hbChoice»
        «hab» «missingMono» «haX» «hbX» «equalSeg» «firstLe» «firstMem» «firstBound» «stableClosed»
        «nonparallelClosed» «hmod» «exceptional»
    have splice : ∃ (S U : TreeSequence G e0),
        TreeSequenceInitialSegment B S ∧ TreeSequenceInitialSegment S X ∧
        TreeSequenceInitialSegment S U ∧ S.length < U.length ∧
        TashkinovAugmentationSequence mu S U ∧
        U.vertex (Fin.last U.length) = y ∧
        (∀ r : Fin U.length, S.length ≤ r.val →
          mu (U.edge r) = some alpha ∨ mu (U.edge r) = some beta) ∧
        (∀ r : Fin U.length, X.length ≤ r.val →
          G.ends (U.edge r) = s(U.vertex r.castSucc, U.vertex r.succ)) ∧
        (H.dividerCount = 0 → j = 2 →
          R.series.data.kind n ≠ some TashkinovExtensionKind.PE → S = X) := by as_aux_lemma =>
      by_cases hmeet : ∃ u ∈ TreeSequenceVertexSet B,
          Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y)
      · exact @helper_branch_567 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@beta) (@j) (@reflSeg) (@hBLen) (@hXLen) (@hBX) (@hBXLen) (@hyB) (@haB)
          (@hbB) (@hab) (@exceptional) (@hmeet)
      · exact @helper_branch_578 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@beta) (@j) (@hintersection) (@reflSeg) (@trans) (@hBX) (@hBXLen) (@hyX)
          (@hab) (@haX) (@hbX) (@hmeet)
    obtain ⟨S, U, hBS, hSX, hSU, hSUstrict, hSUaug, hUlast, hUcolors,
      hUpath, hScorner⟩ := splice
    have hST := trans hSX hXT
    have hAS := trans hAB hBS
    have hAU := trans hAS hSU
    have hBU := trans hBS hSU
    have hAUstrict : A.length < U.length := lt_of_le_of_lt hAS.1 hSUstrict
    have hTnS := trans hTnB hBS
    have hTnU := trans hTnS hSU
    have hTnUstrict : Tn.length < U.length := lt_of_le_of_lt hTnS.1 hSUstrict
    -- Retain the actual last-series route before certifying the new terminal tree.
    have hroute :
        (R.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence mu Tn U) ∨
        ((R.series.data.kind n = some TashkinovExtensionKind.SE ∨
            R.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            R.series.data.connectingEdges n = {f} ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence mu seed U) := by as_aux_lemma =>
      rcases P2813_T1_TerminalRoute G k e0 P.corresponding.replacementInput T mu R
        with ⟨hpe, haug⟩ | ⟨hkind, f, seed, hedges, hadjoin, hinc, hcolor, haug⟩
      · exact Or.inl ⟨hpe,
          (TashkinovAugmentationSequenceRestrict mu Tn S T haug hTnS hST).trans hSUaug⟩
      · exact @helper_branch_636 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha) (@beta) (@j)
          (@hpathLower) (@trans) (@common) (@hpOld) (@chain) (@lastZero) (@lastPositive) (@hBLen)
          (@hXLen) (@hBXLen) (@hba) (@hab) (@exceptional) (@S) (@U) (@hBS) (@hSUaug) (@hScorner)
          (@hST) (@hAS) (@hkind) (@f) (@seed) (@hedges) (@hadjoin) (@haug)
    obtain ⟨corr⟩ := hmod.2.2 U hTnU hTnUstrict hroute
    have hMP := MaximumPropertyTransport G k e0 R mu hmod U corr P.maximum
    obtain ⟨baseU, hcore, hclosure, hsupport⟩ := HierarchyBaseCorrespondingTransport
      G k e0 P.corresponding.replacementInput T U mu R corr P.replacementBase
    have correspondenceData := corr.terminalData
    rcases corr with ⟨newInput, newSeries, newETT, hround, hseries, hgen,
      htrees, hstored, hedges, hkinds, hproper, hone, hstable⟩
    rcases newETT with ⟨rounds, roundsPositive, replacementSeries,
      above, strict, below, generating⟩
    cases hround
    have hseriesEq : replacementSeries = newSeries := eq_of_heq hseries
    cases hseriesEq
    let RU : ExtendedTashkinovTree G k e0 newInput U mu :=
      { rounds := R.rounds
        roundsPositive := roundsPositive
        series := newSeries
        abovePenultimate := above
        strictAbovePenultimate := strict
        belowFinal := below
        generatingColoring := generating }
    change HierarchyBase RU mu at baseU
    change MaximumProperty RU at hMP
    have hTnEq : newSeries.data.tree n.castSucc = Tn := by
      exact correspondenceData.1
    have hstoredEq : TashkinovStoredColors newSeries.data n =
        TashkinovStoredColors R.series.data n := by
      exact correspondenceData.2.2
    have stageA (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (H.stage i.castSucc) A := by
      by_cases hz : H.dividerCount = 0
      · have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
        rw [hi]
        simpa only [Fin.castSucc_zero, H.baseStage] using hTnA
      · rw [lastPositive hz]
        exact chain H.dividerCount (by omega) i.castSucc
          (Nat.le_of_lt_succ i.isLt)
    have stageU (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (H.stage i.castSucc) U := trans (stageA i) hAU
    have stageB (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (H.stage i.castSucc) B := trans (stageA i) hAB
    have hdivB (i : Fin H.dividerCount) : (H.dividerPosition i).val ≤ B.length := by
      have hl := congrArg TreeSequence.length (H.dividerStage i)
      change (H.stage ⟨i.val + 1, by omega⟩).length = (H.dividerPosition i).val at hl
      have hs := (stageB i.succ).1
      change (H.stage ⟨i.val + 1, by omega⟩).length ≤ B.length at hs
      omega
    have prefixEq (p : ℕ) (hp : 1 ≤ p) (hpB : p ≤ B.length) :
        TreeSequencePrefix U p hp (hpB.trans hBU.1) =
          TreeSequencePrefix T p hp (hpB.trans hBT.1) := by
      unfold TreeSequencePrefix
      congr
      · funext i
        have hu := hBU.2.1 (Fin.castLE (Nat.succ_le_succ hpB) i)
        have ht := hBT.2.1 (Fin.castLE (Nat.succ_le_succ hpB) i)
        exact hu.trans ht.symm
      · funext i
        have hu := hBU.2.2 (Fin.castLE hpB i)
        have ht := hBT.2.2 (Fin.castLE hpB i)
        exact hu.trans ht.symm
    -- Only the terminal hierarchy stage changes.
    let newStage : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
      fun i => if i.val = H.dividerCount + 1 then U else H.stage i
    have newStageOld (i : Fin (H.dividerCount + 1)) :
        newStage i.castSucc = H.stage i.castSucc := by
      simp only [newStage, Fin.val_castSucc, ite_eq_right (Nat.ne_of_lt i.isLt)]
    have newStageLast : newStage (Fin.last (H.dividerCount + 1)) = U := by
      simp only [newStage, Fin.val_last, ite_true]
    have newStageAt (i : Fin (H.dividerCount + 2)) (hi : i.val ≤ H.dividerCount) :
        newStage i = H.stage i := by
      simp only [newStage, ite_eq_right (by omega : i.val ≠ H.dividerCount + 1)]
    exact @helper_continuation_2763 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@alpha)
        (@beta) (@j) (@hpathLower) (@trans) (@hpOld) (@hjlow) (@coreA) (@hBLen) (@hXLen) (@hBT)
        (@hBXLen) (@hXshort) (@hyB) (@hay) (@haB) (@haChoice) (@hba) (@hbGamma) (@hab) (@firstMem)
        (@firstBound) (@exceptional) (@S) (@U) (@hBS) (@hSU) (@hSUstrict) (@hUlast) (@hUcolors)
        (@hUpath) (@hScorner) (@hST) (@hAU) (@hBU) (@hAUstrict) (@newInput) (@newSeries) (@hgen)
        (@htrees) (@hstored) (@hedges) (@hkinds) (@hproper) (@hone) (@hstable) (@roundsPositive)
        (@above) (@strict) (@below) (@generating) (@hseries) (@baseU) (@hcore) (@hclosure) (@hMP)
        (@hTnEq) (@hstoredEq) (@stageA) (@stageU) (@stageB) (@hdivB) (@prefixEq) (@newStageOld)
        (@newStageLast) (@newStageAt)

private theorem componentIntersectionFromMissingColors.{u_1, u_2} :
    componentIntersectionFromMissingColorsStatement.{u_1, u_2} := by
  classical
  open scoped Sym2 in
    intro «V» «E» «inst» «inst» «inst» «inst» «G» «k» «e0» «input» «T» «phi» «ett» «base» «C» «ctx»
        «P» «alpha» «beta» «H» «R» «mu» «n» «Tn» «q» «A» «j» «hintersection» «hjdef» «hpathLower»
        «hpathUpper» «ell» «B» «X» «y» «reflSeg» «trans» «common» «sameLast» «hAold» «hpOld» «hell»
        «hjlow» «hjhigh» «chain» «starNext» «hAT» «lastZero» «lastPositive» «coreA» «hTnCore» «hTnA»
        «prefixT» «prefixLen» «hBLen» «hXLen» «hBT» «hXT» «hAB» «hBX» «hAX» «hTnB» «hTnX» «hBXLen»
        «hXshort» «hyX» «hyB» «hay» «haB» «haChoice» «hba» «hbB» «hbGamma» «hbUnused» «hbChoice»
        «hab»
    have missingMono {S U : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U) :
        TreeMissingColors mu S ⊆ TreeMissingColors mu U := by
      exact @helper_missingMono_2274 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@S)
          (@U) (@hSU)
    have haX : alpha ∈ TreeMissingColors mu X := missingMono hBX haB
    have hbX : beta ∈ TreeMissingColors mu X := missingMono hBX hbB
    have equalSeg {S U : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U) (hlen : S.length = U.length) :
        S = U := by as_aux_lemma =>
      exact @helper_equalSeg_2078 (@V) (@E) (@G) (@e0) (@S) (@U) (@hSU) (@hlen)
    have firstLe (W : TreeSequence G e0) (c : Fin k)
        (i : Fin (W.length + 1)) (hi : c ∈ MissingColors G mu (W.vertex i)) :
        (HierarchyFirstMissingPosition mu W c).val ≤ i.val := by
      exact TreeSequenceFirstMissingPositionLe hi
    have firstMem (W : TreeSequence G e0) (c : Fin k)
        (hlt : (HierarchyFirstMissingPosition mu W c).val < W.length) :
        c ∈ MissingColors G mu (W.vertex (HierarchyFirstMissingPosition mu W c)) := by
      exact TreeSequenceFirstMissingPositionMem hlt
    have firstBound {W Z : TreeSequence G e0}
        (hWT : TreeSequenceInitialSegment W Z) (c : Fin k)
        (hc : c ∈ TreeMissingColors mu W) :
        (HierarchyFirstMissingPosition mu Z c).val ≤ W.length := by
      exact TreeSequenceFirstMissingPositionLePrefix hWT hc
    have stableClosed (W : TreeSequence G e0) (D : Finset (Fin k))
        (rho sigma : PartialEdgeColoring E k)
        (hp : IsProperEdgeColoring G rho) (ho : IsOneEdgeUncolored rho e0)
        (hps : IsProperEdgeColoring G sigma) (hos : IsOneEdgeUncolored sigma e0)
        (hst : StableColoring W D rho sigma)
        (hcl : ColoredVertexSetClosed G rho (TreeSequenceVertexSet W)) :
        ColoredVertexSetClosed G sigma (TreeSequenceVertexSet W) := by as_aux_lemma =>
      exact StableColoring.closed W D rho sigma hp ho hps hos hcl hst
    have nonparallelClosed
        (hk : R.series.data.kind n ≠ some TashkinovExtensionKind.PE) :
        ColoredVertexSetClosed G mu (TreeSequenceVertexSet Tn) := by as_aux_lemma =>
      clear * - R n Tn mu hk stableClosed
      have step := R.series.certified n
      generalize hn : n = z at step
      cases step with
      | initial =>
          exact @helper_branch_397 (@V) (@E) inferInstance inferInstance inferInstance
              inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
              (@hn)
      | SE i hp ho hc hnc hnr choice halt hcol hstored hedges hkind
          hvertex houtside hdelta hgamma seed hadjoin hclosure hordered hstrict =>
              exact @helper_branch_402 (@V) (@E) inferInstance inferInstance inferInstance
                  inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
                  (@P) (@stableClosed) (@i) (@hp) (@ho) (@hc) (@choice) (@hcol) (@hn)
      | PE i hp ho hc hnc hnr choice halt gamma hgamma second hps hos hst
          exit hcol hproper hone hstored hedges hkind hvertex houtside hdelta
          hgammaEq hclosure hordered hstrict =>
        exfalso
        exact hk (hn.symm ▸ hkind)
      | RE i hp ho hc hnc available hcol hstored hedges hkind hvertex
          houtside hdelta hgamma seed hadjoin hclosure hordered hstrict =>
              exact @helper_branch_419 (@V) (@E) inferInstance inferInstance inferInstance
                  inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx)
                  (@P) (@i) (@hc) (@hcol) (@hn)
    have hmod : ModColoring R mu := by as_aux_lemma =>
      clear * - P R mu
      apply Td G k e0 P.corresponding.replacementInput T mu R P.maximum
        P.counterexample.positive P.minimumContext.lowerRung mu
        P.minimumContext.proper P.minimumContext.oneEdgeUncolored
      rw [← R.generatingColoring]
      exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
    -- At the nonparallel zero-divider boundary, the prescribed seed must survive.
    have exceptional : H.dividerCount = 0 → j = 2 →
        R.series.data.kind n ≠ some TashkinovExtensionKind.PE →
        ¬ ∃ u ∈ TreeSequenceVertexSet B,
          Sum.inl u ∈ TwoColorComponent G mu alpha beta (Sum.inl y) := by
      exact @helper_exceptional_436 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
          (@alpha) (@beta) (@j) (@trans) (@common) (@hpOld) (@hAT) (@lastZero) (@hBLen) (@hXLen)
          (@hBT) (@hXT) (@hAB) (@hBXLen) (@hXshort) (@hyB) (@hay) (@haB) (@hba) (@hbB) (@hab)
          (@missingMono) (@equalSeg) (@firstMem) (@firstBound) (@nonparallelClosed)
    -- Choose the shorter base unless the component first meets its new last vertex.
    exact @componentIntersectionFromSpliceFacts (@«V») (@«E») inferInstance inferInstance
        inferInstance inferInstance (@«G») (@«k») (@«e0») (@«input») (@«T») (@«phi») (@«ett»)
        (@«base») (@«C») (@«ctx») (@«P») (@«alpha») (@«beta») (@«j») (@«hintersection») (@«hjdef»)
        (@«hpathLower») (@«hpathUpper») (@«reflSeg») (@«trans») (@«common») (@«sameLast») (@«hAold»)
        (@«hpOld») (@«hell») (@«hjlow») (@«hjhigh») (@«chain») (@«starNext») (@«hAT») (@«lastZero»)
        (@«lastPositive») (@«coreA») (@«hTnCore») (@«hTnA») (@«prefixT») (@«prefixLen») (@«hBLen»)
        (@«hXLen») (@«hBT») (@«hXT») (@«hAB») (@«hBX») (@«hAX») (@«hTnB») (@«hTnX») (@«hBXLen»)
        (@«hXshort») (@«hyX») (@«hyB») (@«hay») (@«haB») (@«haChoice») (@«hba») (@«hbB»)
        (@«hbGamma») (@«hbUnused») (@«hbChoice») (@«hab») (@«missingMono») (@«haX») (@«hbX»)
        (@«equalSeg») (@«firstLe») (@«firstMem») (@«firstBound») (@«stableClosed»)
        (@«nonparallelClosed») (@«hmod») (@«exceptional»)

theorem HierarchySituationThreeComponentIntersectionShortening
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k)
    (hpathLower : 2 <= HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (halpha :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)) /\
        alpha ∈ TreeMissingColors P.coloring B /\
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          exists eta : Fin k, eta ∈ D /\
            alpha ∈ P.counterexample.good.gamma q eta /\
            (HierarchyFirstMissingPosition P.coloring T eta).val <=
              B.length))
    (hbeta :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let j := HierarchyPathNumber C.hierarchy
      let A := HierarchyStarredStage H q
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      let tailUsedThroughJ :=
        (Finset.univ : Finset (Fin k)).filter fun c =>
          exists r : Fin T.length,
            A.length <= r.val /\ r.val < A.length + j /\
              P.coloring (T.edge r) = some c
      beta ≠ alpha /\
        beta ∈ TreeMissingColors P.coloring B /\
        beta ∉ Gamma /\ beta ∉ tailUsedThroughJ /\
        (beta ∉ baseExtraMissing ∪ D ∨
          beta ∈ D /\
            Disjoint (P.counterexample.good.gamma q beta ∪ {beta})
              tailUsedThroughJ))
    (hintersection :
      let j := HierarchyPathNumber C.hierarchy
      let X := HierarchyFullTailPrefix C (j - 1)
      ∃ u ∈ TreeSequenceVertexSet X,
        Sum.inl u ∈ TwoColorComponent G P.coloring alpha beta
          (Sum.inl (T.vertex (Fin.last T.length)))) :
    False := by
  classical
  open scoped Sym2 in
    let H := P.counterexample.hierarchy
    let R := P.corresponding.replacementETT
    let mu := P.coloring
    let n := Fin.last R.rounds
    let Tn := R.series.data.tree n.castSucc
    let q := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    generalize hjdef : HierarchyPathNumber C.hierarchy = j at hpathLower hpathUpper
    rw [hjdef] at halpha hbeta hintersection
    let ell := HierarchyFullTailLength C
    let B := HierarchyFullTailPrefix C (j - 2)
    let X := HierarchyFullTailPrefix C (j - 1)
    let y := T.vertex (Fin.last T.length)
    have reflSeg (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
      ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    have trans {S U W : TreeSequence G e0}
        (hSU : TreeSequenceInitialSegment S U)
        (hUW : TreeSequenceInitialSegment U W) :
        TreeSequenceInitialSegment S W := by as_aux_lemma =>
      exact @SharedFacts.ShorteningTransport.trans (@V) (@E) (@G) (@e0) (@S) (@U) (@W) (@hSU) (@hUW)
    have common {S U W : TreeSequence G e0}
        (hSW : TreeSequenceInitialSegment S W)
        (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
        TreeSequenceInitialSegment S U := by
      exact hUW.of_common_extension hSW hlen
    have sameLast : ∀ {a b : ℕ}
        (s : Fin (a + 2) → TreeSequence G e0)
        (t : Fin (b + 2) → TreeSequence G e0)
        (u v : TreeSequence G e0), a = b → HEq s t → u = v →
        Fin.cases (motive := fun _ => TreeSequence G e0)
          u (fun i : Fin a => s i.succ.castSucc) (Fin.last a) =
          Fin.cases (motive := fun _ => TreeSequence G e0)
            v (fun i : Fin b => t i.succ.castSucc) (Fin.last b) := by
      exact @helper_sameLast_1457 (@V) (@E) (@G) (@e0)
    have hAold : HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount) = A :=
      sameLast _ _ _ _ P.sameGood.1.2.1 P.sameGood.1.2.2.1 P.sameGood.1.1
    have hpOld : HierarchyPathNumber H = j := by as_aux_lemma =>
      exact @helper_hAold_2232 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@j) (@hjdef)
          (@hAold)
    have hell : ell = T.length - A.length := by
      dsimp [ell, HierarchyFullTailLength]
      rw [hAold]
    have hjlow : 2 ≤ j := hpathLower
    have hjhigh : j < ell := hpathUpper
    have chain : ∀ (b : ℕ) (hb : b < H.dividerCount + 2)
        (a : Fin (H.dividerCount + 2)), a.val ≤ b →
        TreeSequenceInitialSegment (H.stage a) (H.stage ⟨b, hb⟩) := by as_aux_lemma =>
      clear * - H reflSeg trans
      intro b
      induction b with
      | zero =>
          exact @helper_branch_221 (@V) (@E) inferInstance inferInstance inferInstance
              inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
              (@reflSeg)
      | succ b ih =>
          exact @helper_branch_226 (@V) (@E) inferInstance inferInstance inferInstance
              inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P)
              (@reflSeg) (@trans) (@b) (@ih)
    have starNext (i : Fin (H.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage H i) (H.stage i.succ) :=
      Fin.cases H.coreInsideFirst (fun i => H.nested i.succ) i
    have hAT : TreeSequenceInitialSegment A T := by
      simpa only [q, Fin.succ_last, H.terminalStage] using starNext q
    have lastZero (hz : H.dividerCount = 0) : A = P.replacementBase.core := by
      simp [A, q, HierarchyStarredStage, hz, Fin.last]
    have lastPositive (hz : H.dividerCount ≠ 0) :
        A = H.stage ⟨H.dividerCount, by omega⟩ := by
      exact @helper_lastPositive_240 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@j)
          (@hz)
    have coreA : TreeSequenceInitialSegment P.replacementBase.core A := by
      exact H.coreInitialSegmentOfStarredStage (Fin.last _)
    have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
      exact P.replacementBase.lastRoundInitialSegmentCore
    have hTnA := trans hTnCore coreA
    have prefixT (r : ℕ) : TreeSequenceInitialSegment (HierarchyFullTailPrefix C r) T :=
      ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
    have prefixLen (r : ℕ) (hr : r ≤ ell) :
        (HierarchyFullTailPrefix C r).length = A.length + r := by as_aux_lemma =>
      exact @helper_prefixLen_2218 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@P) (@hAold) (@hell)
          (@hAT) (@r) (@hr)
    have hBLen : B.length = A.length + (j - 2) := prefixLen _ (by omega)
    have hXLen : X.length = A.length + (j - 1) := prefixLen _ (by omega)
    have hBT := prefixT (j - 2)
    have hXT := prefixT (j - 1)
    have hAB : TreeSequenceInitialSegment A B := common hAT hBT (by omega)
    have hBX : TreeSequenceInitialSegment B X := common hBT hXT (by omega)
    have hAX := trans hAB hBX
    have hTnB := trans hTnA hAB
    have hTnX := trans hTnB hBX
    have hBXLen : X.length = B.length + 1 := by omega
    have hXshort : X.length < T.length := by omega
    have hyX : y ∉ TreeSequenceVertexSet X := by as_aux_lemma =>
      clear * - hXT hXshort
      intro hy
      obtain ⟨i, hi⟩ : ∃ i, X.vertex i = y := by
        simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hy
      have hv := T.vertex_injective ((hXT.2.1 i).trans hi)
      have hh := congrArg Fin.val hv
      change i.val = T.length at hh
      have hiBound := i.isLt
      change i.val < X.length + 1 at hiBound
      omega
    have hyB : y ∉ TreeSequenceVertexSet B :=
      fun hy => hyX (TreeSequenceInitialSegmentVertexSetSubset hBX hy)
    rcases halpha with ⟨hay, haB, haChoice⟩
    rcases hbeta with ⟨hba, hbB, hbGamma, hbUnused, hbChoice⟩
    have hab : alpha ≠ beta := Ne.symm hba
    exact @componentIntersectionFromMissingColors (@«V») (@«E») inferInstance inferInstance
        inferInstance inferInstance (@«G») (@«k») (@«e0») (@«input») (@«T») (@«phi») (@«ett»)
        (@«base») (@«C») (@«ctx») (@«P») (@«alpha») (@«beta») (@«j») (@«hintersection») (@«hjdef»)
        (@«hpathLower») (@«hpathUpper») (@«reflSeg») (@«trans») (@«common») (@«sameLast») (@«hAold»)
        (@«hpOld») (@«hell») (@«hjlow») (@«hjhigh») (@«chain») (@«starNext») (@«hAT») (@«lastZero»)
        (@«lastPositive») (@«coreA») (@«hTnCore») (@«hTnA») (@«prefixT») (@«prefixLen») (@«hBLen»)
        (@«hXLen») (@«hBT») (@«hXT») (@«hAB») (@«hBX») (@«hAX») (@«hTnB») (@«hTnX») (@«hBXLen»)
        (@«hXshort») (@«hyX») (@«hyB») (@«hay») (@«haB») (@«haChoice») (@«hba») (@«hbB»)
        (@«hbGamma») (@«hbUnused») (@«hbChoice») (@«hab»)

end GoldbergSeymour

end
