/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleTransport


public import LeanPool.GoldbergSeymour.ChangeLemma
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseTwoData
public import LeanPool.GoldbergSeymour.HierarchySituationTwoCaseTwoExclusions
public import LeanPool.GoldbergSeymour.HierarchySituationTwoReorderedTreesCertified
public import LeanPool.GoldbergSeymour.NineN

/-!
# Hierarchy Situation Two Subcase Two One Nonexceptional

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperHendsTerminal1091Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [DecidableEq V]
   [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx) (beta : Fin k),
  TwoColorComponent G phi beta D.alpha
     (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
    TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.terminalVertexIndex)) →
  let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
  let yt : V := T.vertex D.terminalVertexIndex;
  let graph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi beta D.alpha;
  ∀ (a b : V ⊕ E),
  (
  ∀ (w : V),
  Sum.inl w ∈ TwoColorComponent G phi beta D.alpha (Sum.inl vb) →
  @SimpleGraph.degree (Sum V E) graph (@Sum.inl V E w)
     (@Fintype.ofFinite
      (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w)))
      (@Subtype.finite (Sum V E)
       (@Finite.instSum V E (@Finite.of_fintype V inst) (@Finite.of_fintype E inst_1))
       (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w))))) ≤
    (1 : ℕ) →
  Sum.inl w = a ∨ Sum.inl w = b) →
  (
  ∀ (w : V),
  D.alpha ∈ MissingColors G phi w →
  @SimpleGraph.degree (Sum V E) graph (@Sum.inl V E w)
    (@Fintype.ofFinite
     (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w)))
     (@Subtype.finite (Sum V E)
      (@Finite.instSum V E (@Finite.of_fintype V inst) (@Finite.of_fintype E inst_1))
      (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
       (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w))))) ≤
   (1 : ℕ)) →
  Sum.inl yt = a ∨ Sum.inl yt = b

private noncomputable abbrev helperCStar1926.{u_1, u_2} :
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
  (D :
      HierarchySituationTwoCaseTwoData G k e0 input T phi ett
        base C ctx) →
  (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi
        ett base C ctx D.toHierarchySituationTwoTailData) →
  (corrStar :
      CorrespondingExtendedTashkinovTree G k e0 ett phi
        R.star) →
  MaximumProperty corrStar.replacementETT →
  (baseStar :
      HierarchyBase corrStar.replacementETT phi) →
  (HStar :
      TashkinovHierarchy corrStar.replacementETT
        baseStar) →
  GoodHierarchy HStar →
  HierarchyCounterexample baseStar := by
  classical
  intro V E inst inst_1 inst_2 inst_3 G k e0 input T phi ett base C ctx D R corrStar hstarMP
      baseStar HStar goodStar
  exact (C.transport HStar goodStar hstarMP corrStar.rungAgreement R.starVertexSet);

private abbrev helperContinuation3768Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀ (htail : (2 : ℕ) ≤ ell) (hell : ell = T.length - A.length) (hsum : A.length + ell = T.length)
   (hBlen : B.length = T.length - (2 : ℕ)) (hBT : TreeSequenceInitialSegment B T)
   (R :
    HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
     D.toHierarchySituationTwoTailData)
   (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
   (baseMinus : HierarchyBase corrMinus.replacementETT phi)
   (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
   (hminusCount : HMinus.dividerCount = C.hierarchy.dividerCount)
   (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
   (hstarMP : MaximumProperty corrStar.replacementETT)
   (baseStar : HierarchyBase corrStar.replacementETT phi)
   (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
   (hstarCount : HStar.dividerCount = C.hierarchy.dividerCount)
   (hstarLen : R.star.length = R.minus.length + (1 : ℕ))
   (hminusStar : TreeSequenceInitialSegment R.minus R.star)
   (hminusLen : R.minus.length = B.length + (1 : ℕ)) (hstarLength : R.star.length = T.length)
   (beta : Fin k)
   (hbetaUnused :
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta)
   (hcolorsDistinct : beta ≠ D.alpha)
   (firstMissingMem :
  ∀ (S : TreeSequence G e0) (c : Fin k) (hc : c ∈ TreeMissingColors phi S),
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c)))
   (hbetaT : beta ∈ TreeMissingColors phi T)
   (hbetaFirstBound : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
   (hDnDisjoint : Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn)
   (hcomponentPenultimate :
    TwoColorComponent G phi beta D.alpha
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
     TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)))
   (hBstar : TreeSequenceInitialSegment B R.star)
   (hstarFirstEdge :
  ∀ (r : Fin R.star.length) (hr : (↑r : ℕ) = B.length),
  R.star.edge r = T.edge D.lastEdgeIndex)
   (terminalData :
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
  corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
    ett.series.data.tree n.castSucc ∧
   corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
     ett.series.data.kind n ∧
    TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) =
     Dn)
   (goodStar : GoodHierarchy HStar)
   (hstarStarred : HierarchyStarredStage HStar (Fin.last HStar.dividerCount) = A),
  let ibeta : Fin (B.length + (1 : ℕ)) :=
   (⟨(↑(HierarchyFirstMissingPosition phi T beta) : ℕ), by omega⟩ : Fin (B.length + (1 : ℕ)));
  ∀
   (hibeta :
    Fin.castLE (Nat.succ_le_succ hBT.1) ibeta = HierarchyFirstMissingPosition phi T beta),
  let CStar : HierarchyCounterexample baseStar :=
   (C.transport HStar goodStar hstarMP corrStar.rungAgreement R.starVertexSet);
  ∀
   (ctxStar :
    HierarchyMinimumCounterexampleContext G k e0 corrStar.replacementInput R.star phi
     corrStar.replacementETT baseStar CStar)
   (hprefixStarElementary :
    ColoredVertexSetElementary G phi
     (TreeSequenceVertexSet
      (HierarchyFullTailPrefix CStar (HierarchyFullTailLength CStar - (1 : ℕ))))),
  let iaStar : Fin (R.star.length + (1 : ℕ)) :=
   Fin.castLE (Nat.succ_le_succ hminusStar.1) (Fin.last R.minus.length);
  ∀ (hiaStar : (↑iaStar : ℕ) = R.minus.length)
   (halphaStarVertex : R.star.vertex iaStar = T.vertex D.terminalVertexIndex)
   (halphaFirstStar : HierarchyFirstMissingPosition phi R.star D.alpha = iaStar)
   (hbetaStarBound : (↑(HierarchyFirstMissingPosition phi R.star beta) : ℕ) ≤ B.length)
   (hbetaStarVertex :
    R.star.vertex (HierarchyFirstMissingPosition phi R.star beta) =
     T.vertex (HierarchyFirstMissingPosition phi T beta))
   (hmissingStar :
    beta ∈
      TreeMissingColors phi
       (HierarchyFullTailPrefix CStar (HierarchyFullTailLength CStar - (1 : ℕ))) ∧
     D.alpha ∈
      TreeMissingColors phi
       (HierarchyFullTailPrefix CStar (HierarchyFullTailLength CStar - (1 : ℕ)))),
  False

private abbrev helperContinuation3898Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀ (htail : (2 : ℕ) ≤ ell) (hell : ell = T.length - A.length) (hsum : A.length + ell = T.length)
   (hBlen : B.length = T.length - (2 : ℕ)) (hBT : TreeSequenceInitialSegment B T)
   (halpha :
    D.alpha ∉ TreeMissingColors phi B ∧
     D.alpha ∉ Dn ∧
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some D.alpha)
   (R :
    HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
     D.toHierarchySituationTwoTailData)
   (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
   (baseMinus : HierarchyBase corrMinus.replacementETT phi)
   (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
   (hminusCount : HMinus.dividerCount = C.hierarchy.dividerCount)
   (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
   (hstarMP : MaximumProperty corrStar.replacementETT)
   (baseStar : HierarchyBase corrStar.replacementETT phi)
   (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
   (hstarCount : HStar.dividerCount = C.hierarchy.dividerCount)
   (hstarStages :
  ∀ (j : Fin (HStar.dividerCount + (1 : ℕ))),
  HStar.stage j.castSucc = C.hierarchy.stage (Fin.cast (by omega) j).castSucc)
   (hBminus :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ)))
     R.minus)
   (hstarLen : R.star.length = R.minus.length + (1 : ℕ))
   (hminusStar : TreeSequenceInitialSegment R.minus R.star)
   (hminusLen : R.minus.length = B.length + (1 : ℕ)) (hstarLength : R.star.length = T.length)
   (beta : Fin k) (hbetaMissing : beta ∈ TreeMissingColors phi B)
   (hbetaUnused :
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta)
   (hcolorsDistinct : beta ≠ D.alpha)
   (firstMissingLe :
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ)))
   (hc : c ∈ MissingColors G phi (S.vertex i)),
  HierarchyFirstMissingPosition phi S c ≤ i)
   (firstMissingMem :
  ∀ (S : TreeSequence G e0) (c : Fin k) (hc : c ∈ TreeMissingColors phi S),
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c)))
   (vertexMem :
  ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S)
   (missingMono :
  ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U),
  TreeMissingColors phi S ⊆ TreeMissingColors phi U)
   (hbetaT : beta ∈ TreeMissingColors phi T)
   (hbetaFirstBound : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
   (hDnDisjoint : Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn)
   (hcomponentPenultimate :
    TwoColorComponent G phi beta D.alpha
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
     TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)))
   (hBstar : TreeSequenceInitialSegment B R.star)
   (hstarFirstEdge :
  ∀ (r : Fin R.star.length) (hr : (↑r : ℕ) = B.length),
  R.star.edge r = T.edge D.lastEdgeIndex)
   (terminalData :
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
  corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
    ett.series.data.tree n.castSucc ∧
   corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
     ett.series.data.kind n ∧
    TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) =
     Dn)
   (goodStar : GoodHierarchy HStar)
   (hstarLastIndex :
    Fin.cast
      (by
       first
       | omega
       | (
         have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corrStar
         have := GoldbergSeymour.TreeSequence.positive T
         have := GoldbergSeymour.ExtendedTashkinovTree.roundsPositive ett
         have := GoldbergSeymour.HierarchyCounterexample.positive C
         have := hBT.1
         have := hBminus.1
         have := hminusStar.1
         have := hBstar.1
         try dsimp only [H] at *
         try dsimp only [GoldbergSeymour.HierarchyFullTailLength] at *
         try dsimp only [GoldbergSeymour.HierarchyFullTailPrefix] at *
         try dsimp only [GoldbergSeymour.TreeSequencePrefix] at *
         all_goals omega))
      (Fin.last HStar.dividerCount) =
     q)
   (hstarStarred : HierarchyStarredStage HStar (Fin.last HStar.dividerCount) = A),
  let ibeta : Fin (B.length + (1 : ℕ)) :=
   (⟨(↑(HierarchyFirstMissingPosition phi T beta) : ℕ), by omega⟩ : Fin (B.length + (1 : ℕ)));
  ∀
   (hibeta : Fin.castLE (Nat.succ_le_succ hBT.1) ibeta = HierarchyFirstMissingPosition phi T beta)
   (hbetaAtB : beta ∈ MissingColors G phi (B.vertex ibeta)),
  let CStar : HierarchyCounterexample baseStar :=
   (C.transport HStar goodStar hstarMP corrStar.rungAgreement R.starVertexSet);
  ∀ (hstarPath : HierarchyPathNumber HStar = HierarchyPathNumber H),
  False

private abbrev helperContinuation4102Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀ (htail : (2 : ℕ) ≤ ell) (hell : ell = T.length - A.length) (hsum : A.length + ell = T.length)
   (hBlen : B.length = T.length - (2 : ℕ)) (hBT : TreeSequenceInitialSegment B T)
   (halpha :
    D.alpha ∉ TreeMissingColors phi B ∧
     D.alpha ∉ Dn ∧
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some D.alpha)
   (R :
    HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
     D.toHierarchySituationTwoTailData)
   (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
   (hminusMP : MaximumProperty corrMinus.replacementETT)
   (baseMinus : HierarchyBase corrMinus.replacementETT phi)
   (hminusCore : baseMinus.core = base.core) (hminusClosure : baseMinus.closure = base.closure)
   (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
   (hminusCount : HMinus.dividerCount = C.hierarchy.dividerCount)
   (hminusStages :
  ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
  HMinus.stage j.castSucc = C.hierarchy.stage (Fin.cast (by omega) j).castSucc)
   (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
   (hstarMP : MaximumProperty corrStar.replacementETT)
   (baseStar : HierarchyBase corrStar.replacementETT phi) (hstarCore : baseStar.core = base.core)
   (hstarClosure : baseStar.closure = base.closure)
   (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
   (hstarCount : HStar.dividerCount = C.hierarchy.dividerCount)
   (hstarStages :
  ∀ (j : Fin (HStar.dividerCount + (1 : ℕ))),
  HStar.stage j.castSucc = C.hierarchy.stage (Fin.cast (by omega) j).castSucc)
   (hBminus :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ)))
     R.minus)
   (hstarLen : R.star.length = R.minus.length + (1 : ℕ))
   (hminusStar : TreeSequenceInitialSegment R.minus R.star)
   (hminusLen : R.minus.length = B.length + (1 : ℕ)) (hstarLength : R.star.length = T.length)
   (beta : Fin k) (hbetaMissing : beta ∈ TreeMissingColors phi B)
   (hbetaUnused :
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta)
   (hcolorsDistinct : beta ≠ D.alpha)
   (firstMissingLe :
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ)))
   (hc : c ∈ MissingColors G phi (S.vertex i)),
  HierarchyFirstMissingPosition phi S c ≤ i)
   (firstMissingMem :
  ∀ (S : TreeSequence G e0) (c : Fin k) (hc : c ∈ TreeMissingColors phi S),
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c)))
   (vertexMem :
  ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S)
   (missingMono :
  ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U),
  TreeMissingColors phi S ⊆ TreeMissingColors phi U)
   (hbetaT : beta ∈ TreeMissingColors phi T)
   (hbetaFirstBound : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
   (hDnDisjoint : Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn)
   (hcomponentPenultimate :
    TwoColorComponent G phi beta D.alpha
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
     TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)))
   (hminusTerminalAvoidance :
    ∀ eta ∈ HierarchyStoredColorsAt H q,
     Disjoint (C.good.gamma q eta)
      ({c : Fin k |
        ∃ (r : Fin R.minus.length),
         A.length ≤ (↑r : ℕ) ∧
          (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi R.minus eta) : ℕ) R.minus.length ∧
           phi (R.minus.edge r) = some c} :
       Finset (Fin k)))
   (hBstar : TreeSequenceInitialSegment B R.star)
   (hstarFirstEdge :
  ∀ (r : Fin R.star.length) (hr : (↑r : ℕ) = B.length),
  R.star.edge r = T.edge D.lastEdgeIndex)
   (hstarTerminalAvoidance :
    ∀ eta ∈ HierarchyStoredColorsAt H q,
     Disjoint (C.good.gamma q eta)
      ({c : Fin k |
        ∃ (r : Fin R.star.length),
         A.length ≤ (↑r : ℕ) ∧
          (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi R.star eta) : ℕ) R.star.length ∧
           phi (R.star.edge r) = some c} :
       Finset (Fin k)))
   (terminalData :
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U),
  corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
    ett.series.data.tree n.castSucc ∧
   corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
     ett.series.data.kind n ∧
    TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) =
     Dn)
   (copyGood :
    ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
     (baseU : HierarchyBase corr.replacementETT phi) (hcore : baseU.core = base.core)
     (hclosure : baseU.closure = base.closure) (K : TashkinovHierarchy corr.replacementETT baseU)
     (hcount : K.dividerCount = H.dividerCount)
     (hstages :
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  K.stage j.castSucc = H.stage (Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j).castSucc)
     (hBU : TreeSequenceInitialSegment B U)
     (havoid :
      ∀ eta ∈ HierarchyStoredColorsAt H q,
       Disjoint (C.good.gamma q eta)
        ({c : Fin k |
          ∃ (r : Fin U.length),
           A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi U eta) : ℕ) U.length ∧
             phi (U.edge r) = some c} :
         Finset (Fin k))),
     ∃ (goodU : GoodHierarchy K),
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))) (eta : Fin k),
  goodU.gamma j eta = C.good.gamma (Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j) eta),
  False

private abbrev helperContinuation4235Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀ (htail : (2 : ℕ) ≤ ell) (hell : ell = T.length - A.length) (hsum : A.length + ell = T.length)
   (hBlen : B.length = T.length - (2 : ℕ)) (hBT : TreeSequenceInitialSegment B T)
   (halpha :
    D.alpha ∉ TreeMissingColors phi B ∧
     D.alpha ∉ Dn ∧
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some D.alpha)
   (R :
    HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
     D.toHierarchySituationTwoTailData)
   (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
   (hminusMP : MaximumProperty corrMinus.replacementETT)
   (baseMinus : HierarchyBase corrMinus.replacementETT phi)
   (hminusCore : baseMinus.core = base.core) (hminusClosure : baseMinus.closure = base.closure)
   (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
   (hminusCount : HMinus.dividerCount = C.hierarchy.dividerCount)
   (hminusStages :
  ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
  HMinus.stage j.castSucc = C.hierarchy.stage (Fin.cast (by omega) j).castSucc)
   (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
   (hstarMP : MaximumProperty corrStar.replacementETT)
   (baseStar : HierarchyBase corrStar.replacementETT phi) (hstarCore : baseStar.core = base.core)
   (hstarClosure : baseStar.closure = base.closure)
   (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
   (hstarCount : HStar.dividerCount = C.hierarchy.dividerCount)
   (hstarStages :
  ∀ (j : Fin (HStar.dividerCount + (1 : ℕ))),
  HStar.stage j.castSucc = C.hierarchy.stage (Fin.cast (by omega) j).castSucc)
   (hBminus :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ)))
     R.minus)
   (hstarLen : R.star.length = R.minus.length + (1 : ℕ))
   (hminusStar : TreeSequenceInitialSegment R.minus R.star)
   (hstarEdge :
    R.star.edge (Fin.cast (by omega) (Fin.last R.minus.length)) = T.edge R.penultimateEdgeIndex)
   (hminusLen : R.minus.length = B.length + (1 : ℕ)) (hstarLength : R.star.length = T.length)
   (beta : Fin k) (hbetaMissing : beta ∈ TreeMissingColors phi B)
   (hbetaUnused :
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta)
   (hcolorsDistinct : beta ≠ D.alpha)
   (firstMissingLe :
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ)))
   (hc : c ∈ MissingColors G phi (S.vertex i)),
  HierarchyFirstMissingPosition phi S c ≤ i)
   (firstMissingMem :
  ∀ (S : TreeSequence G e0) (c : Fin k) (hc : c ∈ TreeMissingColors phi S),
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c)))
   (vertexMem :
  ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S)
   (missingMono :
  ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U),
  TreeMissingColors phi S ⊆ TreeMissingColors phi U)
   (hbetaT : beta ∈ TreeMissingColors phi T)
   (hbetaFirstBound : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
   (hDnDisjoint : Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn)
   (hcomponentPenultimate :
    TwoColorComponent G phi beta D.alpha
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
     TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)))
   (terminalAvoidance :
    ∀ (U : TreeSequence G e0) (hBU : TreeSequenceInitialSegment B U)
     (hlen : U.length ≤ B.length + (2 : ℕ))
     (hfirstEdge :
  ∀ (r : Fin U.length),
  (↑r : ℕ) = B.length →
  U.edge r = T.edge D.lastEdgeIndex)
     (hsecondEdge :
  ∀ (r : Fin U.length),
  (↑r : ℕ) = B.length + (1 : ℕ) →
  U.edge r = T.edge R.penultimateEdgeIndex),
     ∀ eta ∈ HierarchyStoredColorsAt H q,
      Disjoint (C.good.gamma q eta)
       ({c : Fin k |
         ∃ (r : Fin U.length),
          A.length ≤ (↑r : ℕ) ∧
           (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi U eta) : ℕ) U.length ∧
            phi (U.edge r) = some c} :
        Finset (Fin k)))
   (hminusFirstEdge :
  ∀ (r : Fin R.minus.length) (hr : (↑r : ℕ) = B.length),
  R.minus.edge r = T.edge D.lastEdgeIndex)
   (hminusTerminalAvoidance :
    ∀ eta ∈ HierarchyStoredColorsAt H q,
     Disjoint (C.good.gamma q eta)
      ({c : Fin k |
        ∃ (r : Fin R.minus.length),
         A.length ≤ (↑r : ℕ) ∧
          (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi R.minus eta) : ℕ) R.minus.length ∧
           phi (R.minus.edge r) = some c} :
       Finset (Fin k)))
   (hBstar : TreeSequenceInitialSegment B R.star),
  False

private abbrev transferredGoodHierarchyConstructorType.{u_1, u_2} (V : Type u_1) (E : Type u_2) :=
    open scoped Classical in
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
  (D :
      HierarchySituationTwoCaseTwoData G k e0 input T phi ett
        base C ctx) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) :=
    Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) :=
    TashkinovStoredColors ett.series.data n;
  (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi
        ett base C ctx D.toHierarchySituationTwoTailData) →
  (corrMinus :
      CorrespondingExtendedTashkinovTree G k e0 ett phi
        R.minus) →
  (baseMinus :
      HierarchyBase corrMinus.replacementETT phi) →
  TashkinovHierarchy corrMinus.replacementETT
      baseMinus →
  (corrStar :
      CorrespondingExtendedTashkinovTree G k e0 ett
        phi R.star) →
  (baseStar :
      HierarchyBase corrStar.replacementETT phi) →
  TashkinovHierarchy corrStar.replacementETT
      baseStar →
  Fin k →
  (U : TreeSequence G e0) →
  (corr :
      CorrespondingExtendedTashkinovTree G k
        e0 ett phi U) →
  (baseU :
      HierarchyBase corr.replacementETT
        phi) →
  baseU.core = base.core →
  baseU.closure = base.closure →
  (K :
      TashkinovHierarchy
        corr.replacementETT baseU) →
  (hcount :
      K.dividerCount =
        H.dividerCount) →
  (∀
      eta ∈
        HierarchyStoredColorsAt
          H q,
      Disjoint
        (C.good.gamma q eta)
        ({c : Fin k |
            ∃ (r :
              Fin U.length),
              A.length ≤
                  (↑r : ℕ) ∧
                (↑r : ℕ) <
                    min
                      (↑(HierarchyFirstMissingPosition
                            phi
                            U
                            eta) :
                        ℕ)
                      U.length ∧
                  phi
                      (U.edge
                        r) =
                    some c} :
          Finset (Fin k))) →
  let index :
  Fin
      (K.dividerCount +
        (1 : ℕ)) →
  Fin
    (H.dividerCount +
      (1 : ℕ)) :=
    fun
      (j :
        Fin
          (K.dividerCount +
            (1 : ℕ))) ↦
    Fin.cast
      (by
        have :=
          GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement
            corr
        have :=
          GoldbergSeymour.TreeSequence.positive
            T
        have :=
          GoldbergSeymour.TreeSequence.positive
            U
        omega)
      j;
  let _ :
  Fin
      (K.dividerCount +
        (1 : ℕ)) →
  Fin k →
  Finset (Fin k) :=
    fun
      (j :
        Fin
          (K.dividerCount +
            (1 : ℕ)))
      (eta : Fin k) ↦
    C.good.gamma (index j)
      eta;
  corr.replacementETT.series.data.tree
          (Fin.last
              corr.replacementETT.rounds).castSucc =
        ett.series.data.tree
          n.castSucc ∧
      corr.replacementETT.series.data.kind
            (Fin.last
              corr.replacementETT.rounds) =
          ett.series.data.kind
            n ∧
        TashkinovStoredColors
            corr.replacementETT.series.data
            (Fin.last
              corr.replacementETT.rounds) =
          Dn →
  (
  ∀
     (j :
       Fin
         (K.dividerCount +
           (1 : ℕ))),
  K.stage j.castSucc =
    H.stage
      (index
          j).castSucc) →
  (
  ∀
     (j :
       Fin
         (K.dividerCount +
           (1 : ℕ))),
  HierarchyStarredStage
      K j =
    HierarchyStarredStage
      H (index j)) →
  (
  ∀
     (j :
       Fin
         (K.dividerCount +
           (1 : ℕ))),
  HierarchyStoredColorsAt
      K j =
    HierarchyStoredColorsAt
      H (index j)) →
  (
  ∀
     (j :
       Fin
         (K.dividerCount +
           (1 : ℕ))),
  HierarchyStageMissingColors
      K j =
    HierarchyStageMissingColors
      H
      (index j)) →
  (
  ∀
     (i :
       Fin
         K.dividerCount)
     (eta : Fin k),
  HierarchySegmentColors
      K
      i.castSucc
      eta =
    HierarchySegmentColors
      H
      (index
        i.castSucc)
      eta) →
  index
        (Fin.last
          K.dividerCount) =
      q →
  (
  ∀
     (eta :
       Fin k),
  HierarchySegmentColors
      K
      (Fin.last
        K.dividerCount)
      eta =
    ({c :
        Fin
          k |
        ∃ (r
          :
          Fin
            U.length),
          A.length ≤
              (↑r :
                ℕ) ∧
            (↑r :
                  ℕ) <
                min
                  (↑(HierarchyFirstMissingPosition
                        phi
                        U
                        eta) :
                    ℕ)
                  U.length ∧
              phi
                  (U.edge
                    r) =
                some
                  c} :
      Finset
        (Fin
          k))) →
  GoodHierarchy
    K

private abbrev helperBranch685Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
   (baseU : HierarchyBase corr.replacementETT phi)
   (K : TashkinovHierarchy corr.replacementETT baseU) (hcount : K.dividerCount = H.dividerCount),
  let index :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin (H.dividerCount + (1 : ℕ)) :=
   fun (j : Fin (K.dividerCount + (1 : ℕ))) ↦
   Fin.cast
    (by
     have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive U
     omega)
    j;
  let gammaU :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin k →
  Finset (Fin k) :=
   fun (j : Fin (K.dividerCount + (1 : ℕ))) (eta : Fin k) ↦ C.good.gamma (index j) eta;
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  K.stage j.castSucc = H.stage (index j).castSucc) →
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStarredStage K j = HierarchyStarredStage H (index j)) →
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H (index j)) →
  ∀ (i : Fin K.dividerCount),
  let io : Fin H.dividerCount := Fin.cast hcount i;
  io.succ = index i.succ →
  io.castSucc = index i.castSucc →
  ∀ (eta : Fin k),
  (∀ (y : Fin k),
    (fun (eta : Fin k) ↦
       eta ∈ HierarchyStoredColorsAt C.hierarchy io.succ ∧
        (C.good.gamma io.succ eta ⊆
          (TreeSequenceVertexSet (C.hierarchy.stage io.succ.castSucc) \
             TreeSequenceVertexSet (HierarchyStarredStage C.hierarchy io.castSucc)).biUnion
           fun (v : V) ↦ MissingColors G phi v) ∧
         ∀ theta ∈ HierarchyStoredColorsAt C.hierarchy io.succ,
  theta ≠ eta →
  C.good.gamma io.succ theta = C.good.gamma io.castSucc theta)
      y →
     y = eta) →
  ∀ (y : Fin k),
  (fun (eta : Fin k) ↦
     eta ∈ HierarchyStoredColorsAt K i.succ ∧
      (gammaU i.succ eta ⊆
        (TreeSequenceVertexSet (K.stage i.succ.castSucc) \
           TreeSequenceVertexSet (HierarchyStarredStage K i.castSucc)).biUnion
         fun (v : V) ↦ MissingColors G phi v) ∧
       ∀ theta ∈ HierarchyStoredColorsAt K i.succ,
  theta ≠ eta →
  gammaU i.succ theta = gammaU i.castSucc theta)
    y →
  y = eta

private abbrev helperContinuation4495Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base)
   (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
   (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
   (hnonexceptional :
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  ¬∃ eta ∈ HierarchyStoredColorsAt H q,
    eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) ∧ D.theta ∈ C.good.gamma q eta),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀ (htail : (2 : ℕ) ≤ ell) (hell : ell = T.length - A.length) (hsum : A.length + ell = T.length)
   (hBlen : B.length = T.length - (2 : ℕ)) (hBT : TreeSequenceInitialSegment B T)
   (hprefixElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Bplus))
   (halpha :
    D.alpha ∉ TreeMissingColors phi B ∧
     D.alpha ∉ Dn ∧
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some D.alpha)
   (R :
    HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
     D.toHierarchySituationTwoTailData)
   (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
   (hminusMP : MaximumProperty corrMinus.replacementETT)
   (baseMinus : HierarchyBase corrMinus.replacementETT phi)
   (hminusCore : baseMinus.core = base.core) (hminusClosure : baseMinus.closure = base.closure)
   (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
   (hminusCount : HMinus.dividerCount = C.hierarchy.dividerCount)
   (hminusStages :
  ∀ (j : Fin (HMinus.dividerCount + (1 : ℕ))),
  HMinus.stage j.castSucc = C.hierarchy.stage (Fin.cast (by omega) j).castSucc)
   (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
   (hstarMP : MaximumProperty corrStar.replacementETT)
   (baseStar : HierarchyBase corrStar.replacementETT phi) (hstarCore : baseStar.core = base.core)
   (hstarClosure : baseStar.closure = base.closure)
   (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
   (hstarCount : HStar.dividerCount = C.hierarchy.dividerCount)
   (hstarStages :
  ∀ (j : Fin (HStar.dividerCount + (1 : ℕ))),
  HStar.stage j.castSucc = C.hierarchy.stage (Fin.cast (by omega) j).castSucc)
   (hBminus :
    TreeSequenceInitialSegment (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ)))
     R.minus)
   (hstarLen : R.star.length = R.minus.length + (1 : ℕ))
   (hminusStar : TreeSequenceInitialSegment R.minus R.star)
   (hstarEdge :
    R.star.edge (Fin.cast (by omega) (Fin.last R.minus.length)) = T.edge R.penultimateEdgeIndex)
   (hminusLen : R.minus.length = B.length + (1 : ℕ))
   (hminusEdge :
    R.minus.edge
      (Fin.cast (by change B.length + 1 = R.minus.length; exact hminusLen.symm)
       (Fin.last (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))).length)) =
     T.edge D.lastEdgeIndex)
   (hstarLength : R.star.length = T.length) (beta : Fin k)
   (hbetaMissing : beta ∈ TreeMissingColors phi B)
   (hbetaUnused :
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta)
   (hcolorsDistinct : beta ≠ D.alpha)
   (firstMissingLe :
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ)))
   (hc : c ∈ MissingColors G phi (S.vertex i)),
  HierarchyFirstMissingPosition phi S c ≤ i)
   (firstMissingMem :
  ∀ (S : TreeSequence G e0) (c : Fin k) (hc : c ∈ TreeMissingColors phi S),
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c)))
   (vertexMem :
  ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S)
   (missingMono :
  ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U),
  TreeMissingColors phi S ⊆ TreeMissingColors phi U)
   (hbetaT : beta ∈ TreeMissingColors phi T)
   (hbetaFirstBound : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
   (halphaFirst : HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex)
   (hbetaPrefix : beta ∈ TreeMissingColors phi Bplus)
   (halphaPrefix : D.alpha ∈ TreeMissingColors phi Bplus)
   (horderedUnused :
  beta ∉ TreeMissingColors phi A ∨ D.alpha ∉ TreeMissingColors phi A →
  TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T beta))
    (T.vertex (HierarchyFirstMissingPosition phi T D.alpha)) ∧
   beta ∉
    ({c : Fin k |
      ∃ (t : Fin T.length),
       A.length ≤ (↑t : ℕ) ∧
        (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T D.alpha) : ℕ) ∧
         phi (T.edge t) = some c} :
     Finset (Fin k)))
   (hDnDisjoint : Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn)
   (hDnqDisjoint :
    Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
     (HierarchyStoredColorsAt H q)),
  False

private theorem helper_hfinalCard_138.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  let finalColors : Finset (Fin k) :=
    ({c : Fin k | phi (T.edge R.penultimateEdgeIndex) = some c} : Finset (Fin k)) ∪
      ({c : Fin k | phi (T.edge D.lastEdgeIndex) = some c} : Finset (Fin k));
  (
  ∀ (f : E),
  ({c : Fin k | phi f = some c} : Finset (Fin k)).card ≤ (1 : ℕ)) →
  finalColors.card ≤ (2 : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D R corrMinus baseMinus HMinus corrStar
      baseStar HStar finalColors singleColorCard
  have hu := Finset.card_union_le
    (Finset.univ.filter fun c => phi (T.edge R.penultimateEdgeIndex) = some c)
    (Finset.univ.filter fun c => phi (T.edge D.lastEdgeIndex) = some c)
  have hp := singleColorCard (T.edge R.penultimateEdgeIndex)
  have hl := singleColorCard (T.edge D.lastEdgeIndex)
  dsimp [finalColors]
  omega

private theorem helper_hremaining_149.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  let baseExtraMissing : Finset (Fin k) :=
    (TreeSequenceVertexSet base.core \
          TreeSequenceVertexSet (ett.series.data.tree n.castSucc)).biUnion
      fun (v : V) ↦ MissingColors G phi v;
  let prefixUsed : Finset (Fin k) :=
    ({c : Fin k |
        ∃ (r : Fin T.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < A.length + (ell - (2 : ℕ)) ∧ phi (T.edge r) = some c} :
      Finset (Fin k));
  let available : Finset (Fin k) :=
    (TreeMissingColors phi B \ baseExtraMissing) \ prefixUsed;
  (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ available.card →
  let finalColors : Finset (Fin k) :=
    ({c : Fin k | phi (T.edge R.penultimateEdgeIndex) = some c} : Finset (Fin k)) ∪
      ({c : Fin k | phi (T.edge D.lastEdgeIndex) = some c} : Finset (Fin k));
  finalColors.card ≤ (2 : ℕ) →
  Dn.card ≤ ett.rounds →
  ett.rounds + (9 : ℕ) ≤ ((available \ finalColors) \ Dn).card := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B n Dn R corrMinus baseMinus
      HMinus corrStar baseStar HStar baseExtraMissing prefixUsed available havailable finalColors
      hfinalCard hDnCard
  have hfirst := Finset.card_le_card_sdiff_add_card
    (s := available) (t := finalColors)
  have hsecond := Finset.card_le_card_sdiff_add_card
    (s := available \ finalColors) (t := Dn)
  omega

private theorem helper_hbetaUnused_164.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  A.length + ell = T.length →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  R.star.length = R.minus.length + (1 : ℕ) →
  R.star.length = T.length →
  let prefixUsed : Finset (Fin k) :=
    ({c : Fin k |
        ∃ (r : Fin T.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < A.length + (ell - (2 : ℕ)) ∧ phi (T.edge r) = some c} :
      Finset (Fin k));
  let finalColors : Finset (Fin k) :=
    ({c : Fin k | phi (T.edge R.penultimateEdgeIndex) = some c} : Finset (Fin k)) ∪
      ({c : Fin k | phi (T.edge D.lastEdgeIndex) = some c} : Finset (Fin k));
  ∀ beta ∉ finalColors,
  beta ∉ prefixUsed →
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell htail hell hsum R corrMinus
      baseMinus HMinus corrStar baseStar HStar hstarLen hstarLength prefixUsed finalColors beta
      hbetaFinal hbetaPrefixUnused t ht hcolor
  by_cases hbefore : t.val < A.length + (ell - 2)
  · exact hbetaPrefixUnused (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, t, ht, hbefore, hcolor⟩)
  · have hp := R.penultimateEdgePosition
    have hl := D.lastEdgePosition
    have htlt := t.isLt
    have hindices : t = R.penultimateEdgeIndex ∨ t = D.lastEdgeIndex := by
      by_cases heq : t.val = R.penultimateEdgeIndex.val
      · exact Or.inl (Fin.ext heq)
      · right
        apply Fin.ext
        omega
    apply hbetaFinal
    rcases hindices with rfl | rfl
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolor⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolor⟩)

private theorem helper_firstMissingLe_188.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
  (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ))),
  c ∈ MissingColors G phi (S.vertex i) →
  HierarchyFirstMissingPosition phi S c ≤ i := by
  classical
  intro V E _ _ G k e0 phi S c i hc
  let _ := Fintype.ofFinite V
  let candidates : Finset (Fin (S.length + 1)) :=
    Finset.univ.filter fun j => c ∈ MissingColors G phi (S.vertex j)
  have hi : i ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hn : candidates.Nonempty := ⟨i, hi⟩
  have heq : HierarchyFirstMissingPosition phi S c = candidates.min' hn := by
    simp [HierarchyFirstMissingPosition, candidates, hn]
  rw [heq]
  exact Finset.min'_le _ _ hi

private theorem helper_firstMissingMem_201.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
  (S : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi S,
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c)) := by
  classical
  intro V E _ _ G k e0 phi S c hc
  let _ := Fintype.ofFinite V
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  have hv' : ∃ i, i ∈ Finset.univ ∧ S.vertex i = v := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image] using hv
  obtain ⟨i, _, hvi⟩ := hv'
  let candidates : Finset (Fin (S.length + 1)) :=
    Finset.univ.filter fun j => c ∈ MissingColors G phi (S.vertex j)
  have hi : i ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hvi.symm ▸ hcv⟩
  have hn : candidates.Nonempty := ⟨i, hi⟩
  have heq : HierarchyFirstMissingPosition phi S c = candidates.min' hn := by
    simp [HierarchyFirstMissingPosition, candidates, hn]
  rw [heq]
  exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2

private theorem helper_missingMono_224.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
  (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
  {S U : TreeSequence G e0},
  TreeSequenceInitialSegment S U →
  TreeMissingColors phi S ⊆ TreeMissingColors phi U := by
  classical
  intro V E _ _ G k e0 phi S U hSU c hc
  let _ := Fintype.ofFinite V
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  have hv' : ∃ i, i ∈ Finset.univ ∧ S.vertex i = v := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image] using hv
  obtain ⟨i, _, hvi⟩ := hv'
  have hvU : v ∈ TreeSequenceVertexSet U := by
    simpa only [TreeSequenceVertexSet] using
      ((@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨Fin.castLE (Nat.succ_le_succ hSU.1) i, Finset.mem_univ _,
          (hSU.2.1 i).trans hvi⟩)
  exact Finset.mem_biUnion.mpr
    ⟨v, hvU, hcv⟩

private theorem helper_hbetaFirstBound_243.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  B.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  R.star.length = R.minus.length + (1 : ℕ) →
  R.minus.length = B.length + (1 : ℕ) →
  R.star.length = T.length →
  ∀ beta ∈ TreeMissingColors phi B,
  (
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ))),
  c ∈ MissingColors G phi (S.vertex i) →
  HierarchyFirstMissingPosition phi S c ≤ i) →
  (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hBlen hBT R corrMinus baseMinus
      HMinus corrStar baseStar HStar hstarLen hminusLen hstarLength beta hbetaMissing firstMissingLe
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hbetaMissing
  have hv' : ∃ i, i ∈ Finset.univ ∧ B.vertex i = v := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image] using hv
  obtain ⟨i, _, hvi⟩ := hv'
  have hc : beta ∈ MissingColors G phi
      (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) i)) := by
    rw [hBT.2.1 i, hvi]
    exact hcv
  have hle := firstMissingLe T beta _ hc
  change (HierarchyFirstMissingPosition phi T beta).val ≤ i.val at hle
  have hi := i.isLt
  omega

private theorem helper_halphaFirst_256.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  B.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  (D.alpha ∉ TreeMissingColors phi B ∧
      D.alpha ∉ Dn ∧
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some D.alpha) →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  R.star.length = R.minus.length + (1 : ℕ) →
  R.minus.length = B.length + (1 : ℕ) →
  R.star.length = T.length →
  ∀ (_ : Fin k),
  (
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ))),
  c ∈ MissingColors G phi (S.vertex i) →
  HierarchyFirstMissingPosition phi S c ≤ i) →
  (
  ∀ (S : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi S,
    c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c))) →
  (
  ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S) →
  D.alpha ∈ TreeMissingColors phi T →
  HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B n Dn hBlen hBT halpha R
      corrMinus baseMinus HMinus corrStar baseStar HStar hstarLen hminusLen hstarLength beta
      firstMissingLe firstMissingMem vertexMem halphaT
  have hle := firstMissingLe T D.alpha D.penultimateVertexIndex
    D.alphaMissingPenultimate
  have hm := firstMissingMem T D.alpha halphaT
  have hp := D.penultimateVertexPosition
  apply Fin.ext
  change (HierarchyFirstMissingPosition phi T D.alpha).val ≤
    D.penultimateVertexIndex.val at hle
  by_contra hne
  have hbound : (HierarchyFirstMissingPosition phi T D.alpha).val ≤ B.length := by
    omega
  let ib : Fin (B.length + 1) :=
    ⟨(HierarchyFirstMissingPosition phi T D.alpha).val, by omega⟩
  have heq : Fin.castLE (Nat.succ_le_succ hBT.1) ib =
      HierarchyFirstMissingPosition phi T D.alpha := Fin.ext rfl
  have hmB : D.alpha ∈ MissingColors G phi (B.vertex ib) := by
    rw [← hBT.2.1 ib, heq]
    exact hm
  exact halpha.1 (Finset.mem_biUnion.mpr ⟨_, vertexMem B ib, hmB⟩)

private theorem helper_halphaPrefix_278.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let ell : ℕ := HierarchyFullTailLength C;
  let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
  Bplus.length = T.length - (1 : ℕ) →
  TreeSequenceInitialSegment Bplus T →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  R.star.length = R.minus.length + (1 : ℕ) →
  R.minus.length = T.length - (1 : ℕ) →
  R.star.length = T.length →
  ∀ (_ : Fin k),
  (
  ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S) →
  D.alpha ∈ TreeMissingColors phi Bplus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell Bplus hBpluslen hBplusT R corrMinus
      baseMinus HMinus corrStar baseStar HStar hstarLen hminusLength hstarLength beta vertexMem
  let i : Fin (Bplus.length + 1) := Fin.last Bplus.length
  have heq : Fin.castLE (Nat.succ_le_succ hBplusT.1) i =
      D.penultimateVertexIndex := by
    apply Fin.ext
    change Bplus.length = D.penultimateVertexIndex.val
    have hp := D.penultimateVertexPosition
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨_, vertexMem Bplus i, ?_⟩
  rw [← hBplusT.2.1 i, heq]
  exact D.alphaMissingPenultimate

private theorem helper_horderedUnused_290.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  B.length = T.length - (2 : ℕ) →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  R.star.length = R.minus.length + (1 : ℕ) →
  R.minus.length = B.length + (1 : ℕ) →
  R.star.length = T.length →
  ∀ (beta : Fin k),
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta) →
  (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length →
  HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
  beta ∉ TreeMissingColors phi A ∨ D.alpha ∉ TreeMissingColors phi A →
  TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T beta))
      (T.vertex (HierarchyFirstMissingPosition phi T D.alpha)) ∧
  beta ∉
    ({c : Fin k |
        ∃ (t : Fin T.length),
          A.length ≤ (↑t : ℕ) ∧
            (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T D.alpha) : ℕ) ∧
              phi (T.edge t) = some c} :
      Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B hBlen R corrMinus baseMinus
      HMinus corrStar baseStar HStar hstarLen hminusLen hstarLength beta hbetaUnused
      hbetaFirstBound halphaFirst _
  refine ⟨?_, ?_⟩
  · refine ⟨_, _, rfl, rfl, ?_⟩
    rw [halphaFirst]
    have hp := D.penultimateVertexPosition
    change (HierarchyFirstMissingPosition phi T beta).val <
      D.penultimateVertexIndex.val
    omega
  · intro hm
    obtain ⟨_, t, ht, _, hcolor⟩ := Finset.mem_filter.mp hm
    exact hbetaUnused t ht hcolor

private theorem helper_hDnDisjoint_310.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let Bplus : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (1 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  (D.alpha ∉ TreeMissingColors phi B ∧
      D.alpha ∉ Dn ∧
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some D.alpha) →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData),
  let baseExtraMissing : Finset (Fin k) :=
    (TreeSequenceVertexSet base.core \
          TreeSequenceVertexSet (ett.series.data.tree n.castSucc)).biUnion
      fun (v : V) ↦ MissingColors G phi v;
  let prefixUsed : Finset (Fin k) :=
    ({c : Fin k |
        ∃ (r : Fin T.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < A.length + (ell - (2 : ℕ)) ∧ phi (T.edge r) = some c} :
      Finset (Fin k));
  let available : Finset (Fin k) :=
    (TreeMissingColors phi B \ baseExtraMissing) \ prefixUsed;
  let finalColors : Finset (Fin k) :=
    ({c : Fin k | phi (T.edge R.penultimateEdgeIndex) = some c} : Finset (Fin k)) ∪
      ({c : Fin k | phi (T.edge D.lastEdgeIndex) = some c} : Finset (Fin k));
  ∀ beta ∈ (available \ finalColors) \ Dn,
  beta ∈ available \ finalColors →
  beta ∉ Dn →
  beta ∈ available →
  beta ∉ finalColors →
  beta ∈ TreeMissingColors phi B \ baseExtraMissing →
  beta ∉ prefixUsed →
  beta ∈ TreeMissingColors phi B →
  beta ∉ baseExtraMissing →
  (
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta) →
  beta ≠ D.alpha →
  beta ∈ TreeMissingColors phi T →
  (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length →
  beta ∈ TreeMissingColors phi Bplus →
  (
  beta ∉ TreeMissingColors phi A ∨ D.alpha ∉ TreeMissingColors phi A →
  TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T beta))
      (T.vertex (HierarchyFirstMissingPosition phi T D.alpha)) ∧
    beta ∉
      ({c : Fin k |
          ∃ (t : Fin T.length),
            A.length ≤ (↑t : ℕ) ∧
              (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T D.alpha) : ℕ) ∧
                phi (T.edge t) = some c} :
        Finset (Fin k))) →
  Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B Bplus n Dn halpha R
      baseExtraMissing prefixUsed available finalColors beta hbeta hbetaAvailableFinal hbetaDn
      hbetaAvailable hbetaFinal hbetaMissingExtra hbetaPrefixUnused hbetaMissing hbetaExtra
      hbetaUnused hcolorsDistinct hbetaT hbetaFirstBound hbetaPrefix horderedUnused
  rw [Finset.disjoint_left]
  intro c hc hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact hbetaDn hd
  · exact halpha.2.1 hd

private theorem helper_hcomponentPenultimate_325.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar) (beta : Fin k),
  HierarchyFirstMissingPosition phi T D.alpha = D.penultimateVertexIndex →
  Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn →
  Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k))
      (HierarchyStoredColorsAt H q) →
  (let H : TashkinovHierarchy ett base := C.hierarchy;
    have q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    have n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    have A : TreeSequence G e0 := HierarchyStarredStage H q;
    have Tnq : TreeSequence G e0 :=
      H.stage
        (⟨H.dividerCount, by
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
    (
  (0 : ℕ) < H.dividerCount ∧
       (beta ∈ TreeMissingColors phi Tnq ∨
         Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dnq) →
  sameComponent) ∧
      (
  H.dividerCount = (0 : ℕ) ∧
       (beta ∈ TreeMissingColors phi Tn ∨
         Disjoint (insert beta ({ D.alpha } : Finset (Fin k)) : Finset (Fin k)) Dn) →
  sameComponent) ∧
        (
  beta ∈ TreeMissingColors phi A ∧
     TreeColorSetClosed G phi A ({ beta } : Finset (Fin k)) →
  sameComponent ∧ TreeInterchangeable G A phi beta D.alpha)) →
  TwoColorComponent G phi beta D.alpha
      (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
    TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q n Dn R corrMinus baseMinus HMinus
      corrStar baseStar HStar beta halphaFirst hDnDisjoint hDnqDisjoint hchange
  have hc : TwoColorComponent G phi beta D.alpha
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
      TwoColorComponent G phi beta D.alpha
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T D.alpha))) := by
    by_cases hq : 0 < H.dividerCount
    · exact hchange.1 ⟨hq, Or.inr hDnqDisjoint⟩
    · have hqzero : H.dividerCount = 0 := by omega
      exact hchange.2.1 ⟨hqzero, Or.inr hDnDisjoint⟩
  simpa [halphaFirst] using hc

private theorem helper_firstMissingMemBelow_339.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
  (R :
    HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
      D.toHierarchySituationTwoTailData)
  (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
  (baseMinus : HierarchyBase corrMinus.replacementETT phi)
  (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
  (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
  (baseStar : HierarchyBase corrStar.replacementETT phi)
  (_ : TashkinovHierarchy corrStar.replacementETT baseStar) (_ : Fin k)
  (S : TreeSequence G e0) (c : Fin k),
  (↑(HierarchyFirstMissingPosition phi S c) : ℕ) < S.length →
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D R corrMinus baseMinus HMinus corrStar
      baseStar HStar beta S c hlt
  let candidates : Finset (Fin (S.length + 1)) :=
    Finset.univ.filter fun j => c ∈ MissingColors G phi (S.vertex j)
  by_cases hn : candidates.Nonempty
  · have heq : HierarchyFirstMissingPosition phi S c = candidates.min' hn := by
      simp [HierarchyFirstMissingPosition, candidates, hn]
    rw [heq]
    exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  · have heq : HierarchyFirstMissingPosition phi S c = Fin.last S.length := by
      simp [HierarchyFirstMissingPosition, candidates, hn]
    rw [heq] at hlt
    simp only [Fin.val_last] at hlt
    omega

private theorem helper_firstLowerInOld_356.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  B.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  R.star.length = R.minus.length + (1 : ℕ) →
  R.minus.length = B.length + (1 : ℕ) →
  R.star.length = T.length →
  ∀ (_ : Fin k),
  (
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ))),
  c ∈ MissingColors G phi (S.vertex i) →
  HierarchyFirstMissingPosition phi S c ≤ i) →
  (
  ∀ (S : TreeSequence G e0) (c : Fin k),
  (↑(HierarchyFirstMissingPosition phi S c) : ℕ) < S.length →
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c))) →
  ∀ (U : TreeSequence G e0),
  TreeSequenceInitialSegment B U →
  ∀ (eta : Fin k),
  ∀ r ≤ B.length,
  r < (↑(HierarchyFirstMissingPosition phi U eta) : ℕ) →
  r < (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hBlen hBT R corrMinus baseMinus
      HMinus corrStar baseStar HStar hstarLen hminusLen hstarLength beta firstMissingLe
      firstMissingMemBelow U hBU eta r hrB hrU
  by_contra hnot
  have hpB : (HierarchyFirstMissingPosition phi T eta).val ≤ B.length := by omega
  have hpT : (HierarchyFirstMissingPosition phi T eta).val < T.length := by omega
  have hm := firstMissingMemBelow T eta hpT
  let i : Fin (B.length + 1) :=
    ⟨(HierarchyFirstMissingPosition phi T eta).val, by omega⟩
  have hiT : Fin.castLE (Nat.succ_le_succ hBT.1) i =
      HierarchyFirstMissingPosition phi T eta := Fin.ext rfl
  have hmU : eta ∈ MissingColors G phi
      (U.vertex (Fin.castLE (Nat.succ_le_succ hBU.1) i)) := by
    rw [hBU.2.1 i, ← hBT.2.1 i, hiT]
    exact hm
  have hle := firstMissingLe U eta _ hmU
  change (HierarchyFirstMissingPosition phi U eta).val ≤
    (HierarchyFirstMissingPosition phi T eta).val at hle
  omega

private theorem helper_oldSegmentMember_377.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (eta c : Fin k) (r : Fin T.length),
  A.length ≤ (↑r : ℕ) →
  (↑r : ℕ) < (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) →
  phi (T.edge r) = some c →
  c ∈ HierarchySegmentColors H q eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A eta c r hlo hhi hcolor
  have hq : q.succ = Fin.last (H.dividerCount + 1) := by
    apply Fin.ext
    simp [q]
  unfold HierarchySegmentColors
  change c ∈ Finset.univ.filter (fun c =>
    ∃ r : Fin (H.stage q.succ).length, A.length ≤ r.val ∧
      r.val < min (HierarchyFirstMissingPosition phi T eta).val
        (H.stage q.succ).length ∧ phi ((H.stage q.succ).edge r) = some c)
  rw [hq, H.terminalStage]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, r, hlo, ?_, hcolor⟩
  exact lt_min hhi r.isLt

private theorem helper_terminalAvoidance_394.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  (
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  ¬∃ eta ∈ HierarchyStoredColorsAt H q,
      eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) ∧
        D.theta ∈ C.good.gamma q eta) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  A.length + ell = T.length →
  B.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  R.star.length = R.minus.length + (1 : ℕ) →
  R.minus.length = B.length + (1 : ℕ) →
  R.star.length = T.length →
  ∀ (_ : Fin k),
  (
  ∀ (S : TreeSequence G e0) (c : Fin k),
  (↑(HierarchyFirstMissingPosition phi S c) : ℕ) < S.length →
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c))) →
  (∀ (U : TreeSequence G e0),
      TreeSequenceInitialSegment B U →
        ∀ (eta : Fin k),
          ∀ r ≤ B.length,
  r < (↑(HierarchyFirstMissingPosition phi U eta) : ℕ) →
  r < (↑(HierarchyFirstMissingPosition phi T eta) : ℕ)) →
  (
  ∀ (eta c : Fin k) (r : Fin T.length),
  A.length ≤ (↑r : ℕ) →
  (↑r : ℕ) < (↑(HierarchyFirstMissingPosition phi T eta) : ℕ) →
  phi (T.edge r) = some c →
  c ∈ HierarchySegmentColors H q eta) →
  ∀ (U : TreeSequence G e0),
  TreeSequenceInitialSegment B U →
  U.length ≤ B.length + (2 : ℕ) →
  (
  ∀ (r : Fin U.length),
  (↑r : ℕ) = B.length →
  U.edge r = T.edge D.lastEdgeIndex) →
  (
  ∀ (r : Fin U.length),
  (↑r : ℕ) = B.length + (1 : ℕ) →
  U.edge r = T.edge R.penultimateEdgeIndex) →
  ∀ eta ∈ HierarchyStoredColorsAt H q,
  Disjoint (C.good.gamma q eta)
    ({c : Fin k |
        ∃ (r : Fin U.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi U eta) : ℕ) U.length ∧
              phi (U.edge r) = some c} :
      Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D hnonexceptional H q A ell B htail hell
      hsum hBlen hBT R corrMinus baseMinus HMinus corrStar baseStar HStar hstarLen hminusLen
      hstarLength beta firstMissingMemBelow firstLowerInOld oldSegmentMember U hBU hlen
      hfirstEdge hsecondEdge eta heta
  rw [Finset.disjoint_left]
  intro c hc hused
  obtain ⟨_, r, hlo, hhi, hcolor⟩ := Finset.mem_filter.mp hused
  have hrU : r.val < (HierarchyFirstMissingPosition phi U eta).val :=
    lt_of_lt_of_le hhi (Nat.min_le_left _ _)
  have hnotOld : c ∉ HierarchySegmentColors H q eta :=
    (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hc)).2
  by_cases hrB : r.val < B.length
  · let rb : Fin B.length := ⟨r.val, hrB⟩
    let rt : Fin T.length := Fin.castLE hBT.1 rb
    have hru : Fin.castLE hBU.1 rb = r := Fin.ext rfl
    have hedge : U.edge r = T.edge rt := by
      rw [← hru, hBU.2.2 rb, hBT.2.2 rb]
    have hcolorOld : phi (T.edge rt) = some c := by
      rw [← hedge]
      exact hcolor
    have hfirst := firstLowerInOld U hBU eta r.val (by omega) hrU
    exact hnotOld (oldSegmentMember eta c rt hlo hfirst hcolorOld)
  · have hrlt := r.isLt
    have hpositions : r.val = B.length ∨ r.val = B.length + 1 := by omega
    rcases hpositions with hfirst | hsecond
    · have hcolorTheta : c = D.theta := by
        rw [hfirstEdge r hfirst] at hcolor
        exact Option.some.inj (hcolor.symm.trans D.thetaOnLastEdge)
      have hpOld := firstLowerInOld U hBU eta B.length le_rfl (by omega)
      have hl := D.lastEdgePosition
      have hp := D.penultimateVertexPosition
      have hpBound : (HierarchyFirstMissingPosition phi T eta).val ≤
          D.lastEdgeIndex.val := by
        by_contra hnot
        apply hnotOld
        apply oldSegmentMember eta c D.lastEdgeIndex
        · omega
        · omega
        · rw [hcolorTheta]
          exact D.thetaOnLastEdge
      have hfirstPenultimate : HierarchyFirstMissingPosition phi T eta =
          D.penultimateVertexIndex := by
        apply Fin.ext
        omega
      have hm := firstMissingMemBelow T eta (by omega)
      rw [hfirstPenultimate] at hm
      exact hnonexceptional ⟨eta, heta, hm, hcolorTheta ▸ hc⟩
    · have hpOld := firstLowerInOld U hBU eta B.length le_rfl (by omega)
      have hp := R.penultimateEdgePosition
      apply hnotOld
      apply oldSegmentMember eta c R.penultimateEdgeIndex
      · omega
      · omega
      · rw [← hsecondEdge r hsecond]
        exact hcolor

private theorem helper_hBstar_471.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData),
  TreeSequenceInitialSegment
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))) R.minus →
  TreeSequenceInitialSegment R.minus R.star →
  TreeSequenceInitialSegment B R.star := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B R hBminus hminusStar
  refine ⟨le_trans hBminus.1 hminusStar.1, ?_, ?_⟩
  · intro i
    exact (hminusStar.2.1
      (Fin.castLE (Nat.succ_le_succ hBminus.1) i)).trans (hBminus.2.1 i)
  · intro i
    exact (hminusStar.2.2 (Fin.castLE hBminus.1 i)).trans (hBminus.2.2 i)

private theorem helper_hstarSecondEdge_484.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  B.length = T.length - (2 : ℕ) →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar)
    (hstarLen : R.star.length = R.minus.length + (1 : ℕ)),
  R.star.edge
        (Fin.cast
          (by
            have := GoldbergSeymour.TreeSequence.positive T
            omega)
          (Fin.last R.minus.length)) =
      T.edge R.penultimateEdgeIndex →
  R.minus.length = B.length + (1 : ℕ) →
  ∀ (_ : Fin k) (r : Fin R.star.length),
  (↑r : ℕ) = B.length + (1 : ℕ) →
  R.star.edge r = T.edge R.penultimateEdgeIndex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hBlen R corrMinus baseMinus HMinus
      corrStar baseStar HStar hstarLen hstarEdge hminusLen beta r hr
  have hi : r = Fin.cast hstarLen.symm (Fin.last R.minus.length) := by
    apply Fin.ext
    change r.val = R.minus.length
    omega
  rw [hi]
  exact hstarEdge

private theorem helper_hApositive_533.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar) (_ : Fin k),
  (0 : ℕ) < H.dividerCount →
  A = H.stage q.castSucc := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A R corrMinus baseMinus HMinus
      corrStar baseStar HStar beta hq
  obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
  · have hv := congrArg Fin.val hz
    simp [q] at hv
    omega
  · dsimp [A]
    rw [hi]
    rfl

private theorem helper_starredEq_570.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (baseU : HierarchyBase corr.replacementETT phi),
  baseU.core = base.core →
  ∀ (K : TashkinovHierarchy corr.replacementETT baseU)
    (hcount : K.dividerCount = H.dividerCount),
  let index :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin (H.dividerCount + (1 : ℕ)) :=
    fun (j : Fin (K.dividerCount + (1 : ℕ))) ↦
    Fin.cast
      (by
        have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive U
        omega)
      j;
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  K.stage j.castSucc = H.stage (index j).castSucc) →
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStarredStage K j = HierarchyStarredStage H (index j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H U corr baseU hcore K hcount index stageEq j
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · have hi : index 0 = 0 := Fin.ext rfl
    rw [hi]
    exact hcore
  · have hi : index i.succ = (Fin.cast hcount i).succ := Fin.ext rfl
    rw [hi]
    simp only [HierarchyStarredStage, Fin.cases_succ]
    have hs := stageEq i.succ
    rw [hi] at hs
    exact hs

private theorem helper_missingEq_587.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (baseU : HierarchyBase corr.replacementETT phi)
    (K : TashkinovHierarchy corr.replacementETT baseU)
    (hcount : K.dividerCount = H.dividerCount),
  let index :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin (H.dividerCount + (1 : ℕ)) :=
    fun (j : Fin (K.dividerCount + (1 : ℕ))) ↦
    Fin.cast
      (by
        have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive U
        omega)
      j;
  corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        ett.series.data.tree n.castSucc ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind n ∧
        TashkinovStoredColors corr.replacementETT.series.data
            (Fin.last corr.replacementETT.rounds) =
          Dn →
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  K.stage j.castSucc = H.stage (index j).castSucc) →
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStageMissingColors K j = HierarchyStageMissingColors H (index j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H n Dn U corr baseU K hcount index hdata stageEq j
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · have hi : index 0 = 0 := Fin.ext rfl
    rw [hi]
    simpa only [HierarchyStageMissingColors, Fin.cases_zero] using
      congrArg (TreeMissingColors phi) hdata.1
  · have hi : index i.succ = (Fin.cast hcount i).succ := Fin.ext rfl
    rw [hi]
    simp only [HierarchyStageMissingColors, Fin.cases_succ]
    have hs := stageEq i.succ
    rw [hi] at hs
    exact congrArg (TreeMissingColors phi) hs

private theorem helper_segmentEqInternal_600.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  A.length + ell = T.length →
  B.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar),
  R.star.length = R.minus.length + (1 : ℕ) →
  R.minus.length = B.length + (1 : ℕ) →
  R.star.length = T.length →
  ∀ (_ : Fin k),
  (
  (0 : ℕ) < H.dividerCount →
  A = H.stage q.castSucc) →
  (Monotone fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦ (H.stage j).length) →
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (baseU : HierarchyBase corr.replacementETT phi)
    (K : TashkinovHierarchy corr.replacementETT baseU)
    (hcount : K.dividerCount = H.dividerCount),
  TreeSequenceInitialSegment B U →
  let index :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin (H.dividerCount + (1 : ℕ)) :=
    fun (j : Fin (K.dividerCount + (1 : ℕ))) ↦
    Fin.cast
      (by
        have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive U
        omega)
      j;
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  K.stage j.castSucc = H.stage (index j).castSucc) →
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStarredStage K j = HierarchyStarredStage H (index j)) →
  ∀ (i : Fin K.dividerCount) (eta : Fin k),
  HierarchySegmentColors K i.castSucc eta =
    HierarchySegmentColors H (index i.castSucc) eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B htail hell hsum hBlen hBT R
      corrMinus baseMinus HMinus corrStar baseStar HStar hstarLen hminusLen hstarLength beta
      hApositive stageLengthMono U corr baseU K hcount hBU index stageEq starredEq i eta
  let io : Fin H.dividerCount := Fin.cast hcount i
  have hnext : (index i.castSucc).succ = (index i.succ).castSucc := Fin.ext rfl
  have hinext : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
  have hL : (H.stage (index i.succ).castSucc).length ≤ B.length := by
    have hpos : 0 < H.dividerCount := Nat.zero_lt_of_lt io.isLt
    have hle : (index i.succ).castSucc ≤ q.castSucc := by
      change io.val + 1 ≤ H.dividerCount
      omega
    have hlen := stageLengthMono hle
    change (H.stage (index i.succ).castSucc).length ≤
      (H.stage q.castSucc).length at hlen
    rw [← hApositive hpos] at hlen
    omega
  have hcU := HierarchyFirstMissingPositionPrefixCutoff phi B U hBU eta
    (H.stage (index i.succ).castSucc).length hL
  have hcT := HierarchyFirstMissingPositionPrefixCutoff phi B T hBT eta
    (H.stage (index i.succ).castSucc).length hL
  have hcut := hcU.symm.trans hcT
  unfold HierarchySegmentColors
  dsimp only
  rw [hinext, stageEq i.succ, hnext, starredEq i.castSucc, hcut]

private theorem helper_terminalSegmentEq_627.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (baseU : HierarchyBase corr.replacementETT phi)
    (K : TashkinovHierarchy corr.replacementETT baseU)
    (hcount : K.dividerCount = H.dividerCount),
  let index :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin (H.dividerCount + (1 : ℕ)) :=
    fun (j : Fin (K.dividerCount + (1 : ℕ))) ↦
    Fin.cast
      (by
        have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive U
        omega)
      j;
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStarredStage K j = HierarchyStarredStage H (index j)) →
  index (Fin.last K.dividerCount) = q →
  ∀ (eta : Fin k),
  HierarchySegmentColors K (Fin.last K.dividerCount) eta =
    ({c : Fin k |
        ∃ (r : Fin U.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi U eta) : ℕ) U.length ∧
              phi (U.edge r) = some c} :
      Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A U corr baseU K hcount index starredEq
      indexLast eta
  unfold HierarchySegmentColors
  dsimp only
  have hi : (Fin.last K.dividerCount).succ =
      Fin.last (K.dividerCount + 1) := Fin.ext rfl
  rw [hi, K.terminalStage, starredEq, indexLast]

private theorem helper_branch_659.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (_ : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (_ : TashkinovHierarchy corrStar.replacementETT baseStar) (_ : Fin k)
    (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (baseU : HierarchyBase corr.replacementETT phi)
    (K : TashkinovHierarchy corr.replacementETT baseU)
    (hcount : K.dividerCount = H.dividerCount),
  (∀ eta ∈ HierarchyStoredColorsAt H q,
      Disjoint (C.good.gamma q eta)
        ({c : Fin k |
            ∃ (r : Fin U.length),
              A.length ≤ (↑r : ℕ) ∧
                (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi U eta) : ℕ) U.length ∧
                  phi (U.edge r) = some c} :
          Finset (Fin k))) →
  let index :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin (H.dividerCount + (1 : ℕ)) :=
    fun (j : Fin (K.dividerCount + (1 : ℕ))) ↦
    Fin.cast
      (by
        have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive U
        omega)
      j;
  let gammaU :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin k →
  Finset (Fin k) :=
    fun (j : Fin (K.dividerCount + (1 : ℕ))) (eta : Fin k) ↦ C.good.gamma (index j) eta;
  index (Fin.last K.dividerCount) = q →
  (
  ∀ (eta : Fin k),
  HierarchySegmentColors K (Fin.last K.dividerCount) eta =
    ({c : Fin k |
        ∃ (r : Fin U.length),
          A.length ≤ (↑r : ℕ) ∧
            (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition phi U eta) : ℕ) U.length ∧
              phi (U.edge r) = some c} :
      Finset (Fin k))) →
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  ∀ eta ∈ HierarchyStoredColorsAt K j,
  ∀ ⦃c : Fin k⦄,
  c ∈ gammaU j eta →
  eta ∈ HierarchyStoredColorsAt H (index j) →
  c ∈ C.good.gamma (index j) eta →
  c ∈ HierarchyStageMissingColors C.hierarchy (index j) ∧
      c ∉ HierarchySegmentColors C.hierarchy (index j) eta →
  c ∈ HierarchySegmentColors K j eta →
  ¬(↑j : ℕ) < K.dividerCount →
  False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A R corrMinus baseMinus HMinus
      corrStar baseStar HStar beta U corr baseU K hcount havoid index gammaU indexLast
      terminalSegmentEq j eta heta c hc hetaOld hcOld hold hseg hj
  have hi : j = Fin.last K.dividerCount := by apply Fin.ext; simp; omega
  subst j
  rw [terminalSegmentEq] at hseg
  rw [indexLast] at hetaOld hcOld
  exact Finset.disjoint_left.mp (havoid eta hetaOld) hcOld hseg

private theorem helper_branch_677.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  ∀ (U : TreeSequence G e0) (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
    (baseU : HierarchyBase corr.replacementETT phi)
    (K : TashkinovHierarchy corr.replacementETT baseU)
    (hcount : K.dividerCount = H.dividerCount),
  let index :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin (H.dividerCount + (1 : ℕ)) :=
    fun (j : Fin (K.dividerCount + (1 : ℕ))) ↦
    Fin.cast
      (by
        have := GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corr
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive U
        omega)
      j;
  let gammaU :
  Fin (K.dividerCount + (1 : ℕ)) →
  Fin k →
  Finset (Fin k) :=
    fun (j : Fin (K.dividerCount + (1 : ℕ))) (eta : Fin k) ↦ C.good.gamma (index j) eta;
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  K.stage j.castSucc = H.stage (index j).castSucc) →
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStarredStage K j = HierarchyStarredStage H (index j)) →
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H (index j)) →
  ∀ (i : Fin K.dividerCount),
  let io : Fin H.dividerCount := Fin.cast hcount i;
  io.succ = index i.succ →
  io.castSucc = index i.castSucc →
  ∀ (eta : Fin k),
  (eta ∈ HierarchyStoredColorsAt C.hierarchy io.succ ∧
      (C.good.gamma io.succ eta ⊆
          (TreeSequenceVertexSet (C.hierarchy.stage io.succ.castSucc) \
                TreeSequenceVertexSet
                  (HierarchyStarredStage C.hierarchy io.castSucc)).biUnion
            fun (v : V) ↦ MissingColors G phi v) ∧
        ∀ theta ∈ HierarchyStoredColorsAt C.hierarchy io.succ,
  theta ≠ eta →
  C.good.gamma io.succ theta = C.good.gamma io.castSucc theta) →
  (fun (eta : Fin k) ↦
      eta ∈ HierarchyStoredColorsAt K i.succ ∧
        (gammaU i.succ eta ⊆
            (TreeSequenceVertexSet (K.stage i.succ.castSucc) \
                  TreeSequenceVertexSet (HierarchyStarredStage K i.castSucc)).biUnion
              fun (v : V) ↦ MissingColors G phi v) ∧
          ∀ theta ∈ HierarchyStoredColorsAt K i.succ,
  theta ≠ eta →
  gammaU i.succ theta = gammaU i.castSucc theta)
    eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H U corr baseU K hcount index gammaU stageEq
      starredEq storedEq i io hn hp eta heta
  refine ⟨?_, ?_, ?_⟩
  · rw [storedEq, ← hn]
    exact heta.1
  · rw [stageEq, starredEq]
    simpa [gammaU, ← hn, ← hp] using heta.2.1
  · intro theta htheta hne
    rw [storedEq, ← hn] at htheta
    simpa [gammaU, ← hn, ← hp] using heta.2.2 theta htheta hne

private theorem helper_branch_685.{u_1, u_2} :
    helperBranch685Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H U corr baseU K hcount index gammaU stageEq
      starredEq storedEq i io hn hp eta hunique theta htheta
  apply hunique theta
  refine ⟨?_, ?_, ?_⟩
  · rw [storedEq, ← hn] at htheta
    exact htheta.1
  · have hlocal := htheta.2.1
    rw [stageEq, starredEq] at hlocal
    simpa [gammaU, ← hn, ← hp] using hlocal
  · intro z hz hne
    have hzNew : z ∈ HierarchyStoredColorsAt K i.succ := by
      rwa [storedEq, ← hn]
    simpa [gammaU, ← hn, ← hp] using htheta.2.2 z hzNew hne

private noncomputable abbrev helperGoodU2513.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2}, transferredGoodHierarchyConstructorType V E := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A n Dn R corrMinus baseMinus HMinus
      corrStar baseStar HStar beta U corr baseU hcore hclosure K hcount havoid index gammaU hdata
      stageEq starredEq storedEq missingEq segmentEqInternal indexLast terminalSegmentEq
  exact {
    gamma := gammaU
    twoColors := by
      intro j eta heta
      apply C.good.twoColors (index j) eta
      rwa [← storedEq j]
    avoidance := by
      intro j eta heta c hc
      have hetaOld : eta ∈ HierarchyStoredColorsAt H (index j) := by
        rwa [← storedEq j]
      have hcOld : c ∈ C.good.gamma (index j) eta := hc
      have hold := Finset.mem_sdiff.mp (C.good.avoidance (index j) eta hetaOld hcOld)
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · rw [missingEq j]
        exact hold.1
      intro hseg
      by_cases hj : j.val < K.dividerCount
      · let i : Fin K.dividerCount := ⟨j.val, hj⟩
        have hi : i.castSucc = j := Fin.ext rfl
        rw [← hi, segmentEqInternal i eta] at hseg
        exact hold.2 hseg
      · exact @helper_branch_659 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@R)
          (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@beta) (@U)
          (@corr) (@baseU) (@K) (@hcount) (@havoid) (@indexLast) (@terminalSegmentEq) (@j) (@eta)
          (@heta) (@c) (@hc) (@hetaOld) (@hcOld) (@hold) (@hseg) (@hj)
    disjointPairs := by
      intro j eta theta heta htheta hne
      apply C.good.disjointPairs (index j) eta theta
      · rwa [← storedEq j]
      · rwa [← storedEq j]
      · exact hne
    uniqueRefresh := by
      intro i
      let io : Fin H.dividerCount := Fin.cast hcount i
      have hn : io.succ = index i.succ := Fin.ext rfl
      have hp : io.castSucc = index i.castSucc := Fin.ext rfl
      obtain ⟨eta, heta, hunique⟩ := C.good.uniqueRefresh io
      refine ⟨eta, ?_, ?_⟩
      · apply helper_branch_677 <;> assumption
      · apply helper_branch_685 <;> assumption
    parallelBase := by
      have hzero : (HierarchyStoredColorsAt K 0).biUnion (gammaU 0) =
          (HierarchyStoredColorsAt H 0).biUnion (C.good.gamma 0) := by
        have hi : index 0 = 0 := Fin.ext rfl
        rw [storedEq, hi]
        simp only [gammaU, hi]
      dsimp only
      intro hpe
      have hpeOld : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
        rwa [← hdata.2.1]
      have hold := C.good.parallelBase hpeOld
      rw [hcore, hclosure, hzero, hdata.1]
      exact hold
    minusClosed := by
      intro i
      let io : Fin H.dividerCount := Fin.cast hcount i
      have hn : io.succ = index i.succ := Fin.ext rfl
      have hp : io.castSucc = index i.castSucc := Fin.ext rfl
      have hold := C.good.minusClosed io
      rw [hn, hp] at hold
      rw [stageEq, storedEq]
      simpa [gammaU] using hold }

private theorem helper_starredTransfer_726.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  ∀ {inputU : PartialEdgeColoring E k} {U : TreeSequence G e0}
    {ettU : ExtendedTashkinovTree G k e0 inputU U phi} {baseU : HierarchyBase ettU phi}
    (K : TashkinovHierarchy ettU baseU),
  baseU.core = base.core →
  ∀ (hc : K.dividerCount = H.dividerCount),
  (
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  K.stage j.castSucc =
    H.stage
      (Fin.cast
          (by
            have := GoldbergSeymour.TreeSequence.positive T
            have := GoldbergSeymour.TreeSequence.positive U
            omega)
          j).castSucc) →
  ∀ (j : Fin (K.dividerCount + (1 : ℕ))),
  HierarchyStarredStage K j =
    HierarchyStarredStage H
      (Fin.cast
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive U
          omega)
        j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H inputU U ettU baseU K hcore hc hs j
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · have hi : Fin.cast (congrArg (fun d => d + 1) hc) 0 =
        (0 : Fin (H.dividerCount + 1)) := Fin.ext rfl
    rw [hi]
    exact hcore
  · have hi : Fin.cast (congrArg (fun d => d + 1) hc) i.succ =
        (Fin.cast hc i).succ := Fin.ext rfl
    rw [hi]
    simp only [HierarchyStarredStage, Fin.cases_succ]
    have h := hs i.succ
    rw [hi] at h
    exact h

private theorem helper_pathLeFull_765.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (phi : PartialEdgeColoring E k) {inputU : PartialEdgeColoring E k}
  {U : TreeSequence G e0} {ettU : ExtendedTashkinovTree G k e0 inputU U phi}
  {baseU : HierarchyBase ettU phi} (K : TashkinovHierarchy ettU baseU),
  HierarchyPathNumber K ≤
    U.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length := by
  classical
  intro V E _ _ _ _ G k e0 phi inputU U ettU baseU K
  unfold HierarchyPathNumber
  dsimp only
  split
  · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ _)).1).2
  · exact le_rfl

private theorem helper_hbetaPresentTerminal_783.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  A.length + ell = T.length →
  ∀ (hBlen : B.length = T.length - (2 : ℕ)),
  TreeSequenceInitialSegment B T →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus),
  MaximumProperty corrMinus.replacementETT →
  ∀ (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (_ : HMinus.dividerCount = C.hierarchy.dividerCount)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
    (_ : HStar.dividerCount = C.hierarchy.dividerCount),
  TreeSequenceInitialSegment
      (HierarchyFullTailPrefix C (HierarchyFullTailLength C - (2 : ℕ))) R.minus →
  R.star.length = R.minus.length + (1 : ℕ) →
  ∀ (hminusLen : R.minus.length = B.length + (1 : ℕ)),
  R.star.length = T.length →
  ∀ (beta : Fin k),
  (
  ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S) →
  ∀ (hbetaFirstBound : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
    (_ : GoodHierarchy HMinus),
  HierarchyStarredStage HMinus (Fin.last HMinus.dividerCount) = A →
  (
  ∀ {inputU : PartialEdgeColoring E k} {U : TreeSequence G e0}
     {ettU : ExtendedTashkinovTree G k e0 inputU U phi} {baseU : HierarchyBase ettU phi}
     (K : TashkinovHierarchy ettU baseU),
  HierarchyPathNumber K ≤
    U.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length) →
  let ibeta : Fin (B.length + (1 : ℕ)) :=
    (⟨(↑(HierarchyFirstMissingPosition phi T beta) : ℕ),
        by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive B
        omega⟩ :
      Fin (B.length + (1 : ℕ)));
  beta ∈ MissingColors G phi (B.vertex ibeta) →
  beta ∉ MissingColors G phi (T.vertex D.terminalVertexIndex) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B htail hell hsum hBlen hBT R
      corrMinus hminusMP baseMinus HMinus hminusCount corrStar baseStar HStar hstarCount hBminus
      hstarLen hminusLen hstarLength beta vertexMem hbetaFirstBound goodMinus hminusStarred
      pathLeFull ibeta hbetaAtB hm
  let im : Fin (R.minus.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hBminus.1) ibeta
  have hbetaMinus : beta ∈ MissingColors G phi (R.minus.vertex im) := by
    rw [hBminus.2.1 ibeta]
    exact hbetaAtB
  have hne : R.minus.vertex im ≠ R.minus.vertex (Fin.last R.minus.length) := by
    intro heq
    have hv := congrArg Fin.val (R.minus.vertex_injective heq)
    change ibeta.val = R.minus.length at hv
    have hi := ibeta.isLt
    omega
  have hnot : ¬ ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet R.minus) := by
    intro helem
    have hd := helem (vertexMem R.minus im)
      (vertexMem R.minus (Fin.last R.minus.length)) hne
    apply Finset.disjoint_left.mp hd hbetaMinus
    rw [R.minusTerminalVertex]
    exact hm
  let CMinus : HierarchyCounterexample baseMinus := {
    positive := by simpa [corrMinus.rungAgreement] using C.positive
    hierarchy := HMinus
    good := goodMinus
    maximum := hminusMP
    notElementary := hnot }
  apply ctx.lexicographicMinimality CMinus corrMinus.rungAgreement hminusCount
  apply Or.inl
  change HierarchyPathNumber HMinus < HierarchyPathNumber H
  rw [D.pathNumberFull]
  have hp := pathLeFull HMinus
  rw [hminusStarred] at hp
  omega

private theorem helper_hstarPath_824.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
    [inst_2 : DecidableEq V] [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  ell = T.length - A.length →
  A.length + ell = T.length →
  B.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus),
  HMinus.dividerCount = C.hierarchy.dividerCount →
  ∀ (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (hstarMP : MaximumProperty corrStar.replacementETT)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar),
  HStar.dividerCount = C.hierarchy.dividerCount →
  R.star.length = R.minus.length + (1 : ℕ) →
  R.minus.length = B.length + (1 : ℕ) →
  R.star.length = T.length →
  ∀ (beta : Fin k),
  (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length →
  ∀ (goodStar : GoodHierarchy HStar),
  HierarchyStarredStage HStar (Fin.last HStar.dividerCount) = A →
  (
  ∀ {inputU : PartialEdgeColoring E k} {U : TreeSequence G e0}
     {ettU : ExtendedTashkinovTree G k e0 inputU U phi} {baseU : HierarchyBase ettU phi}
     (K : TashkinovHierarchy ettU baseU),
  HierarchyPathNumber K ≤
    U.length - (HierarchyStarredStage K (Fin.last K.dividerCount)).length) →
  let _ : HierarchyCounterexample baseStar := by
    exact
      (C.transport HStar goodStar hstarMP corrStar.rungAgreement R.starVertexSet);
  HierarchyPathNumber HStar = HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B hell hsum hBlen hBT R
      corrMinus baseMinus HMinus hminusCount corrStar hstarMP baseStar HStar hstarCount hstarLen
      hminusLen hstarLength beta hbetaFirstBound goodStar hstarStarred pathLeFull CStar
  have hle := pathLeFull HStar
  rw [hstarStarred, hstarLength] at hle
  have hnot : ¬ HierarchyPathNumber HStar < HierarchyPathNumber H := by
    intro hlt
    apply ctx.lexicographicMinimality CStar corrStar.rungAgreement hstarCount
    exact Or.inl hlt
  have hfull := D.pathNumberFull
  change HierarchyPathNumber H = ell at hfull
  omega

private theorem helper_hstarMeasure_839.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
  [inst_2 : DecidableEq V] [inst_3 : DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  ∀ (_ : B.length = T.length - (2 : ℕ)) (_ : TreeSequenceInitialSegment B T)
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (_ : HMinus.dividerCount = C.hierarchy.dividerCount)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (hstarMP : MaximumProperty corrStar.replacementETT)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
    (_ : HStar.dividerCount = C.hierarchy.dividerCount)
    (_ : R.minus.length = B.length + (1 : ℕ)),
  R.star.length = T.length →
  ∀ (beta : Fin k)
    (_ : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
    (goodStar : GoodHierarchy HStar),
  let CStar : HierarchyCounterexample baseStar := by
    exact
      (C.transport HStar goodStar hstarMP corrStar.rungAgreement R.starVertexSet);
  HierarchyPathNumber HStar = HierarchyPathNumber H →
  HStar.stage
        (⟨HStar.dividerCount,
            by
            have :=
              GoldbergSeymour.CorrespondingExtendedTashkinovTree.rungAgreement corrStar
            have := GoldbergSeymour.TreeSequence.positive T
            omega⟩ :
          Fin (HStar.dividerCount + (2 : ℕ))) =
      H.stage
        (⟨H.dividerCount, by
            have := GoldbergSeymour.TreeSequence.positive T
            omega⟩ :
          Fin (H.dividerCount + (2 : ℕ))) →
  HierarchyCounterexampleMeasure CStar = HierarchyCounterexampleMeasure C := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H ell B hBlen hBT R corrMinus baseMinus
      HMinus hminusCount corrStar hstarMP baseStar HStar hstarCount hminusLen hstarLength beta
      hbetaFirstBound goodStar CStar hstarPath hstarLastStage
  change (HierarchyPathNumber HStar,
      R.star.length - (HStar.stage ⟨HStar.dividerCount, by omega⟩).length) =
    (HierarchyPathNumber H,
      T.length - (H.stage ⟨H.dividerCount, by omega⟩).length)
  rw [hstarPath, hstarLength, hstarLastStage]

private theorem helper_prefixOfSegment_876.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) {S U : TreeSequence G e0}
  (hSU : TreeSequenceInitialSegment S U),
  TreeSequencePrefix U S.length S.positive hSU.1 = S
         := by
  classical
  intro V E G e0 S U hSU
  cases S with
  | mk ls ps vs es vis eis fs ats =>
    cases U with
    | mk lu pu vu eu viu eiu fu atu =>
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        exact hSU.2.1 i
      · apply heq_of_eq
        funext i
        exact hSU.2.2 i

private theorem helper_hstarPrefix_896.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  (2 : ℕ) ≤ ell →
  ell = T.length - A.length →
  A.length + ell = T.length →
  B.length = T.length - (2 : ℕ) →
  TreeSequenceInitialSegment B T →
  ∀
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus),
  HMinus.dividerCount = C.hierarchy.dividerCount →
  ∀ (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (hstarMP : MaximumProperty corrStar.replacementETT)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar),
  HStar.dividerCount = C.hierarchy.dividerCount →
  R.star.length = R.minus.length + (1 : ℕ) →
  TreeSequenceInitialSegment R.minus R.star →
  R.minus.length = B.length + (1 : ℕ) →
  R.star.length = T.length →
  ∀ (beta : Fin k),
  (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length →
  ∀ (goodStar : GoodHierarchy HStar),
  HierarchyStarredStage HStar (Fin.last HStar.dividerCount) = A →
  let CStar : HierarchyCounterexample baseStar := by
    exact
      @helperCStar1926 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@R)
        (@corrStar) (@hstarMP) (@baseStar) (@HStar) (@goodStar)
  (
  ∀ {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U),
  TreeSequencePrefix U S.length S.positive hSU.1 = S) →
  (
  ∀ (S : TreeSequence G e0) (i j : ℕ) (hi : (1 : ℕ) ≤ i) (hj : (1 : ℕ) ≤ j)
     (hiS : i ≤ S.length) (hjS : j ≤ S.length),
  i = j →
  TreeSequencePrefix S i hi hiS = TreeSequencePrefix S j hj hjS) →
  HierarchyFullTailPrefix CStar (HierarchyFullTailLength CStar - (1 : ℕ)) = R.minus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B htail hell hsum hBlen hBT R
      corrMinus baseMinus HMinus hminusCount corrStar hstarMP baseStar HStar hstarCount hstarLen
      hminusStar hminusLen hstarLength beta hbetaFirstBound goodStar hstarStarred CStar
      prefixOfSegment prefixLengthEq
  have hlen : min (A.length + (R.star.length - A.length - 1))
      R.star.length = R.minus.length := by omega
  unfold HierarchyFullTailPrefix HierarchyFullTailLength
  dsimp only [CStar]
  refine (prefixLengthEq R.star _ R.minus.length _ R.minus.positive _ hminusStar.1
    ?_).trans (prefixOfSegment hminusStar)
  rw [hstarStarred]
  exact hlen

private theorem helper_endpoint_1052.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
  (beta : Fin k),
  let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
  let graph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi beta D.alpha;
  ∀ (a b : V ⊕ E) (p : (TwoColorIncidenceGraph G phi beta D.alpha).Walk a b),
  p.IsPath →
  {x : V ⊕ E | x ∈ p.support} = TwoColorComponent G phi beta D.alpha (Sum.inl vb) →
  ∀ (w : V),
  Sum.inl w ∈ TwoColorComponent G phi beta D.alpha (Sum.inl vb) →
  @SimpleGraph.degree (Sum V E) graph (@Sum.inl V E w)
        (@Fintype.ofFinite
          (@Set.Elem (Sum V E)
            (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w)))
          (@Subtype.finite (Sum V E)
            (@Finite.instSum V E (@Finite.of_fintype V inst)
              (@Finite.of_fintype E inst_1))
            (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
              (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w))))) ≤
      (1 : ℕ) →
  Sum.inl w = a ∨ Sum.inl w = b := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D beta vb graph a b p hp hsupport w hw hd
  have hleaf : (graph.neighborSet (Sum.inl w)).Subsingleton := by
    let : Fintype (graph.neighborSet (Sum.inl w)) := Fintype.ofFinite _
    have hc : Fintype.card (graph.neighborSet (Sum.inl w)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hd
    intro x hx y hy
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hc ⟨x, hx⟩ ⟨y, hy⟩)
  have hwpath : Sum.inl w ∈ p.support := by
    change Sum.inl w ∈ {x | x ∈ p.support}
    rw [hsupport]
    exact hw
  by_contra hend
  push Not at hend
  exact (hp.isTrail.notMem_support_of_subsingleton_neighborSet
    hend.1 hend.2 hleaf) hwpath

private theorem helper_hendsBeta_1079.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
    (beta : Fin k),
  beta ≠ D.alpha →
  (
  ∀ (S : TreeSequence G e0),
  ∀ c ∈ TreeMissingColors phi S,
    c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c))) →
  beta ∈ TreeMissingColors phi T →
  let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
  let graph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi beta D.alpha;
  ∀ (a b : V ⊕ E),
  (
  ∀ (w : V),
  Sum.inl w ∈ TwoColorComponent G phi beta D.alpha (Sum.inl vb) →
  @SimpleGraph.degree (Sum V E) graph (@Sum.inl V E w)
        (@Fintype.ofFinite
          (@Set.Elem (Sum V E)
            (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w)))
          (@Subtype.finite (Sum V E)
            (@Finite.instSum V E (@Finite.of_fintype V inst)
              (@Finite.of_fintype E inst_1))
            (@Membership.mem (Sum V E) (Set (Sum V E))
              (@Set.instMembership (Sum V E))
              (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w))))) ≤
      (1 : ℕ) →
  Sum.inl w = a ∨ Sum.inl w = b) →
  Sum.inl vb = a ∨ Sum.inl vb = b := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D beta hcolorsDistinct firstMissingMem
      hbetaT vb graph a b endpoint
  apply endpoint vb
  · change graph.connectedComponentMk (Sum.inl vb) = graph.connectedComponentMk (Sum.inl vb)
    rfl
  · exact MissingColorIncidenceEndpoint G phi beta D.alpha hcolorsDistinct ctx.proper vb
      (firstMissingMem T beta hbetaT)

private theorem helper_hendsPenultimate_1085.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx)
    (beta : Fin k),
  TwoColorComponent G phi beta D.alpha
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
      TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex D.penultimateVertexIndex)) →
  let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
  let yp : V := T.vertex D.penultimateVertexIndex;
  let graph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi beta D.alpha;
  ∀ (a b : V ⊕ E),
  (
  ∀ (w : V),
  Sum.inl w ∈ TwoColorComponent G phi beta D.alpha (Sum.inl vb) →
  @SimpleGraph.degree (Sum V E) graph (@Sum.inl V E w)
        (@Fintype.ofFinite
          (@Set.Elem (Sum V E)
            (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w)))
          (@Subtype.finite (Sum V E)
            (@Finite.instSum V E (@Finite.of_fintype V inst)
              (@Finite.of_fintype E inst_1))
            (@Membership.mem (Sum V E) (Set (Sum V E))
              (@Set.instMembership (Sum V E))
              (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w))))) ≤
      (1 : ℕ) →
  Sum.inl w = a ∨ Sum.inl w = b) →
  (
  ∀ (w : V),
  D.alpha ∈ MissingColors G phi w →
  @SimpleGraph.degree (Sum V E) graph (@Sum.inl V E w)
      (@Fintype.ofFinite
        (@Set.Elem (Sum V E)
          (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w)))
        (@Subtype.finite (Sum V E)
          (@Finite.instSum V E (@Finite.of_fintype V inst)
            (@Finite.of_fintype E inst_1))
          (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
            (@SimpleGraph.neighborSet (Sum V E) graph (@Sum.inl V E w))))) ≤
    (1 : ℕ)) →
  Sum.inl yp = a ∨ Sum.inl yp = b := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D beta hcomponentPenultimate vb yp graph a
      b endpoint hdegreeAlpha
  apply endpoint yp
  · rw [hcomponentPenultimate]
    change graph.connectedComponentMk (Sum.inl yp) = graph.connectedComponentMk (Sum.inl yp)
    rfl
  · exact hdegreeAlpha yp D.alphaMissingPenultimate

private theorem helper_hendsTerminal_1091.{u_1, u_2} :
    helperHendsTerminal1091Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D beta hcomponentTerminal vb yt graph a b
      endpoint hdegreeAlpha
  apply endpoint yt
  · rw [hcomponentTerminal]
    change graph.connectedComponentMk (Sum.inl yt) = graph.connectedComponentMk (Sum.inl yt)
    rfl
  · exact hdegreeAlpha yt D.alphaMissingTerminal

private theorem helper_horderedStar_2907.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  ∀ (_ : (2 : ℕ) ≤ ell) (_ : ell = T.length - A.length)
    (_ : A.length + ell = T.length) (_ : B.length = T.length - (2 : ℕ))
    (_ : TreeSequenceInitialSegment B T)
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (_ : HMinus.dividerCount = C.hierarchy.dividerCount)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
    (_ : HStar.dividerCount = C.hierarchy.dividerCount)
    (_ : R.star.length = R.minus.length + (1 : ℕ))
    (hminusStar : TreeSequenceInitialSegment R.minus R.star)
    (_ : R.minus.length = B.length + (1 : ℕ))
    (_ : R.star.length = T.length) (beta : Fin k)
    (_ :
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some beta)
    (_ : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
    (_ : TreeSequenceInitialSegment B R.star)
    (_ :
  ∀ (r : Fin R.star.length) (_ : (↑r : ℕ) = B.length),
  R.star.edge r = T.edge D.lastEdgeIndex)
    (_ : HierarchyStarredStage HStar (Fin.last HStar.dividerCount) = A),
  let iaStar : Fin (R.star.length + (1 : ℕ)) :=
    Fin.castLE (Nat.succ_le_succ hminusStar.1) (Fin.last R.minus.length);
  ∀ (_ : (↑iaStar : ℕ) = R.minus.length)
    (_ : HierarchyFirstMissingPosition phi R.star D.alpha = iaStar)
    (_ : (↑(HierarchyFirstMissingPosition phi R.star beta) : ℕ) ≤ B.length),
  beta ∉
        TreeMissingColors phi
          (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)) ∨
      D.alpha ∉
        TreeMissingColors phi
          (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)) →
  TreeVertexOrder R.star (R.star.vertex (HierarchyFirstMissingPosition phi R.star beta))
      (R.star.vertex (HierarchyFirstMissingPosition phi R.star D.alpha)) ∧
  beta ∉
    ({c : Fin k |
        ∃ (t : Fin R.star.length),
          (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)).length ≤ (↑t : ℕ) ∧
            (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi R.star D.alpha) : ℕ) ∧
              phi (R.star.edge t) = some c} :
      Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B htail hell hsum hBlen hBT R
      corrMinus baseMinus HMinus hminusCount corrStar baseStar HStar hstarCount hstarLen
      hminusStar hminusLen hstarLength beta hbetaUnused hbetaFirstBound hBstar hstarFirstEdge
      hstarStarred iaStar hiaStar halphaFirstStar hbetaStarBound _
  refine ⟨?_, ?_⟩
  · refine ⟨_, _, rfl, rfl, ?_⟩
    rw [halphaFirstStar]
    omega
  · intro hm
    obtain ⟨_, t, ht, hhi, hcolor⟩ := Finset.mem_filter.mp hm
    rw [hstarStarred] at ht
    rw [halphaFirstStar] at hhi
    by_cases hbefore : t.val < B.length
    · let tb : Fin B.length := ⟨t.val, hbefore⟩
      let toriginal : Fin T.length := Fin.castLE hBT.1 tb
      have hi : Fin.castLE hBstar.1 tb = t := Fin.ext rfl
      have hedge : R.star.edge t = T.edge toriginal := by
        rw [← hi, hBstar.2.2 tb, hBT.2.2 tb]
      rw [hedge] at hcolor
      exact hbetaUnused toriginal ht hcolor
    · have heq : t.val = B.length := by omega
      rw [hstarFirstEdge t heq] at hcolor
      apply hbetaUnused D.lastEdgeIndex _ hcolor
      have hl := D.lastEdgePosition
      omega

private theorem helper_halphaStar_2928.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  ∀ (_ : B.length = T.length - (2 : ℕ)) (_ : TreeSequenceInitialSegment B T)
    (_ :
      D.alpha ∉ TreeMissingColors phi B ∧
        D.alpha ∉ Dn ∧
  ∀ (t : Fin T.length),
  A.length ≤ (↑t : ℕ) →
  phi (T.edge t) ≠ some D.alpha)
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (_ : HMinus.dividerCount = C.hierarchy.dividerCount)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
    (_ : HStar.dividerCount = C.hierarchy.dividerCount)
    (hminusStar : TreeSequenceInitialSegment R.minus R.star)
    (_ : R.minus.length = B.length + (1 : ℕ)) (beta : Fin k)
    (_ :
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ)))
    (_ : c ∈ MissingColors G phi (S.vertex i)),
  HierarchyFirstMissingPosition phi S c ≤ i)
    (_ :
  ∀ (S : TreeSequence G e0) (c : Fin k) (_ : c ∈ TreeMissingColors phi S),
  c ∈ MissingColors G phi (S.vertex (HierarchyFirstMissingPosition phi S c)))
    (_ :
  ∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S)
    (_ : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
    (_ : TreeSequenceInitialSegment B R.star),
  let iaStar : Fin (R.star.length + (1 : ℕ)) :=
    Fin.castLE (Nat.succ_le_succ hminusStar.1) (Fin.last R.minus.length);
  ∀ (_ : (↑iaStar : ℕ) = R.minus.length)
    (_ : R.star.vertex iaStar = T.vertex D.terminalVertexIndex)
    (_ : D.alpha ∈ TreeMissingColors phi R.star),
  HierarchyFirstMissingPosition phi R.star D.alpha = iaStar := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B n Dn hBlen hBT halpha R
      corrMinus baseMinus HMinus hminusCount corrStar baseStar HStar hstarCount hminusStar
      hminusLen beta firstMissingLe firstMissingMem vertexMem hbetaFirstBound hBstar iaStar
      hiaStar halphaStarVertex halphaStar
  have hm : D.alpha ∈ MissingColors G phi (R.star.vertex iaStar) := by
    rw [halphaStarVertex]
    exact D.alphaMissingTerminal
  have hle := firstMissingLe R.star D.alpha iaStar hm
  have hmFirst := firstMissingMem R.star D.alpha halphaStar
  apply Fin.ext
  change (HierarchyFirstMissingPosition phi R.star D.alpha).val ≤ iaStar.val at hle
  by_contra hne
  have hbound : (HierarchyFirstMissingPosition phi R.star D.alpha).val ≤ B.length := by
    omega
  let i : Fin (B.length + 1) :=
    ⟨(HierarchyFirstMissingPosition phi R.star D.alpha).val, by omega⟩
  have hi : Fin.castLE (Nat.succ_le_succ hBstar.1) i =
      HierarchyFirstMissingPosition phi R.star D.alpha := Fin.ext rfl
  have hmB : D.alpha ∈ MissingColors G phi (B.vertex i) := by
    rw [← hBstar.2.1 i, hi]
    exact hmFirst
  exact halpha.1 (Finset.mem_biUnion.mpr ⟨_, vertexMem B i, hmB⟩)

private theorem helper_hbetaStarVertex_3005.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  ∀ (hBlen : B.length = T.length - (2 : ℕ)) (hBT : TreeSequenceInitialSegment B T)
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (_ : HMinus.dividerCount = C.hierarchy.dividerCount)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
    (_ : HStar.dividerCount = C.hierarchy.dividerCount)
    (hminusStar : TreeSequenceInitialSegment R.minus R.star)
    (hminusLen : R.minus.length = B.length + (1 : ℕ)) (beta : Fin k)
    (hbetaFirstBound : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
    (_ : TreeSequenceInitialSegment B R.star),
  let ibeta : Fin (B.length + (1 : ℕ)) :=
    (⟨(↑(HierarchyFirstMissingPosition phi T beta) : ℕ), by
        omega⟩ :
      Fin (B.length + (1 : ℕ)));
  ∀
    (_ :
      Fin.castLE (Nat.succ_le_succ hBT.1) ibeta =
        HierarchyFirstMissingPosition phi T beta),
  let iaStar : Fin (R.star.length + (1 : ℕ)) :=
    Fin.castLE (Nat.succ_le_succ hminusStar.1) (Fin.last R.minus.length);
  ∀ (_ : (↑iaStar : ℕ) = R.minus.length)
    (_ : HierarchyFirstMissingPosition phi R.star D.alpha = iaStar)
    (_ : (↑(HierarchyFirstMissingPosition phi R.star beta) : ℕ) ≤ B.length),
  R.star.vertex (HierarchyFirstMissingPosition phi R.star beta) =
    T.vertex (HierarchyFirstMissingPosition phi T beta) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hBlen hBT R corrMinus baseMinus
      HMinus hminusCount corrStar baseStar HStar hstarCount hminusStar hminusLen beta
      hbetaFirstBound hBstar ibeta hibeta iaStar hiaStar halphaFirstStar hbetaStarBound
  have hcStar := HierarchyFirstMissingPositionPrefixCutoff
    phi B R.star hBstar beta B.length le_rfl
  have hcOld := HierarchyFirstMissingPositionPrefixCutoff
    phi B T hBT beta B.length le_rfl
  have heq : (HierarchyFirstMissingPosition phi R.star beta).val =
      (HierarchyFirstMissingPosition phi T beta).val := by omega
  have hi : Fin.castLE (Nat.succ_le_succ hBstar.1) ibeta =
      HierarchyFirstMissingPosition phi R.star beta := Fin.ext heq.symm
  rw [← hi, hBstar.2.1 ibeta, ← hBT.2.1 ibeta, hibeta]

private theorem helper_hbetaStarBound_3053.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
    (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  ∀ (hBlen : B.length = T.length - (2 : ℕ)) (_ : TreeSequenceInitialSegment B T)
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (_ : HMinus.dividerCount = C.hierarchy.dividerCount)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
    (_ : HStar.dividerCount = C.hierarchy.dividerCount)
    (_ : R.star.length = R.minus.length + (1 : ℕ))
    (hminusStar : TreeSequenceInitialSegment R.minus R.star)
    (hminusLen : R.minus.length = B.length + (1 : ℕ)) (beta : Fin k)
    (_ :
  ∀ (S : TreeSequence G e0) (c : Fin k) (i : Fin (S.length + (1 : ℕ)))
    (_ : c ∈ MissingColors G phi (S.vertex i)),
  HierarchyFirstMissingPosition phi S c ≤ i)
    (hbetaFirstBound : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length)
    (_ : TreeSequenceInitialSegment B R.star),
  let ibeta : Fin (B.length + (1 : ℕ)) :=
    (⟨(↑(HierarchyFirstMissingPosition phi T beta) : ℕ), by
        omega⟩ :
      Fin (B.length + (1 : ℕ)));
  ∀ (_ : beta ∈ MissingColors G phi (B.vertex ibeta)),
  let iaStar : Fin (R.star.length + (1 : ℕ)) :=
    Fin.castLE (Nat.succ_le_succ hminusStar.1) (Fin.last R.minus.length);
  ∀ (_ : (↑iaStar : ℕ) = R.minus.length)
    (_ : HierarchyFirstMissingPosition phi R.star D.alpha = iaStar),
  (↑(HierarchyFirstMissingPosition phi R.star beta) : ℕ) ≤ B.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hBlen hBT R corrMinus baseMinus
      HMinus hminusCount corrStar baseStar HStar hstarCount hstarLen hminusStar hminusLen beta
      firstMissingLe hbetaFirstBound hBstar ibeta hbetaAtB iaStar hiaStar halphaFirstStar
  have hm : beta ∈ MissingColors G phi
      (R.star.vertex (Fin.castLE (Nat.succ_le_succ hBstar.1) ibeta)) := by
    rw [hBstar.2.1 ibeta]
    exact hbetaAtB
  have hle := firstMissingLe R.star beta _ hm
  change (HierarchyFirstMissingPosition phi R.star beta).val ≤ ibeta.val at hle
  have hi := ibeta.isLt
  omega

private theorem helper_hpt_3177.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
  (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
  (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
  (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
  (D : HierarchySituationTwoCaseTwoData G k e0 input T phi ett base C ctx),
  let ell : ℕ := HierarchyFullTailLength C;
  let B : TreeSequence G e0 := HierarchyFullTailPrefix C (ell - (2 : ℕ));
  ∀ (_ : B.length = T.length - (2 : ℕ)) (_ : TreeSequenceInitialSegment B T)
    (R :
      HierarchySituationTwoReorderedTrees G k e0 input T phi ett base C ctx
        D.toHierarchySituationTwoTailData)
    (corrMinus : CorrespondingExtendedTashkinovTree G k e0 ett phi R.minus)
    (baseMinus : HierarchyBase corrMinus.replacementETT phi)
    (HMinus : TashkinovHierarchy corrMinus.replacementETT baseMinus)
    (_ : HMinus.dividerCount = C.hierarchy.dividerCount)
    (corrStar : CorrespondingExtendedTashkinovTree G k e0 ett phi R.star)
    (baseStar : HierarchyBase corrStar.replacementETT phi)
    (HStar : TashkinovHierarchy corrStar.replacementETT baseStar)
    (_ : HStar.dividerCount = C.hierarchy.dividerCount)
    (_ : R.star.length = R.minus.length + (1 : ℕ))
    (hminusStar : TreeSequenceInitialSegment R.minus R.star)
    (_ : R.minus.length = B.length + (1 : ℕ))
    (_ : R.star.length = T.length) (beta : Fin k)
    (_ : (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ B.length),
  let iaStar : Fin (R.star.length + (1 : ℕ)) :=
    Fin.castLE (Nat.succ_le_succ hminusStar.1) (Fin.last R.minus.length);
  ∀ (_ : (↑iaStar : ℕ) = R.minus.length)
    (_ : HierarchyFirstMissingPosition phi R.star D.alpha = iaStar),
  let yp : V := T.vertex D.penultimateVertexIndex;
  let yt : V := T.vertex D.terminalVertexIndex;
  yp ≠ yt := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D ell B hBlen hBT R corrMinus baseMinus
      HMinus hminusCount corrStar baseStar HStar hstarCount hstarLen hminusStar hminusLen
      hstarLength beta hbetaFirstBound iaStar hiaStar halphaFirstStar yp yt heq
  have hv := congrArg Fin.val (T.vertex_injective heq)
  have hp := D.penultimateVertexPosition
  have ht := D.terminalVertexPosition
  omega

private theorem helper_continuation_3768.{u_1, u_2} :
    helperContinuation3768Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B n Dn htail hell hsum hBlen
      hBT R corrMinus baseMinus HMinus hminusCount corrStar hstarMP baseStar HStar hstarCount
      hstarLen hminusStar hminusLen hstarLength beta hbetaUnused hcolorsDistinct firstMissingMem
      hbetaT hbetaFirstBound hDnDisjoint hcomponentPenultimate hBstar hstarFirstEdge terminalData
      goodStar hstarStarred ibeta hibeta CStar ctxStar hprefixStarElementary iaStar hiaStar
      halphaStarVertex halphaFirstStar hbetaStarBound hbetaStarVertex hmissingStar
  have horderedStar :
      (beta ∉ TreeMissingColors phi (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)) ∨
        D.alpha ∉ TreeMissingColors phi (HierarchyStarredStage HStar (Fin.last
            HStar.dividerCount))) →
      TreeVertexOrder R.star
        (R.star.vertex (HierarchyFirstMissingPosition phi R.star beta))
        (R.star.vertex (HierarchyFirstMissingPosition phi R.star D.alpha)) ∧
      beta ∉ (Finset.univ.filter fun c => ∃ t : Fin R.star.length,
        (HierarchyStarredStage HStar (Fin.last HStar.dividerCount)).length ≤ t.val ∧
          t.val < (HierarchyFirstMissingPosition phi R.star D.alpha).val ∧
            phi (R.star.edge t) = some c) := by
    exact @helper_horderedStar_2907 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hell) (@hsum) (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus)
        (@hminusCount) (@corrStar) (@baseStar) (@HStar) (@hstarCount) (@hstarLen) (@hminusStar)
        (@hminusLen) (@hstarLength) (@beta) (@hbetaUnused) (@hbetaFirstBound) (@hBstar)
        (@hstarFirstEdge) (@hstarStarred) (@hiaStar) (@halphaFirstStar) (@hbetaStarBound)
  have hstarDnDisjoint : Disjoint ({beta, D.alpha} : Finset (Fin k))
      (TashkinovStoredColors corrStar.replacementETT.series.data
        (Fin.last corrStar.replacementETT.rounds)) := by
    rw [(terminalData R.star corrStar).2.2]
    exact hDnDisjoint
  have hstarDnqDisjoint : Disjoint ({beta, D.alpha} : Finset (Fin k))
      (HierarchyStoredColorsAt HStar (Fin.last HStar.dividerCount)) :=
    hstarDnDisjoint.mono_right Finset.sdiff_subset
  have hchangeStar := ChangeLemma G k e0 corrStar.replacementInput R.star phi
    corrStar.replacementETT baseStar CStar ctxStar.proper ctxStar.oneEdgeUncolored
    ctxStar.lowerRung ctxStar.fewerDividers ctxStar.lexicographicMinimality
    hprefixStarElementary ctxStar.largeMissingSet beta D.alpha hcolorsDistinct
    hmissingStar horderedStar
  have hcomponentTerminal :
      TwoColorComponent G phi beta D.alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
        TwoColorComponent G phi beta D.alpha
          (Sum.inl (T.vertex D.terminalVertexIndex)) := by
    have hc : TwoColorComponent G phi beta D.alpha
          (Sum.inl (R.star.vertex (HierarchyFirstMissingPosition phi R.star beta))) =
        TwoColorComponent G phi beta D.alpha
          (Sum.inl (R.star.vertex (HierarchyFirstMissingPosition phi R.star D.alpha))) := by
      by_cases hq : 0 < HStar.dividerCount
      · exact hchangeStar.1 ⟨hq, Or.inr hstarDnqDisjoint⟩
      · have hz : HStar.dividerCount = 0 := by omega
        exact hchangeStar.2.1 ⟨hz, Or.inr hstarDnDisjoint⟩
    simpa only [hbetaStarVertex, halphaFirstStar, halphaStarVertex] using hc
  let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
  let yp := T.vertex D.penultimateVertexIndex
  let yt := T.vertex D.terminalVertexIndex
  have hbp : vb ≠ yp := by
    intro heq
    have hv := congrArg Fin.val (T.vertex_injective heq)
    have hp := D.penultimateVertexPosition
    omega
  have hbt : vb ≠ yt := by
    intro heq
    have hv := congrArg Fin.val (T.vertex_injective heq)
    have hp := D.terminalVertexPosition
    omega
  have hpt : yp ≠ yt := by
    exact @helper_hpt_3177 (@V) (@E) inferInstance inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hBlen) (@hBT) (@R)
        (@corrMinus) (@baseMinus) (@HMinus) (@hminusCount) (@corrStar) (@baseStar) (@HStar)
        (@hstarCount) (@hstarLen) (@hminusStar) (@hminusLen) (@hstarLength) (@beta)
        (@hbetaFirstBound) (@hiaStar) (@halphaFirstStar)
  let graph := TwoColorIncidenceGraph G phi beta D.alpha
  obtain ⟨a, b, p, hp, hsupport⟩ :=
    TwoColorComponentSpanningPath G phi beta D.alpha ctx.proper (Sum.inl vb)
  have endpoint (w : V)
      (hw : Sum.inl w ∈ TwoColorComponent G phi beta D.alpha (Sum.inl vb))
      (hd : @SimpleGraph.degree _ graph (Sum.inl w) (Fintype.ofFinite _) ≤ 1) :
      Sum.inl w = a ∨ Sum.inl w = b := by
    exact @helper_endpoint_1052 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@beta) (@a) (@b)
        (@p) (@hp) (@hsupport) (@w) (@hw) (@hd)
  have hgraphSwap : TwoColorIncidenceGraph G phi D.alpha beta = graph := by
    ext x y
    cases x <;> cases y <;> simp [graph, TwoColorIncidenceGraph, or_comm]
  have hdegreeAlpha (w : V) (hm : D.alpha ∈ MissingColors G phi w) :
      @SimpleGraph.degree _ graph (Sum.inl w) (Fintype.ofFinite _) ≤ 1 := by
    rw [← hgraphSwap]
    exact MissingColorIncidenceEndpoint G phi D.alpha beta hcolorsDistinct.symm ctx.proper w hm
  have hendsBeta : Sum.inl vb = a ∨ Sum.inl vb = b := by
    exact @helper_hendsBeta_1079 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@beta) (@hcolorsDistinct) (@firstMissingMem) (@hbetaT) (@a) (@b) (@endpoint)
  have hendsPenultimate : Sum.inl yp = a ∨ Sum.inl yp = b := by
    exact @helper_hendsPenultimate_1085 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@beta) (@hcomponentPenultimate) (@a) (@b) (@endpoint) (@hdegreeAlpha)
  have hendsTerminal : Sum.inl yt = a ∨ Sum.inl yt = b := by
    exact @helper_hendsTerminal_1091 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@beta) (@hcomponentTerminal) (@a) (@b) (@endpoint) (@hdegreeAlpha)
  have hbp' : Sum.inl vb ≠ (Sum.inl yp : Sum V E) := fun h => hbp (Sum.inl.inj h)
  have hbt' : Sum.inl vb ≠ (Sum.inl yt : Sum V E) := fun h => hbt (Sum.inl.inj h)
  have hpt' : Sum.inl yp ≠ (Sum.inl yt : Sum V E) := fun h => hpt (Sum.inl.inj h)
  rcases hendsBeta with hba | hbb <;>
    rcases hendsPenultimate with hpa | hpb <;>
    rcases hendsTerminal with hta | htb
  all_goals first
    | exact hbp' (hba.trans hpa.symm)
    | exact hbp' (hbb.trans hpb.symm)
    | exact hbt' (hba.trans hta.symm)
    | exact hbt' (hbb.trans htb.symm)
    | exact hpt' (hpa.trans hta.symm)
    | exact hpt' (hpb.trans htb.symm)

private theorem helper_continuation_3898.{u_1, u_2} :
    helperContinuation3898Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B n Dn htail hell hsum hBlen
      hBT halpha R corrMinus baseMinus HMinus hminusCount corrStar hstarMP baseStar HStar
      hstarCount hstarStages hBminus hstarLen hminusStar hminusLen hstarLength beta hbetaMissing
      hbetaUnused hcolorsDistinct firstMissingLe firstMissingMem vertexMem missingMono hbetaT
      hbetaFirstBound hDnDisjoint hcomponentPenultimate hBstar hstarFirstEdge terminalData
      goodStar hstarLastIndex hstarStarred ibeta hibeta hbetaAtB CStar hstarPath
  have hstarLastStage : HStar.stage ⟨HStar.dividerCount, by omega⟩ =
      H.stage ⟨H.dividerCount, by omega⟩ := by
    have h := hstarStages (Fin.last HStar.dividerCount)
    rw [hstarLastIndex] at h
    exact h
  have hstarMeasure : HierarchyCounterexampleMeasure CStar =
      HierarchyCounterexampleMeasure C := by
    exact @helper_hstarMeasure_839 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@hminusCount) (@corrStar)
        (@hstarMP) (@baseStar) (@HStar) (@hstarCount) (@hminusLen) (@hstarLength) (@beta)
        (@hbetaFirstBound) (@goodStar) (@hstarPath) (@hstarLastStage)
  let ctxStar : HierarchyMinimumCounterexampleContext G k e0
      corrStar.replacementInput R.star phi corrStar.replacementETT baseStar CStar := by
    exact {
      proper := ctx.proper
      oneEdgeUncolored := ctx.oneEdgeUncolored
      lowerRung := by
        intro input' T' generating' lower hpos hlt hmax
        apply ctx.lowerRung lower hpos
        · simpa [corrStar.rungAgreement] using hlt
        · exact hmax
      fewerDividers := by
        intro input' T' generating' other hr hmax base' K goodK hdiv
        apply ctx.fewerDividers other (hr.trans corrStar.rungAgreement) hmax base' K goodK
        change K.dividerCount < HStar.dividerCount at hdiv
        rwa [hstarCount] at hdiv
      lexicographicMinimality := by
        intro input' T' generating' other base' C' hr hc
        rw [hstarMeasure]
        exact ctx.lexicographicMinimality C' (hr.trans corrStar.rungAgreement)
          (hc.trans hstarCount)
      largeMissingSet := by
        dsimp only
        rw [(terminalData R.star corrStar).1, corrStar.rungAgreement]
        exact ctx.largeMissingSet }
  have hprefixStarElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyFullTailPrefix CStar
        (HierarchyFullTailLength CStar - 1))) :=
    HierarchyCounterexamplePenultimateElementary
      G k e0 corrStar.replacementInput R.star phi corrStar.replacementETT baseStar CStar
      ctxStar.proper ctxStar.oneEdgeUncolored ctxStar.lowerRung ctxStar.fewerDividers
      ctxStar.lexicographicMinimality ctxStar.largeMissingSet
  have prefixOfSegment {S U : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) :
      TreeSequencePrefix U S.length S.positive hSU.1 = S := by
    exact @helper_prefixOfSegment_876 (@V) (@E) (@G) (@e0) (@S) (@U) (@hSU)
  have prefixLengthEq (S : TreeSequence G e0) (i j : ℕ)
      (hi : 1 ≤ i) (hj : 1 ≤ j) (hiS : i ≤ S.length) (hjS : j ≤ S.length)
      (hij : i = j) : TreeSequencePrefix S i hi hiS = TreeSequencePrefix S j hj hjS := by
    cases hij
    rfl
  have hstarPrefix : HierarchyFullTailPrefix CStar
      (HierarchyFullTailLength CStar - 1) = R.minus := by
    exact @helper_hstarPrefix_896 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hell) (@hsum) (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus)
        (@hminusCount) (@corrStar) (@hstarMP) (@baseStar) (@HStar) (@hstarCount) (@hstarLen)
        (@hminusStar) (@hminusLen) (@hstarLength) (@beta) (@hbetaFirstBound) (@goodStar)
        (@hstarStarred) (@prefixOfSegment) (@prefixLengthEq)
  have hminusElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet R.minus) := by
    change ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyFullTailPrefix CStar
        (HierarchyFullTailLength CStar - 1))) at hprefixStarElementary
    rwa [hstarPrefix] at hprefixStarElementary
  let iaStar : Fin (R.star.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hminusStar.1) (Fin.last R.minus.length)
  have hiaStar : iaStar.val = R.minus.length := rfl
  have halphaStarVertex : R.star.vertex iaStar = T.vertex D.terminalVertexIndex :=
    (hminusStar.2.1 (Fin.last R.minus.length)).trans R.minusTerminalVertex
  have halphaMinus : D.alpha ∈ TreeMissingColors phi R.minus :=
    Finset.mem_biUnion.mpr ⟨_, vertexMem R.minus (Fin.last R.minus.length),
      R.minusTerminalVertex.symm ▸ D.alphaMissingTerminal⟩
  have halphaStar : D.alpha ∈ TreeMissingColors phi R.star :=
    missingMono hminusStar halphaMinus
  have halphaFirstStar : HierarchyFirstMissingPosition phi R.star D.alpha = iaStar := by
    exact @helper_halphaStar_2928 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@halpha) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@hminusCount)
        (@corrStar) (@baseStar) (@HStar) (@hstarCount) (@hminusStar) (@hminusLen) (@beta)
        (@firstMissingLe) (@firstMissingMem) (@vertexMem) (@hbetaFirstBound) (@hBstar) (@hiaStar)
        (@halphaStarVertex) (@halphaStar)
  have hbetaStarBound : (HierarchyFirstMissingPosition phi R.star beta).val ≤ B.length := by
    exact @helper_hbetaStarBound_3053 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@hminusCount) (@corrStar)
        (@baseStar) (@HStar) (@hstarCount) (@hstarLen) (@hminusStar) (@hminusLen) (@beta)
        (@firstMissingLe) (@hbetaFirstBound) (@hBstar) (@hbetaAtB) (@hiaStar) (@halphaFirstStar)
  have hbetaStarVertex :
      R.star.vertex (HierarchyFirstMissingPosition phi R.star beta) =
        T.vertex (HierarchyFirstMissingPosition phi T beta) := by
    exact @helper_hbetaStarVertex_3005 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@hminusCount) (@corrStar)
        (@baseStar) (@HStar) (@hstarCount) (@hminusStar) (@hminusLen) (@beta) (@hbetaFirstBound)
        (@hBstar) (@hibeta) (@hiaStar) (@halphaFirstStar) (@hbetaStarBound)
  have hbetaMinus : beta ∈ TreeMissingColors phi R.minus := missingMono hBminus hbetaMissing
  have hmissingStar :
      beta ∈ TreeMissingColors phi (HierarchyFullTailPrefix CStar
        (HierarchyFullTailLength CStar - 1)) ∧
      D.alpha ∈ TreeMissingColors phi (HierarchyFullTailPrefix CStar
        (HierarchyFullTailLength CStar - 1)) := by
    rw [hstarPrefix]
    exact ⟨hbetaMinus, halphaMinus⟩
  exact @helper_continuation_3768 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hell) (@hsum) (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@hminusCount)
      (@corrStar) (@hstarMP) (@baseStar) (@HStar) (@hstarCount) (@hstarLen) (@hminusStar)
      (@hminusLen) (@hstarLength) (@beta) (@hbetaUnused) (@hcolorsDistinct) (@firstMissingMem)
      (@hbetaT) (@hbetaFirstBound) (@hDnDisjoint) (@hcomponentPenultimate) (@hBstar)
      (@hstarFirstEdge) (@terminalData) (@goodStar) (@hstarStarred) (@hibeta) (@ctxStar)
      (@hprefixStarElementary) (@hiaStar) (@halphaStarVertex) (@halphaFirstStar)
      (@hbetaStarBound) (@hbetaStarVertex) (@hmissingStar)

private theorem helper_continuation_4102.{u_1, u_2} :
    helperContinuation4102Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B n Dn htail hell hsum hBlen
      hBT halpha R corrMinus hminusMP baseMinus hminusCore hminusClosure HMinus hminusCount
      hminusStages corrStar hstarMP baseStar hstarCore hstarClosure HStar hstarCount hstarStages
      hBminus hstarLen hminusStar hminusLen hstarLength beta hbetaMissing hbetaUnused
      hcolorsDistinct firstMissingLe firstMissingMem vertexMem missingMono hbetaT hbetaFirstBound
      hDnDisjoint hcomponentPenultimate hminusTerminalAvoidance hBstar hstarFirstEdge
      hstarTerminalAvoidance terminalData copyGood
  obtain ⟨goodMinus, hgammaMinus⟩ := copyGood R.minus corrMinus baseMinus
    hminusCore hminusClosure HMinus hminusCount hminusStages hBminus
    hminusTerminalAvoidance
  obtain ⟨goodStar, hgammaStar⟩ := copyGood R.star corrStar baseStar
    hstarCore hstarClosure HStar hstarCount hstarStages hBstar
    hstarTerminalAvoidance
  have starredTransfer {inputU : PartialEdgeColoring E k}
      {U : TreeSequence G e0}
      {ettU : ExtendedTashkinovTree G k e0 inputU U phi}
      {baseU : HierarchyBase ettU phi}
      (K : TashkinovHierarchy ettU baseU)
      (hcore : baseU.core = base.core) (hc : K.dividerCount = H.dividerCount)
      (hs : ∀ j : Fin (K.dividerCount + 1), K.stage j.castSucc =
        H.stage (Fin.cast (congrArg (fun d => d + 1) hc) j).castSucc)
      (j : Fin (K.dividerCount + 1)) :
      HierarchyStarredStage K j =
        HierarchyStarredStage H (Fin.cast (congrArg (fun d => d + 1) hc) j) := by
    exact @helper_starredTransfer_726 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@inputU) (@U)
        (@ettU) (@baseU) (@K) (@hcore) (@hc) (@hs) (@j)
  have hminusLastIndex : Fin.cast (congrArg (fun d => d + 1) hminusCount)
      (Fin.last HMinus.dividerCount) = q := by
    apply Fin.ext
    simp [q, H]
  have hstarLastIndex : Fin.cast (congrArg (fun d => d + 1) hstarCount)
      (Fin.last HStar.dividerCount) = q := by
    apply Fin.ext
    simp [q, H]
  have hminusStarred : HierarchyStarredStage HMinus
      (Fin.last HMinus.dividerCount) = A := by
    simpa only [hminusLastIndex] using starredTransfer HMinus hminusCore
      hminusCount hminusStages (Fin.last HMinus.dividerCount)
  have hstarStarred : HierarchyStarredStage HStar
      (Fin.last HStar.dividerCount) = A := by
    simpa only [hstarLastIndex] using starredTransfer HStar hstarCore
      hstarCount hstarStages (Fin.last HStar.dividerCount)
  have pathLeFull {inputU : PartialEdgeColoring E k}
      {U : TreeSequence G e0}
      {ettU : ExtendedTashkinovTree G k e0 inputU U phi}
      {baseU : HierarchyBase ettU phi} (K : TashkinovHierarchy ettU baseU) :
      HierarchyPathNumber K ≤ U.length -
        (HierarchyStarredStage K (Fin.last K.dividerCount)).length := by
    exact @helper_pathLeFull_765 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@inputU) (@U) (@ettU) (@baseU) (@K)
  let ibeta : Fin (B.length + 1) :=
    ⟨(HierarchyFirstMissingPosition phi T beta).val, by omega⟩
  have hibeta : Fin.castLE (Nat.succ_le_succ hBT.1) ibeta =
      HierarchyFirstMissingPosition phi T beta := Fin.ext rfl
  have hbetaAtB : beta ∈ MissingColors G phi (B.vertex ibeta) := by
    rw [← hBT.2.1 ibeta, hibeta]
    exact firstMissingMem T beta hbetaT
  have hbetaPresentTerminal : beta ∉ MissingColors G phi
      (T.vertex D.terminalVertexIndex) := by
    exact @helper_hbetaPresentTerminal_783 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hell) (@hsum) (@hBlen) (@hBT) (@R) (@corrMinus) (@hminusMP) (@baseMinus)
        (@HMinus) (@hminusCount) (@corrStar) (@baseStar) (@HStar) (@hstarCount) (@hBminus)
        (@hstarLen) (@hminusLen) (@hstarLength) (@beta) (@vertexMem) (@hbetaFirstBound)
        (@goodMinus) (@hminusStarred) (@pathLeFull) (@hbetaAtB)
  let CStar : HierarchyCounterexample baseStar :=
    (C.transport HStar goodStar hstarMP corrStar.rungAgreement R.starVertexSet)
  have hstarPath : HierarchyPathNumber HStar = HierarchyPathNumber H := by
    exact @helper_hstarPath_824 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hell) (@hsum) (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@hminusCount)
        (@corrStar) (@hstarMP) (@baseStar) (@HStar) (@hstarCount) (@hstarLen) (@hminusLen)
        (@hstarLength) (@beta) (@hbetaFirstBound) (@goodStar) (@hstarStarred) (@pathLeFull)
  exact @helper_continuation_3898 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hell) (@hsum) (@hBlen) (@hBT) (@halpha) (@R) (@corrMinus) (@baseMinus) (@HMinus)
      (@hminusCount) (@corrStar) (@hstarMP) (@baseStar) (@HStar) (@hstarCount) (@hstarStages)
      (@hBminus) (@hstarLen) (@hminusStar) (@hminusLen) (@hstarLength) (@beta) (@hbetaMissing)
      (@hbetaUnused) (@hcolorsDistinct) (@firstMissingLe) (@firstMissingMem) (@vertexMem)
      (@missingMono) (@hbetaT) (@hbetaFirstBound) (@hDnDisjoint) (@hcomponentPenultimate)
      (@hBstar) (@hstarFirstEdge) (@terminalData) (@goodStar) (@hstarLastIndex) (@hstarStarred)
      (@hibeta) (@hbetaAtB) (@hstarPath)

private theorem helper_continuation_4235.{u_1, u_2} :
    helperContinuation4235Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D H q A ell B n Dn htail hell hsum hBlen
      hBT halpha R corrMinus hminusMP baseMinus hminusCore hminusClosure HMinus hminusCount
      hminusStages corrStar hstarMP baseStar hstarCore hstarClosure HStar hstarCount hstarStages
      hBminus hstarLen hminusStar hstarEdge hminusLen hstarLength beta hbetaMissing hbetaUnused
      hcolorsDistinct firstMissingLe firstMissingMem vertexMem missingMono hbetaT hbetaFirstBound
      hDnDisjoint hcomponentPenultimate terminalAvoidance hminusFirstEdge hminusTerminalAvoidance
      hBstar
  have hstarFirstEdge (r : Fin R.star.length) (hr : r.val = B.length) :
      R.star.edge r = T.edge D.lastEdgeIndex := by
    let rm : Fin R.minus.length := ⟨r.val, by omega⟩
    have hi : Fin.castLE hminusStar.1 rm = r := Fin.ext rfl
    rw [← hi, hminusStar.2.2 rm]
    exact hminusFirstEdge rm hr
  have hstarSecondEdge (r : Fin R.star.length) (hr : r.val = B.length + 1) :
      R.star.edge r = T.edge R.penultimateEdgeIndex := by
    exact @helper_hstarSecondEdge_484 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar)
        (@hstarLen) (@hstarEdge) (@hminusLen) (@beta) (@r) (@hr)
  have hstarTerminalAvoidance := terminalAvoidance R.star hBstar (by omega)
    hstarFirstEdge hstarSecondEdge
  have terminalData (U : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U) :
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc =
          ett.series.data.tree n.castSucc ∧
        corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind n ∧
        TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) = Dn := by
    exact corr.terminalData
  have hApositive (hq : 0 < H.dividerCount) : A = H.stage q.castSucc := by
    exact @helper_hApositive_533 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@R)
        (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@beta) (@hq)
  have stageLengthMono : Monotone (fun j => (H.stage j).length) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    exact (H.nested j).1
  have copyGood (U : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi U)
      (baseU : HierarchyBase corr.replacementETT phi)
      (hcore : baseU.core = base.core) (hclosure : baseU.closure = base.closure)
      (K : TashkinovHierarchy corr.replacementETT baseU)
      (hcount : K.dividerCount = H.dividerCount)
      (hstages : ∀ j : Fin (K.dividerCount + 1),
        K.stage j.castSucc =
          H.stage (Fin.cast (congrArg (fun d => d + 1) hcount) j).castSucc)
      (hBU : TreeSequenceInitialSegment B U)
      (havoid : ∀ eta ∈ HierarchyStoredColorsAt H q,
        Disjoint (C.good.gamma q eta)
          (Finset.univ.filter fun c => ∃ r : Fin U.length,
            A.length ≤ r.val ∧
              r.val < min (HierarchyFirstMissingPosition phi U eta).val U.length ∧
                phi (U.edge r) = some c)) :
      ∃ goodU : GoodHierarchy K,
        ∀ j eta, goodU.gamma j eta =
          C.good.gamma (Fin.cast (congrArg (fun d => d + 1) hcount) j) eta := by
    let index (j : Fin (K.dividerCount + 1)) : Fin (H.dividerCount + 1) :=
      Fin.cast (congrArg (fun d => d + 1) hcount) j
    let gammaU := fun j eta => C.good.gamma (index j) eta
    have hdata := terminalData U corr
    have stageEq (j : Fin (K.dividerCount + 1)) :
        K.stage j.castSucc = H.stage (index j).castSucc := hstages j
    have starredEq (j : Fin (K.dividerCount + 1)) :
        HierarchyStarredStage K j = HierarchyStarredStage H (index j) := by
      exact @helper_starredEq_570 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@U) (@corr)
          (@baseU) (@hcore) (@K) (@hcount) (@stageEq) (@j)
    have storedEq (j : Fin (K.dividerCount + 1)) :
        HierarchyStoredColorsAt K j = HierarchyStoredColorsAt H (index j) := by
      unfold HierarchyStoredColorsAt
      dsimp only
      rw [hdata.2.2, starredEq j]
    have missingEq (j : Fin (K.dividerCount + 1)) :
        HierarchyStageMissingColors K j = HierarchyStageMissingColors H (index j) := by
      exact @helper_missingEq_587 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@U) (@corr)
          (@baseU) (@K) (@hcount) (@hdata) (@stageEq) (@j)
    have segmentEqInternal (i : Fin K.dividerCount) (eta : Fin k) :
        HierarchySegmentColors K i.castSucc eta =
          HierarchySegmentColors H (index i.castSucc) eta := by
      exact @helper_segmentEqInternal_600 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
          (@htail) (@hell) (@hsum) (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus)
          (@corrStar) (@baseStar) (@HStar) (@hstarLen) (@hminusLen) (@hstarLength) (@beta)
          (@hApositive) (@stageLengthMono) (@U) (@corr) (@baseU) (@K) (@hcount) (@hBU) (@stageEq)
          (@starredEq) (@i) (@eta)
    have indexLast : index (Fin.last K.dividerCount) = q := by
      apply Fin.ext
      simp [index, q]
    have terminalSegmentEq (eta : Fin k) :
        HierarchySegmentColors K (Fin.last K.dividerCount) eta =
          Finset.univ.filter (fun c => ∃ r : Fin U.length,
            A.length ≤ r.val ∧
              r.val < min (HierarchyFirstMissingPosition phi U eta).val U.length ∧
                phi (U.edge r) = some c) := by
      exact @helper_terminalSegmentEq_627 (@V) (@E) inferInstance inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@U) (@corr)
          (@baseU) (@K) (@hcount) (@starredEq) (@indexLast) (@eta)
    let goodU : GoodHierarchy K := by
      exact @helperGoodU2513 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@R) (@corrMinus)
          (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@beta) (@U) (@corr) (@baseU)
          (@hcore) (@hclosure) (@K) (@hcount) (@havoid) (@hdata) (@stageEq) (@starredEq)
          (@storedEq) (@missingEq) (@segmentEqInternal) (@indexLast) (@terminalSegmentEq)
    exact ⟨goodU, by intro j eta; rfl⟩
  exact @helper_continuation_4102 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hell) (@hsum) (@hBlen) (@hBT) (@halpha) (@R) (@corrMinus) (@hminusMP) (@baseMinus)
      (@hminusCore) (@hminusClosure) (@HMinus) (@hminusCount) (@hminusStages) (@corrStar)
      (@hstarMP) (@baseStar) (@hstarCore) (@hstarClosure) (@HStar) (@hstarCount) (@hstarStages)
      (@hBminus) (@hstarLen) (@hminusStar) (@hminusLen) (@hstarLength) (@beta) (@hbetaMissing)
      (@hbetaUnused) (@hcolorsDistinct) (@firstMissingLe) (@firstMissingMem) (@vertexMem)
      (@missingMono) (@hbetaT) (@hbetaFirstBound) (@hDnDisjoint) (@hcomponentPenultimate)
      (@hminusTerminalAvoidance) (@hBstar) (@hstarFirstEdge) (@hstarTerminalAvoidance)
      (@terminalData) (@copyGood)

private theorem helper_continuation_4495.{u_1, u_2} :
    helperContinuation4495Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx D hnonexceptional H q A ell B Bplus n Dn
      htail hell hsum hBlen hBT hprefixElementary halpha R corrMinus hminusMP baseMinus
      hminusCore hminusClosure HMinus hminusCount hminusStages corrStar hstarMP baseStar
      hstarCore hstarClosure HStar hstarCount hstarStages hBminus hstarLen hminusStar hstarEdge
      hminusLen hminusEdge hstarLength beta hbetaMissing hbetaUnused hcolorsDistinct
      firstMissingLe firstMissingMem vertexMem missingMono hbetaT hbetaFirstBound halphaFirst
      hbetaPrefix halphaPrefix horderedUnused hDnDisjoint hDnqDisjoint
  have hchange := ChangeLemma G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hprefixElementary ctx.largeMissingSet
    beta D.alpha hcolorsDistinct ⟨hbetaPrefix, halphaPrefix⟩ horderedUnused
  have hcomponentPenultimate :
      TwoColorComponent G phi beta D.alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition phi T beta))) =
        TwoColorComponent G phi beta D.alpha
          (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
    apply helper_hcomponentPenultimate_325 <;> assumption
  have firstMissingMemBelow (S : TreeSequence G e0) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition phi S c).val < S.length) :
      c ∈ MissingColors G phi
        (S.vertex (HierarchyFirstMissingPosition phi S c)) := by
    exact @helper_firstMissingMemBelow_339 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@R)
        (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@beta) (@S) (@c)
        (@hlt)
  -- A strict cutoff inside the common prefix also holds in the old display.
  have firstLowerInOld (U : TreeSequence G e0)
      (hBU : TreeSequenceInitialSegment B U) (eta : Fin k) (r : ℕ)
      (hrB : r ≤ B.length)
      (hrU : r < (HierarchyFirstMissingPosition phi U eta).val) :
      r < (HierarchyFirstMissingPosition phi T eta).val := by
    exact (@helper_firstLowerInOld_356 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@hBlen) (@hBT)
        (@R) (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@hstarLen)
        (@hminusLen) (@hstarLength) (@eta) (@firstMissingLe) (@firstMissingMemBelow) (@U) (@hBU)
        (@eta) (@r) (@hrB) (@hrU))
  have oldSegmentMember (eta c : Fin k) (r : Fin T.length)
      (hlo : A.length ≤ r.val)
      (hhi : r.val < (HierarchyFirstMissingPosition phi T eta).val)
      (hcolor : phi (T.edge r) = some c) :
      c ∈ HierarchySegmentColors H q eta := by
    apply helper_oldSegmentMember_377 <;> assumption
  have terminalAvoidance (U : TreeSequence G e0)
      (hBU : TreeSequenceInitialSegment B U)
      (hlen : U.length ≤ B.length + 2)
      (hfirstEdge : ∀ r : Fin U.length, r.val = B.length →
        U.edge r = T.edge D.lastEdgeIndex)
      (hsecondEdge : ∀ r : Fin U.length, r.val = B.length + 1 →
        U.edge r = T.edge R.penultimateEdgeIndex) :
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        Disjoint (C.good.gamma q eta)
          (Finset.univ.filter fun c => ∃ r : Fin U.length,
            A.length ≤ r.val ∧
              r.val < min (HierarchyFirstMissingPosition phi U eta).val U.length ∧
                phi (U.edge r) = some c) := by
    exact @helper_terminalAvoidance_394 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hnonexceptional) (@htail) (@hell) (@hsum) (@hBlen) (@hBT) (@R) (@corrMinus)
        (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar) (@hstarLen) (@hminusLen)
        (@hstarLength) (@beta) (@firstMissingMemBelow) (@firstLowerInOld) (@oldSegmentMember)
        (@U) (@hBU) (@hlen) (@hfirstEdge) (@hsecondEdge)
  have hminusFirstEdge (r : Fin R.minus.length) (hr : r.val = B.length) :
      R.minus.edge r = T.edge D.lastEdgeIndex := by
    have hi : r = Fin.cast hminusLen.symm (Fin.last B.length) := by
      apply Fin.ext
      exact hr
    rw [hi]
    exact hminusEdge
  have hminusTerminalAvoidance := terminalAvoidance R.minus hBminus (by omega)
    hminusFirstEdge (by
      intro r hr
      have hi := r.isLt
      omega)
  have hBstar : TreeSequenceInitialSegment B R.star := by
    exact @helper_hBstar_471 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@R) (@hBminus)
        (@hminusStar)
  exact @helper_continuation_4235 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D) (@htail)
      (@hell) (@hsum) (@hBlen) (@hBT) (@halpha) (@R) (@corrMinus) (@hminusMP) (@baseMinus)
      (@hminusCore) (@hminusClosure) (@HMinus) (@hminusCount) (@hminusStages) (@corrStar)
      (@hstarMP) (@baseStar) (@hstarCore) (@hstarClosure) (@HStar) (@hstarCount) (@hstarStages)
      (@hBminus) (@hstarLen) (@hminusStar) (@hstarEdge) (@hminusLen) (@hstarLength) (@beta)
      (@hbetaMissing) (@hbetaUnused) (@hcolorsDistinct) (@firstMissingLe) (@firstMissingMem)
      (@vertexMem) (@missingMono) (@hbetaT) (@hbetaFirstBound) (@hDnDisjoint)
      (@hcomponentPenultimate) (@terminalAvoidance) (@hminusFirstEdge) (@hminusTerminalAvoidance)
      (@hBstar)

theorem HierarchySituationTwoSubcaseTwoOneNonexceptional {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData
      G k e0 input T phi ett base C ctx)
    (hnonexceptional :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      ¬ ∃ eta, eta ∈ HierarchyStoredColorsAt H q ∧
        eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex) ∧
        D.theta ∈ C.good.gamma q eta) :
    False := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let Bplus := HierarchyFullTailPrefix C (ell - 1)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Dn := TashkinovStoredColors ett.series.data n
  have htail : 2 ≤ ell := D.tailAtLeastTwo
  have hell : ell = T.length - A.length := rfl
  have hsum : A.length + ell = T.length := by omega
  have hBlen : B.length = T.length - 2 := by
    change min (A.length + (ell - 2)) T.length = T.length - 2
    omega
  have hBpluslen : Bplus.length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    omega
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
  have hBplusT : TreeSequenceInitialSegment Bplus T :=
    ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
  have hBBplus : TreeSequenceInitialSegment B Bplus :=
    ⟨by omega, (by intro i; rfl), (by intro i; rfl)⟩
  have hprefixElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet Bplus) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have halpha := HierarchySituationTwoCaseTwoExclusions
    G k e0 input T phi ett base C ctx D
  change D.alpha ∉ TreeMissingColors phi B ∧ D.alpha ∉ Dn ∧
    ∀ t : Fin T.length, A.length ≤ t.val →
      phi (T.edge t) ≠ some D.alpha at halpha
  obtain ⟨R, hroute, hminusRoute, hstarRoute,
    corrMinus, hminusMP, baseMinus, hminusCore, hminusClosure,
    hminusSupport, HMinus, hminusCount, hminusStages, hminusPositions,
    corrStar, hstarMP, baseStar, hstarCore, hstarClosure,
    hstarSupport, HStar, hstarCount, hstarStages, hstarPositions⟩ :=
    HierarchySituationTwoReorderedTreesCertified
      G k e0 input T phi ett base C ctx D.toHierarchySituationTwoTailData
  obtain ⟨hminusLen, hBminus, hminusEdge⟩ := R.minusFinal
  obtain ⟨hstarLen, hminusStar, hstarEdge⟩ := R.starFinal
  change R.minus.length = B.length + 1 at hminusLen
  have hminusLength : R.minus.length = T.length - 1 := by omega
  have hstarLength : R.star.length = T.length := by omega
  let baseExtraMissing :=
    (TreeSequenceVertexSet base.core \
      TreeSequenceVertexSet (ett.series.data.tree n.castSucc)).biUnion
        fun v => MissingColors G phi v
  let prefixUsed : Finset (Fin k) := Finset.univ.filter fun c =>
    ∃ r : Fin T.length, A.length ≤ r.val ∧
      r.val < A.length + (ell - 2) ∧ phi (T.edge r) = some c
  let available := (TreeMissingColors phi B \ baseExtraMissing) \ prefixUsed
  have havailable : 2 * ett.rounds + 11 ≤ available.card :=
    (NineN G k e0 input T phi ett C.positive base H C.good
      hprefixElementary ctx.largeMissingSet (ell - 2)
      (by change ell - 2 < ell; omega)).1
  -- Only the two exact final edges are added to the used-color exclusion.
  let finalColors : Finset (Fin k) :=
    (Finset.univ.filter fun c =>
      phi (T.edge R.penultimateEdgeIndex) = some c) ∪
    (Finset.univ.filter fun c => phi (T.edge D.lastEdgeIndex) = some c)
  have singleColorCard (f : E) :
      (Finset.univ.filter fun c => phi f = some c).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact Option.some.inj ((Finset.mem_filter.mp ha).2.symm.trans
      (Finset.mem_filter.mp hb).2)
  have hfinalCard : finalColors.card ≤ 2 := by
    apply helper_hfinalCard_138 <;> assumption
  have hDnCard : Dn.card ≤ ett.rounds := by
    simpa [Dn, n] using TashkinovStoredColorsCardinality
      G k ett.rounds e0 input ett.series n
  have hremaining : ett.rounds + 9 ≤
      ((available \ finalColors) \ Dn).card := by
    apply helper_hremaining_149 <;> assumption
  have hnonempty : ((available \ finalColors) \ Dn).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨beta, hbeta⟩ := hnonempty
  obtain ⟨hbetaAvailableFinal, hbetaDn⟩ := Finset.mem_sdiff.mp hbeta
  obtain ⟨hbetaAvailable, hbetaFinal⟩ := Finset.mem_sdiff.mp hbetaAvailableFinal
  obtain ⟨hbetaMissingExtra, hbetaPrefixUnused⟩ := Finset.mem_sdiff.mp hbetaAvailable
  obtain ⟨hbetaMissing, hbetaExtra⟩ := Finset.mem_sdiff.mp hbetaMissingExtra
  have hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
      phi (T.edge t) ≠ some beta := by
    exact @helper_hbetaUnused_164 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@htail) (@hell) (@hsum) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar)
        (@HStar) (@hstarLen) (@hstarLength) (@beta) (@hbetaFinal) (@hbetaPrefixUnused)
  have hcolorsDistinct : beta ≠ D.alpha := by
    intro heq
    exact halpha.1 (heq ▸ hbetaMissing)
  have firstMissingLe (S : TreeSequence G e0) (c : Fin k)
      (i : Fin (S.length + 1))
      (hc : c ∈ MissingColors G phi (S.vertex i)) :
      HierarchyFirstMissingPosition phi S c ≤ i := by
    apply helper_firstMissingLe_188; assumption
  have firstMissingMem (S : TreeSequence G e0) (c : Fin k)
      (hc : c ∈ TreeMissingColors phi S) :
      c ∈ MissingColors G phi
        (S.vertex (HierarchyFirstMissingPosition phi S c)) := by
    apply helper_firstMissingMem_201; assumption
  have vertexMem (S : TreeSequence G e0) (i : Fin (S.length + 1)) :
      S.vertex i ∈ TreeSequenceVertexSet S := by
    simpa only [TreeSequenceVertexSet] using
      ((@Finset.mem_image _ _ (Classical.decEq V)).mpr
        ⟨i, Finset.mem_univ _, rfl⟩)
  have missingMono {S U : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) :
      TreeMissingColors phi S ⊆ TreeMissingColors phi U := by
    apply helper_missingMono_224; assumption
  have hbetaT : beta ∈ TreeMissingColors phi T := missingMono hBT hbetaMissing
  have halphaT : D.alpha ∈ TreeMissingColors phi T :=
    Finset.mem_biUnion.mpr
      ⟨_, vertexMem T D.penultimateVertexIndex, D.alphaMissingPenultimate⟩
  have hbetaFirstBound : (HierarchyFirstMissingPosition phi T beta).val ≤ B.length := by
    exact @helper_hbetaFirstBound_243 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar)
        (@hstarLen) (@hminusLen) (@hstarLength) (@beta) (@hbetaMissing) (@firstMissingLe)
  have halphaFirst : HierarchyFirstMissingPosition phi T D.alpha =
      D.penultimateVertexIndex := by
    exact @helper_halphaFirst_256 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@hBT) (@halpha) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@corrStar)
        (@baseStar) (@HStar) (@hstarLen) (@hminusLen) (@hstarLength) (@beta) (@firstMissingLe)
        (@firstMissingMem) (@vertexMem) (@halphaT)
  have hbetaPrefix : beta ∈ TreeMissingColors phi Bplus :=
    missingMono hBBplus hbetaMissing
  have halphaPrefix : D.alpha ∈ TreeMissingColors phi Bplus := by
    exact @helper_halphaPrefix_278 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBpluslen) (@hBplusT) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar)
        (@HStar) (@hstarLen) (@hminusLength) (@hstarLength) (@beta) (@vertexMem)
  have horderedUnused :
      (beta ∉ TreeMissingColors phi A ∨ D.alpha ∉ TreeMissingColors phi A) →
        TreeVertexOrder T
          (T.vertex (HierarchyFirstMissingPosition phi T beta))
          (T.vertex (HierarchyFirstMissingPosition phi T D.alpha)) ∧
        beta ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
          A.length ≤ t.val ∧
            t.val < (HierarchyFirstMissingPosition phi T D.alpha).val ∧
              phi (T.edge t) = some c) := by
    exact @helper_horderedUnused_290 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@hBlen) (@R) (@corrMinus) (@baseMinus) (@HMinus) (@corrStar) (@baseStar) (@HStar)
        (@hstarLen) (@hminusLen) (@hstarLength) (@beta) (@hbetaUnused) (@hbetaFirstBound)
        (@halphaFirst)
  have hDnDisjoint : Disjoint ({beta, D.alpha} : Finset (Fin k)) Dn := by
    exact @helper_hDnDisjoint_310 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
        (@halpha) (@R) (@beta) (@hbeta) (@hbetaAvailableFinal) (@hbetaDn) (@hbetaAvailable)
        (@hbetaFinal) (@hbetaMissingExtra) (@hbetaPrefixUnused) (@hbetaMissing) (@hbetaExtra)
        (@hbetaUnused) (@hcolorsDistinct) (@hbetaT) (@hbetaFirstBound) (@hbetaPrefix)
        (@horderedUnused)
  have hDnqDisjoint : Disjoint ({beta, D.alpha} : Finset (Fin k))
      (HierarchyStoredColorsAt H q) := by
    apply hDnDisjoint.mono_right
    exact Finset.sdiff_subset
  exact @helper_continuation_4495 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@ctx) (@D)
      (@hnonexceptional) (@htail) (@hell) (@hsum) (@hBlen) (@hBT) (@hprefixElementary) (@halpha)
      (@R) (@corrMinus) (@hminusMP) (@baseMinus) (@hminusCore) (@hminusClosure) (@HMinus)
      (@hminusCount) (@hminusStages) (@corrStar) (@hstarMP) (@baseStar) (@hstarCore)
      (@hstarClosure) (@HStar) (@hstarCount) (@hstarStages) (@hBminus) (@hstarLen) (@hminusStar)
      (@hstarEdge) (@hminusLen) (@hminusEdge) (@hstarLength) (@beta) (@hbetaMissing)
      (@hbetaUnused) (@hcolorsDistinct) (@firstMissingLe) (@firstMissingMem) (@vertexMem)
      (@missingMono) (@hbetaT) (@hbetaFirstBound) (@halphaFirst) (@hbetaPrefix) (@halphaPrefix)
      (@horderedUnused) (@hDnDisjoint) (@hDnqDisjoint)
end GoldbergSeymour

end
