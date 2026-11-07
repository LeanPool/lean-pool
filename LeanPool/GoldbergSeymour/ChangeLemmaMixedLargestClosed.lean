/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.NonparallelPenultimateInterchangeability

public import LeanPool.GoldbergSeymour.HierarchyPathNumberPrefix
public import LeanPool.GoldbergSeymour.StableHierarchyReplacement

public import LeanPool.GoldbergSeymour.TashkinovSeriesTerminalRoute

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyOrderedExitReduction
public import LeanPool.GoldbergSeymour.HierarchyStageInterchangeability
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition
public import LeanPool.GoldbergSeymour.GoodHierarchyTerminalPrefixRepackage
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.SharedFacts.MixedChangeTransport.Preparation2
public import LeanPool.GoldbergSeymour.HierarchyFieldTransport
public import LeanPool.GoldbergSeymour.TreeSequenceFirstMissingPositionInvariant

/-!
# Change Lemma Mixed Largest Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation4549Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
  IsProperEdgeColoring G phi →
  IsOneEdgeUncolored phi e0 →
  LowerRoundInductionHypothesis G k e0 ett.rounds →
  (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
    {generating' : PartialEdgeColoring E k}
    (other : ExtendedTashkinovTree G k e0 input' T' generating'),
    other.rounds = ett.rounds →
     MaximumProperty other →
      ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
       (_ : GoodHierarchy K),
       K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
  (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
    {generating' : PartialEdgeColoring E k}
    {other : ExtendedTashkinovTree G k e0 input' T' generating'}
    {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
    other.rounds = ett.rounds →
     C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C)) →
  (let H : TashkinovHierarchy ett base := C.hierarchy;
   let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
   let ell : ℕ := T.length - A.length;
   let Ty : TreeSequence G e0 :=
    TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
     (by have := A.positive; have := T.positive; omega) (by omega);
   ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty)) →
  (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card) →
  ∀ (alpha beta : Fin k),
  alpha ≠ beta →
  (let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
   let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
   alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A →
    TreeVertexOrder T (T.vertex ia) (T.vertex ib) ∧
     alpha ∉
      ({c : Fin k |
        ∃ (t : Fin T.length),
         A.length ≤ (↑t : ℕ) ∧ (↑t : ℕ) < (↑ib : ℕ) ∧ phi (T.edge t) = some c} :
       Finset (Fin k))) →
  (let H : TashkinovHierarchy ett base := C.hierarchy;
   let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
   let A : TreeSequence G e0 := HierarchyStarredStage H q;
   let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
   let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
   va ∈ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A) →
  ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let R : TreeSequence G e0 := HierarchyStarredStage H r;
  (0 : ℕ) < H.dividerCount →
  (↑r : ℕ) < H.dividerCount →
  TreeColorSetClosed G phi R ({ alpha } : Finset (Fin k)) →
  (∀ (s : Fin (H.dividerCount + (1 : ℕ))),
    (↑r : ℕ) < (↑s : ℕ) →
     ¬TreeColorSetClosed G phi (HierarchyStarredStage H s)
       ({ alpha } : Finset (Fin k))) →
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
  let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
  let _ : V := T.vertex ia;
  let _ : V := T.vertex ib;
  let ell : ℕ := T.length - A.length;
  let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
  let Y : TreeSequence G e0 :=
   TreeSequencePrefix T yLength
    (have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
    (by omega);
  (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
  (∀ {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S U →
     TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
  (∀ {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S W →
     TreeSequenceInitialSegment U W →
      S.length ≤ U.length → TreeSequenceInitialSegment S U) →
  TreeSequenceInitialSegment base.core A →
  TreeSequenceInitialSegment Tn A →
  TreeSequenceInitialSegment A T →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (H.stage j.castSucc) A) →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑j : ℕ) ≠ (0 : ℕ) → HierarchyStarredStage H j = H.stage j.castSucc) →
  ((↑r : ℕ) = (0 : ℕ) → R = base.core) →
  ((↑r : ℕ) ≠ (0 : ℕ) → R = H.stage r.castSucc) →
  TreeSequenceInitialSegment R A →
  TreeSequenceInitialSegment base.core R →
  TreeSequenceInitialSegment Tn R →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑j : ℕ) ≤ (↑r : ℕ) →
     TreeSequenceInitialSegment (H.stage j.castSucc) R) →
  TreeSequenceInitialSegment Y T →
  alpha ∈ TreeMissingColors phi Y ∧
    beta ∈ TreeMissingColors phi Y →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
  (∀ c ∈ TreeMissingColors phi Y,
    c ∈
      MissingColors G phi
       (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
     (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ Y.length) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) :=
   Fin.last H.dividerCount;
  let _ : TreeSequence G e0 := HierarchyStarredStage H q;
  let va : V :=
   T.vertex (HierarchyFirstMissingPosition phi T alpha);
  let vb : V :=
   T.vertex (HierarchyFirstMissingPosition phi T beta);
  let sameComponent : Prop :=
   TwoColorComponent G phi alpha beta (Sum.inl va) =
    TwoColorComponent G phi alpha beta (Sum.inl vb);
  sameComponent

private abbrev helperContinuation4559Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
  IsProperEdgeColoring G phi →
  IsOneEdgeUncolored phi e0 →
  LowerRoundInductionHypothesis G k e0 ett.rounds →
  (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
    {generating' : PartialEdgeColoring E k}
    (other : ExtendedTashkinovTree G k e0 input' T' generating'),
    other.rounds = ett.rounds →
     MaximumProperty other →
      ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
       (x : GoodHierarchy K),
       K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
  (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
    {generating' : PartialEdgeColoring E k}
    {other : ExtendedTashkinovTree G k e0 input' T' generating'}
    {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
    other.rounds = ett.rounds →
     C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C)) →
  (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
   let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
   (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card) →
  ∀ (alpha beta : Fin k),
  alpha ≠ beta →
  ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let R : TreeSequence G e0 := HierarchyStarredStage H r;
  (0 : ℕ) < H.dividerCount →
  (↑r : ℕ) < H.dividerCount →
  TreeColorSetClosed G phi R ({ alpha } : Finset (Fin k)) →
  (∀ (s : Fin (H.dividerCount + (1 : ℕ))),
    (↑r : ℕ) < (↑s : ℕ) →
     ¬TreeColorSetClosed G phi (HierarchyStarredStage H s)
       ({ alpha } : Finset (Fin k))) →
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
  let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
  let va : V := T.vertex ia;
  let vb : V := T.vertex ib;
  let ell : ℕ := T.length - A.length;
  let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
  let Y : TreeSequence G e0 :=
   TreeSequencePrefix T yLength
    (have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive;
    by
    have := GoldbergSeymour.TreeSequence.positive T
    have := GoldbergSeymour.TreeSequence.positive A
    omega)
    (by
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive A
     omega);
  (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
  (∀ {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S U →
     TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
  (∀ {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S W →
     TreeSequenceInitialSegment U W →
      S.length ≤ U.length → TreeSequenceInitialSegment S U) →
  TreeSequenceInitialSegment base.core A →
  TreeSequenceInitialSegment Tn A →
  TreeSequenceInitialSegment A T →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (H.stage j.castSucc) A) →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑j : ℕ) ≠ (0 : ℕ) → HierarchyStarredStage H j = H.stage j.castSucc) →
  ((↑r : ℕ) = (0 : ℕ) → R = base.core) →
  ((↑r : ℕ) ≠ (0 : ℕ) → R = H.stage r.castSucc) →
  TreeSequenceInitialSegment R A →
  TreeSequenceInitialSegment base.core R →
  TreeSequenceInitialSegment Tn R →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑j : ℕ) ≤ (↑r : ℕ) →
     TreeSequenceInitialSegment (H.stage j.castSucc) R) →
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
  alpha ∈
     MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
    (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
  beta ∈
     MissingColors G phi
      (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
    (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
  (∀ (i : Fin (T.length + (1 : ℕ))),
    (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
  va ∈ TreeSequenceVertexSet Y →
  vb ∈ TreeSequenceVertexSet Y →
  va ∈ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A →
  ∀ (hAib : A.length < (↑ib : ℕ)),
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑r : ℕ) ≤ (↑j : ℕ) →
     alpha ∈
      TreeMissingColors phi (HierarchyStarredStage H j)) →
  alpha ∈ TreeMissingColors phi R →
  va ∈ TreeSequenceVertexSet R →
  alpha ∉
    ({c : Fin k |
      ∃ (t : Fin A.length),
       R.length ≤ (↑t : ℕ) ∧ phi (A.edge t) = some c} :
     Finset (Fin k)) →
  beta ∉ TreeMissingColors phi A →
  TreeVertexOrder T
     (T.vertex
      (HierarchyFirstMissingPosition phi T alpha))
     (T.vertex
      (HierarchyFirstMissingPosition phi T beta)) ∧
    alpha ∉
     ({c : Fin k |
       ∃ (t : Fin T.length),
        (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length ≤
          (↑t : ℕ) ∧
         (↑t : ℕ) <
           (↑(HierarchyFirstMissingPosition phi T beta) :
            ℕ) ∧
          phi (T.edge t) = some c} :
      Finset (Fin k)) →
  (↑ia : ℕ) < (↑ib : ℕ) →
  va ≠ vb →
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (↑ib : ℕ)
    (have this : (1 : ℕ) ≤ A.length := A.positive;
    Decidable.byContradiction
     fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
    (by
     have := GoldbergSeymour.TreeSequence.positive T
     omega);
  TreeSequenceInitialSegment B T →
  TreeSequenceInitialSegment A B →
  A.length < B.length →
  TreeSequenceInitialSegment B Y →
  B.length < T.length →
  ∀ (rpB : (1 : ℕ) ≤ ett.1)
   (aboveB :
    TreeSequenceInitialSegment
     (ett.series.data.tree
      (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ))))
     B)
   (strictB :
    (ett.series.data.tree
       (⟨ett.1, by omega⟩ :
        Fin (ett.1 + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (ett.series.data.tree
      (Fin.last (ett.1 + (1 : ℕ)))))
   (genB :
    phi =
     ett.series.data.coloring (Fin.last ett.1)),
  MaximumProperty
    {
     rounds := ett.1, roundsPositive := rpB,
     series := ett.series,
     abovePenultimate := aboveB,
     strictAbovePenultimate := strictB,
     belowFinal := belowB,
     generatingColoring := genB :
     ExtendedTashkinovTree G k e0 input B phi } →
  ∀
   (baseB :
    HierarchyBase
     {
      rounds := ett.1, roundsPositive := rpB,
      series := ett.series,
      abovePenultimate := aboveB,
      strictAbovePenultimate := strictB,
      belowFinal := belowB,
      generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B phi }
     phi),
  baseB.core = base.core →
  ∀
   (HB :
    TashkinovHierarchy
     {
      rounds := ett.1, roundsPositive := rpB,
      series := ett.series,
      abovePenultimate := aboveB,
      strictAbovePenultimate := strictB,
      belowFinal := belowB,
      generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B
       phi }
     baseB)
   (hcountB :
    HB.dividerCount = H.dividerCount),
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
    have jo :
     Fin (H.dividerCount + (1 : ℕ)) :=
     Fin.cast
      (by
       have :=
        GoldbergSeymour.TreeSequence.positive
         T
       have :=
        GoldbergSeymour.TreeSequence.positive
         A
       have :=
        GoldbergSeymour.TreeSequence.positive
         B
       omega)
      j;
    HB.stage j.castSucc =
      H.stage jo.castSucc ∧
     HierarchyStarredStage HB j =
      HierarchyStarredStage H jo) →
  (∀ (i : Fin HB.dividerCount),
    (↑(HB.dividerPosition i) : ℕ) =
     (↑(H.dividerPosition
        (Fin.cast hcountB i)) :
      ℕ)) →
  ∀ (goodB : GoodHierarchy HB),
  (∀
    (j : Fin (HB.dividerCount + (1 : ℕ))),
    have jo :
     Fin (H.dividerCount + (1 : ℕ)) :=
     Fin.cast
      (by
       have :=
        GoldbergSeymour.TreeSequence.positive
         T
       have :=
        GoldbergSeymour.TreeSequence.positive
         A
       have :=
        GoldbergSeymour.TreeSequence.positive
         B
       omega)
      j;
    HierarchyStoredColorsAt HB j =
      HierarchyStoredColorsAt H jo ∧
     HierarchyStageMissingColors HB j =
       HierarchyStageMissingColors H jo ∧
      ∀ (eta : Fin k),
       goodB.gamma j eta =
         C.good.gamma jo eta ∧
        HierarchySegmentColors HB j eta ⊆
         HierarchySegmentColors H jo
          eta) →
  let ettB :
   ExtendedTashkinovTree G k e0 input B
    phi :=
   {
    rounds := ett.rounds,
    roundsPositive := rpB,
    series := ett.series,
    abovePenultimate := aboveB,
    strictAbovePenultimate := strictB,
    belowFinal := belowB,
    generatingColoring := genB :
    ExtendedTashkinovTree G k e0 input B
     phi };
  let H : TashkinovHierarchy ett base :=
   C.hierarchy;
  let q :
   Fin (H.dividerCount + (1 : ℕ)) :=
   Fin.last H.dividerCount;
  let x : TreeSequence G e0 :=
   HierarchyStarredStage H q;
  let va : V :=
   T.vertex
    (HierarchyFirstMissingPosition phi T
     alpha);
  let vb : V :=
   T.vertex
    (HierarchyFirstMissingPosition phi T
     beta);
  let sameComponent : Prop :=
   TwoColorComponent G phi alpha beta
     (Sum.inl va) =
    TwoColorComponent G phi alpha beta
     (Sum.inl vb);
  sameComponent

private abbrev helperContinuation5082Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base),
  (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
    {generating' : PartialEdgeColoring E k}
    {other : ExtendedTashkinovTree G k e0 input' T' generating'}
    {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
    other.rounds = ett.rounds →
     C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C)) →
  ∀ (alpha beta : Fin k),
  alpha ≠ beta →
  ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let R : TreeSequence G e0 := HierarchyStarredStage H r;
  (∀ (s : Fin (H.dividerCount + (1 : ℕ))),
    (↑r : ℕ) < (↑s : ℕ) →
     ¬TreeColorSetClosed G phi (HierarchyStarredStage H s) ({ alpha } : Finset (Fin k))) →
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
  let vb : V := T.vertex ib;
  let ell : ℕ := T.length - A.length;
  let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
  let Y : TreeSequence G e0 :=
   TreeSequencePrefix T yLength
    (have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    Decidable.byContradiction fun (a : ¬yLength ≤ T.length) ↦ by omega);
  (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
  (∀ {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S U →
     TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
  TreeSequenceInitialSegment base.core A →
  TreeSequenceInitialSegment Tn A →
  TreeSequenceInitialSegment A T →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (H.stage j.castSucc) A) →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑j : ℕ) ≠ (0 : ℕ) → HierarchyStarredStage H j = H.stage j.castSucc) →
  TreeSequenceInitialSegment R A →
  TreeSequenceInitialSegment base.core R →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑j : ℕ) ≤ (↑r : ℕ) → TreeSequenceInitialSegment (H.stage j.castSucc) R) →
  beta ∈
     MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
    (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
  ∀ (hAib : A.length < (↑ib : ℕ)),
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑r : ℕ) ≤ (↑j : ℕ) →
     alpha ∈ TreeMissingColors phi (HierarchyStarredStage H j)) →
  beta ∉ TreeMissingColors phi A →
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (↑ib : ℕ)
    (have this : (1 : ℕ) ≤ A.length := A.positive;
    by
    have := GoldbergSeymour.TreeSequence.positive T
    omega)
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬(↑ib : ℕ) ≤ T.length) ↦ by omega);
  TreeSequenceInitialSegment B T →
  A.length < B.length →
  B.length < T.length →
  ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (ett.series.data.tree
      (⟨ett.rounds,
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
       Fin (ett.rounds + (2 : ℕ))))
     B)
   (strictB :
    (ett.series.data.tree
       (⟨ett.rounds,
         by
         have := GoldbergSeymour.TreeSequence.positive T
         omega⟩ :
        Fin (ett.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
   (genB : phi = ett.series.data.coloring (Fin.last ett.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
      belowFinal := belowB, generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B phi }
     phi),
  baseB.core = base.core →
  ∀
   (HB :
    TashkinovHierarchy
     {
      rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
      belowFinal := belowB, generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B phi }
     baseB)
   (hcountB : HB.dividerCount = H.dividerCount),
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
    have jo : Fin (H.dividerCount + (1 : ℕ)) :=
     Fin.cast
      (have this : (1 : ℕ) ≤ T.length := T.positive;
      have this : (1 : ℕ) ≤ A.length := A.positive;
      have this : (1 : ℕ) ≤ B.length := B.positive;
      Decidable.byContradiction
       fun (a : ¬HB.dividerCount + (1 : ℕ) = H.dividerCount + (1 : ℕ)) ↦
       by omega)
      j;
    HB.stage j.castSucc = H.stage jo.castSucc ∧
     HierarchyStarredStage HB j = HierarchyStarredStage H jo) →
  (∀ (i : Fin HB.dividerCount),
    (↑(HB.dividerPosition i) : ℕ) =
     (↑(H.dividerPosition (Fin.cast hcountB i)) : ℕ)) →
  ∀ (goodB : GoodHierarchy HB),
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
    have jo : Fin (H.dividerCount + (1 : ℕ)) :=
     Fin.cast
      (have this : (1 : ℕ) ≤ T.length := T.positive;
      have this : (1 : ℕ) ≤ A.length := A.positive;
      have this : (1 : ℕ) ≤ B.length := B.positive;
      Decidable.byContradiction
       fun
        (a : ¬HB.dividerCount + (1 : ℕ) = H.dividerCount + (1 : ℕ)) ↦
       by omega)
      j;
    HierarchyStoredColorsAt HB j = HierarchyStoredColorsAt H jo ∧
     HierarchyStageMissingColors HB j =
       HierarchyStageMissingColors H jo ∧
      ∀ (eta : Fin k),
       goodB.gamma j eta = C.good.gamma jo eta ∧
        HierarchySegmentColors HB j eta ⊆
         HierarchySegmentColors H jo eta) →
  let ettB : ExtendedTashkinovTree G k e0 input B phi :=
   {
    rounds := ett.rounds, roundsPositive := rpB,
    series := ett.series, abovePenultimate := aboveB,
    strictAbovePenultimate := strictB, belowFinal := belowB,
    generatingColoring := genB :
    ExtendedTashkinovTree G k e0 input B phi };
  let sigma : PartialEdgeColoring E k :=
   TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
  (∀ (f : E) (c : Fin k),
    c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
  (∀ v ∈ TreeSequenceVertexSet B,
    v ≠ vb → MissingColors G sigma v = MissingColors G phi v) →
  ¬ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) →
  (∀ v ∈ TreeSequenceVertexSet A,
    MissingColors G sigma v = MissingColors G phi v) →
  (∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
     TreeMissingColors sigma S = TreeMissingColors phi S) →
  (∀ (f : E), TreeIncidentEdge R f → sigma f = phi f) →
  (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
  ∀
   (corr :
    CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
  MaximumProperty corr.replacementETT →
  ∀ (baseS : HierarchyBase corr.replacementETT sigma)
   (HS : TashkinovHierarchy corr.replacementETT baseS),
  SameHierarchyStages HB HS →
  TashkinovStoredColors corr.replacementETT.series.data
     (Fin.last corr.replacementETT.rounds) =
    Dn →
  False

private abbrev helperParallelBase6126Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (alpha beta : Fin k)
   (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let R : TreeSequence G e0 := HierarchyStarredStage H r;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
  let vb : V := T.vertex ib;
  ∀ (TnToA : TreeSequenceInitialSegment Tn A) (coreToR : TreeSequenceInitialSegment base.core R)
   (hAib : A.length < (↑ib : ℕ)),
  let B : TreeSequence G e0 := TreeSequencePrefix T (↑ib : ℕ) (by omega) (by omega);
  ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (ett.series.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))) B)
   (strictB :
    (ett.series.data.tree (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
   (genB : phi = ett.series.data.coloring (Fin.last ett.rounds))
   (baseB :
    HierarchyBase
     {
      rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
      abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
     phi)
   (hcoreB : baseB.core = base.core),
  let ettB : ExtendedTashkinovTree G k e0 input B phi :=
   {
    rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
    abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
    generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
  let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
  ∀
   (treeMissingEq :
    ∀ (S : TreeSequence G e0),
     TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
      TreeMissingColors sigma S = TreeMissingColors phi S)
   (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
   (baseS : HierarchyBase corr.replacementETT sigma)
   (closureBToA :
    ∀ (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE),
     TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A)
   (minusEq :
    ∀ (S : TreeSequence G e0) (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet R)
     (D : Finset (Fin k)),
     TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D)
   (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
   (hbbase :
    stages (0 : Fin (count + (2 : ℕ))) =
     {
      rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
      (Fin.last
        {
         rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB :
          ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc)
   (hbterminal : stages (Fin.last (count + (1 : ℕ))) = B)
   (hbnested :
    ∀ (j : Fin (count + (1 : ℕ))),
     TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
   (hbstrict :
    ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
   (positions : Fin count → Fin (B.length + (1 : ℕ)))
   (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ))
   (hbincreasing :
    ∀ (i j : Fin count), (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
   (hbdivider :
    ∀ (i : Fin count),
     stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
      TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i)
       (Nat.le_of_lt_succ (positions i).isLt))
   (hbcore :
    TreeSequenceInitialSegment baseB.core (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
   (goodB :
    GoodHierarchy
     {
      dividerCount := count, stage := stages, baseStage := hbbase, terminalStage := hbterminal,
      nested := hbnested, strict := hbstrict, dividerPosition := positions,
      dividerPositive := hbpositive, dividerIncreasing := hbincreasing,
      dividerStage := hbdivider, coreInsideFirst := hbcore :
      TashkinovHierarchy
       {
        rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
       baseB })
   (hcore : baseB.core = baseS.core)
   (hpe :
    { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
         abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }.series.data.kind
       (Fin.last
        {
         rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }.rounds) =
      some TashkinovExtensionKind.PE ↔
     corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
      some TashkinovExtensionKind.PE)
   (hclosure :
    {
     rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
         abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }.series.data.kind
       (Fin.last
        { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }.rounds) =
      some TashkinovExtensionKind.PE →
     baseB.closure = baseS.closure)
   (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
   (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
   (hsincreasing :
    ∀ (i j : Fin count), (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
   (hsbase :
    stages (0 : Fin (count + (2 : ℕ))) =
     corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc)
   (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
   (hsnested :
    ∀ (j : Fin (count + (1 : ℕ))),
     TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
   (hsstrict :
    ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
   (hsdivider :
    ∀ (i : Fin count),
     stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
      TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i)
       (Nat.le_of_lt_succ (positionsS i).isLt))
   (hscore :
    TreeSequenceInitialSegment baseS.core
     (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
  let HB : TashkinovHierarchy ettB baseB :=
   {
    dividerCount := count, stage := stages, baseStage := hbbase, terminalStage := hbterminal,
    nested := hbnested, strict := hbstrict, dividerPosition := positions,
    dividerPositive := hbpositive, dividerIncreasing := hbincreasing, dividerStage := hbdivider,
    coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
  let HS : TashkinovHierarchy corr.replacementETT baseS :=
   {
    dividerCount := count, stage := stages, baseStage := hsbase, terminalStage := hsterminal,
    nested := hsnested, strict := hsstrict, dividerPosition := positionsS,
    dividerPositive := hspositive, dividerIncreasing := hsincreasing, dividerStage := hsdivider,
    coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
  ∀
   (storedEq :
    ∀ (j : Fin (count + (1 : ℕ))), HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j),
  let n : Fin (corr.replacementETT.rounds + (1 : ℕ)) := Fin.last corr.replacementETT.rounds;
  let Tn : TreeSequence G e0 := corr.replacementETT.series.data.tree n.castSucc;
  corr.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE →
  ¬TreeColorSetMinusClosed G sigma baseS.core
     ((HierarchyStoredColorsAt HS (0 : Fin (HS.dividerCount + (1 : ℕ)))).biUnion
      (goodB.gamma (0 : Fin (HS.dividerCount + (1 : ℕ))))) ∧
   (4 : ℕ) ≤
    ((TreeMissingColors sigma Tn ∩ TreeMissingColors sigma baseS.closure : Finset (Fin k)) \
      (HierarchyStoredColorsAt HS (0 : Fin (HS.dividerCount + (1 : ℕ)))).biUnion
       (goodB.gamma (0 : Fin (HS.dividerCount + (1 : ℕ))))).card

private theorem lexicographicMeasureDecreases {a b c d : ℕ}
    (hab : a ≤ b) (hcd : c < d) : HierarchyCounterexampleLess (a, c) (b, d) := by
  rcases lt_or_eq_of_le hab with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hcd⟩

private theorem helper_starPositive_301.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    (↑j : ℕ) ≠ (0 : ℕ) →
    HierarchyStarredStage H j = H.stage j.castSucc := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H j hj
  obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ j
  · exact (hj (congrArg Fin.val hz)).elim
  · rw [hi]
    rfl

private theorem helper_descend_417.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    (∀ (s : Fin (H.dividerCount + (1 : ℕ))),
        (↑r : ℕ) < (↑s : ℕ) →
          ¬TreeColorSetClosed G phi (HierarchyStarredStage H s)
              ({ alpha } : Finset (Fin k))) →
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    alpha ∈ TreeMissingColors phi A →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        ColoredVertexSetElementary G phi
          (TreeSequenceVertexSet (HierarchyStarredStage H j))) →
    ∀ (d : ℕ) (j : Fin (H.dividerCount + (1 : ℕ))),
    H.dividerCount ≤ (↑j : ℕ) + d →
    (↑r : ℕ) ≤ (↑j : ℕ) →
    alpha ∈ TreeMissingColors phi (HierarchyStarredStage H j) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne r H hmaximal q A halphaA
      elementaryStar
  clear * - halphaA q C hmaximal elementaryStar r H
  intro d
  induction d with
  | zero =>
    intro j hj _
    have hjq : j = q := Fin.ext (by simp [q]; omega)
    simpa [hjq, q] using halphaA
  | succ d ih =>
    intro j hj hrj
    by_cases hjq : j = q
    · simpa [hjq, q] using halphaA
    · have hjlt : j.val < H.dividerCount := by
        have hne : j.val ≠ H.dividerCount := by
          intro hh; apply hjq; apply Fin.ext; simpa [q] using hh
        omega
      let i : Fin H.dividerCount := ⟨j.val, hjlt⟩
      have hic : i.castSucc = j := Fin.ext rfl
      have hnext := ih i.succ (by dsimp [i]; omega) (by dsimp [i]; omega)
      by_contra hold
      obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hnext
      have hvo : v ∉ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc) := by
        intro hvo
        exact hold (Finset.mem_biUnion.mpr ⟨v, by simpa [hic] using hvo, hvm⟩)
      have hnew : alpha ∈
          ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
              fun v => MissingColors G phi v) :=
        Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvo⟩, hvm⟩
      have hc := GoodHierarchyNewMissingClosed C.good i (elementaryStar i.succ) alpha hnew
      apply hmaximal i.succ (by dsimp [i]; omega)
      intro c hc'
      have : c = alpha := Finset.mem_singleton.mp hc'
      subst c
      exact hc

private theorem helper_branch_487.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let j : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have this : (0 : ℕ) < ett.rounds := C.positive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    ∀ {u : V},
    u ∈ TreeSequenceVertexSet Tn →
    ∀ {v : V},
    v ∈ TreeSequenceVertexSet Tn →
    u ≠ v →
    (1 : ℕ) < ett.rounds →
    Disjoint (MissingColors G (ett.series.data.coloring j.castSucc) u)
      (MissingColors G (ett.series.data.coloring j.castSucc) v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hlower n Tn j u hu v hv huv hn
  obtain ⟨lower, hr, hmax, _, _⟩ :=
    CertifiedETTRestriction G k e0 input T phi ett C.maximum
      (ett.rounds - 1) (by omega) (by omega)
  have he : ColoredVertexSetElementary G
      (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
      (TreeSequenceVertexSet (ett.series.data.tree ⟨ett.rounds - 1 + 1, by omega⟩)) :=
    (hlower lower (by omega) (by omega) hmax).1
  have ht : (⟨ett.rounds - 1 + 1, by omega⟩ : Fin (ett.rounds + 2)) = n.castSucc :=
    Fin.ext (by simp [n]; omega)
  have hu' : u ∈ TreeSequenceVertexSet (ett.series.data.tree
      ⟨ett.rounds - 1 + 1, by omega⟩) := by simpa only [ht] using hu
  have hv' : v ∈ TreeSequenceVertexSet (ett.series.data.tree
      ⟨ett.rounds - 1 + 1, by omega⟩) := by simpa only [ht] using hv
  exact he hu' hv' huv

private theorem helper_branch_501.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let j : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          have this : (0 : ℕ) < ett.rounds := C.positive;
          Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) < ett.rounds) ↦ by
            omega⟩ :
        Fin ett.rounds);
    ∀ {u : V},
    u ∈ TreeSequenceVertexSet Tn →
    ∀ {v : V},
    v ∈ TreeSequenceVertexSet Tn →
    u ≠ v →
    ¬(1 : ℕ) < ett.rounds →
    Disjoint (MissingColors G (ett.series.data.coloring j.castSucc) u)
      (MissingColors G (ett.series.data.coloring j.castSucc) v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C n Tn j u hu v hv huv hn
  have hn1 : ett.rounds = 1 := by have := C.positive; omega
  have hj0 : j.castSucc = (0 : Fin (ett.rounds + 1)) := Fin.ext (by simp [j, hn1])
  have ht1 : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
    Fin.ext (by simp [n, hn1])
  have he : ColoredVertexSetElementary G (ett.series.data.coloring 0)
      (TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩)) :=
    (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
  have hu' : u ∈ TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩) := by
    simpa only [Tn, ht1] using hu
  have hv' : v ∈ TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩) := by
    simpa only [Tn, ht1] using hv
  simpa only [hj0] using he hu' hv' huv

private theorem helper_BstrictT_538.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k)
      (_ : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment A T →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    A.length < B.length →
    TreeSequenceInitialSegment B Y →
    B.length < T.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H q A ib ell yLength Y AToT hAib B
      ABstrict BToY
  clear * - AToT BToY ABstrict Y
  have hAT := AToT.1
  have hY : Y.length = min (A.length + (T.length - A.length - 1)) T.length := rfl
  have hBY := BToY.1
  have hAB := ABstrict
  omega

private theorem helper_branch_561.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k) (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    TreeColorSetClosed G phi R ({ alpha } : Finset (Fin k)) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    ((↑r : ℕ) = (0 : ℕ) → R = base.core) →
    alpha ∈ TreeMissingColors phi R →
    (↑r : ℕ) = (0 : ℕ) →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    TreeInterchangeable G base.core phi alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta r H R hclosed n
      Tn Dn rZero halphaR hz hp
  have hs : CombinedStableColoring Tn base.closure Dn phi phi :=
    ⟨⟨(by intros; rfl), (by intros; rfl)⟩,
      ⟨(by intros; rfl), (by intros; rfl)⟩⟩
  exact (interchange G k e0 input T phi phi ett C.maximum C.positive
    hlower hp base hproper hone hs alpha beta).2.2.1
    (by simpa [rZero hz] using halphaR)
    (by simpa [rZero hz] using hclosed)

private theorem helper_branch_650.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (other : ExtendedTashkinovTree G k e0 input' T' generating'),
        other.rounds = ett.rounds →
          MaximumProperty other →
            ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
              (_ : GoodHierarchy K),
              K.dividerCount < C.hierarchy.dividerCount →
                ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
    (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card) →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    (↑r : ℕ) < H.dividerCount →
    TreeColorSetClosed G phi R ({ alpha } : Finset (Fin k)) →
    ((↑r : ℕ) ≠ (0 : ℕ) → R = H.stage r.castSucc) →
    alpha ∈ TreeMissingColors phi R →
    ¬(↑r : ℕ) = (0 : ℕ) →
    TreeInterchangeable G R phi alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hlarge alpha beta
      hne r H R hrq hclosed rPositive halphaR hz
  let i : Fin H.dividerCount := ⟨r.val - 1, by omega⟩
  have hi : i.succ.castSucc = r.castSucc := Fin.ext (by simp [i]; omega)
  rw [rPositive hz]
  rw [← hi]
  apply step1 G k e0 input T phi ett C.maximum C.positive hproper hone
    hlower base H C.good hfewer hlarge i alpha beta
  · simpa [hi, ← rPositive hz] using halphaR
  · exact hne
  · simpa [hi, ← rPositive hz] using hclosed

private theorem helper_unaffected_722.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
          PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k),
      alpha ≠ beta →
        ∀ (_ : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
          let H : TashkinovHierarchy ett base := C.hierarchy;
          let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
          let A : TreeSequence G e0 := HierarchyStarredStage H q;
          let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
          let vb : V := T.vertex ib;
          let ell : ℕ := T.length - A.length;
          let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
          let Y : TreeSequence G e0 :=
            TreeSequencePrefix T yLength
              (have hA : (1 : ℕ) ≤ A.length := A.positive;
              have hT : (1 : ℕ) ≤ T.length := T.positive;
              Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
              (by omega);
          alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
              (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
            beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
                (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
              let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
              let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta
                  (Sum.inl vb);
              ∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)
                 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne r H q A ib vb ell yLength Y ha
      hb K sigma f c hca hcb
  clear * - hca hcb K sigma hne
  by_cases hf : Sum.inr f ∈ K
  · by_cases ha : phi f = some alpha
    · simp [sigma, TwoColorComponentSwap, K, hf, ha, hca.symm, hcb.symm]
    · by_cases hb : phi f = some beta
      · simp [sigma, TwoColorComponentSwap, K, hf, hb, hne.symm,
          hca.symm, hcb.symm]
      · simp [sigma, TwoColorComponentSwap, K, hf, ha, hb]
  · simp [sigma, TwoColorComponentSwap, K, hf]

private theorem helper_sigmaOne_739.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsOneEdgeUncolored phi e0 →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (_ : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hone alpha beta hne r H q A ib vb ell yLength Y
      ha hb K sigma unaffected
  clear * - hone sigma K unaffected hne
  refine ⟨?_, ?_⟩
  · simp [sigma, TwoColorComponentSwap, hone.1]
  · intro f hf
    obtain ⟨c, hc⟩ := hone.2 f hf
    by_cases ha : c = alpha
    · subst c
      by_cases hK : Sum.inr f ∈ K
      · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
      · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
    · by_cases hb : c = beta
      · subst c
        by_cases hK : Sum.inr f ∈ K
        · exact ⟨alpha, by simp [sigma, TwoColorComponentSwap, K, hK, hc, hne.symm]⟩
        · exact ⟨beta, by simp [sigma, TwoColorComponentSwap, K, hK, hc]⟩
      · exact ⟨c, (unaffected f c ha hb).mpr hc⟩

private theorem helper_missingBefore_764.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (_ : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let va : V := T.vertex ia;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    va ∈ TreeSequenceVertexSet Y →
    vb ∈ TreeSequenceVertexSet Y →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B Y →
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    Sum.inl va ∉ K →
    (have C : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
      have phi' : PartialEdgeColoring E k :=
        TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
      (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G phi v) ∧
        (∀ (v : V),
            Sum.inl v ∈ C → alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v) ∧
          (∀ (v : V),
              Sum.inl v ∈ C →
                beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi' v) ∧
            ∀ (v : V) (c : Fin k),
              c ≠ alpha →
                c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G phi v)) →
    (∀ {v : V} {f : E},
        Sum.inl v ∈ K →
          Incident G v f → phi f = some alpha ∨ phi f = some beta → Sum.inr f ∈ K) →
    ∀ v ∈ TreeSequenceVertexSet B,
    v ≠ vb →
    MissingColors G sigma v = MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne r H q A ia ib va vb ell yLength
      Y hElementaryY ha hb haY hbY hAib B BToY K sigma haK behavior edgeOfVertex v hv hvb
  clear * - hv hvb K haK haY hbY ha hb hElementaryY BToY behavior edgeOfVertex sigma hne
  by_cases hvK : Sum.inl v ∈ K
  · have hva : v ≠ va := by intro he; exact haK (he ▸ hvK)
    have hvY := TreeSequenceInitialSegmentVertexSetSubset BToY hv
    have han : alpha ∉ MissingColors G phi v := fun hc =>
      Finset.disjoint_left.mp (hElementaryY hvY haY hva) hc ha.1
    have hbn : beta ∉ MissingColors G phi v := fun hc =>
      Finset.disjoint_left.mp (hElementaryY hvY hbY hvb) hc hb.1
    have hpa : ∃ f, Incident G v f ∧ phi f = some alpha := by
      simpa [MissingColors, PresentColors] using han
    have hpb : ∃ f, Incident G v f ∧ phi f = some beta := by
      simpa [MissingColors, PresentColors] using hbn
    obtain ⟨fa, hfa, hfca⟩ := hpa
    obtain ⟨fb, hfb, hfcb⟩ := hpb
    have hfaK := edgeOfVertex hvK hfa (Or.inl hfca)
    have hfbK := edgeOfVertex hvK hfb (Or.inr hfcb)
    have hnewa : sigma fb = some alpha := by
      simp [sigma, TwoColorComponentSwap, K, hfbK, hfcb, hne.symm]
    have hnewb : sigma fa = some beta := by
      simp [sigma, TwoColorComponentSwap, K, hfaK, hfca]
    have hana : alpha ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter, not_not]
      exact ⟨fb, hfb, hnewa⟩
    have hbnb : beta ∉ MissingColors G sigma v := by
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter, not_not]
      exact ⟨fa, hfa, hnewb⟩
    ext c
    by_cases hca : c = alpha
    · subst c; simp [hana, han]
    · by_cases hcb : c = beta
      · subst c; simp [hbnb, hbn]
      · exact behavior.2.2.2 v c hca hcb
  · exact behavior.1 v hvK

private theorem helper_incidentFixed_818.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
        (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet R, Sum.inl v ∉ K) →
    (∀ (f : E), phi f ≠ some alpha → phi f ≠ some beta → sigma f = phi f) →
    ∀ (f : E),
    TreeIncidentEdge R f →
    sigma f = phi f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H R q A ib vb ell yLength Y ha hb
      K sigma avoidR fixedValue f hf
  clear * - hf sigma K avoidR fixedValue
  obtain ⟨v, hv, hvf⟩ := hf
  by_cases hK : Sum.inr f ∈ K
  · by_cases ha : phi f = some alpha
    · exact False.elim (avoidR v hv
        ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) (Sum.inr f)
            from ⟨hvf, Or.inl ha⟩)).trans hK))
    · by_cases hb : phi f = some beta
      · exact False.elim (avoidR v hv
          ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            (show (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) (Sum.inr f)
              from ⟨hvf, Or.inr hb⟩)).trans hK))
      · exact fixedValue f ha hb
  · simp [sigma, TwoColorComponentSwap, K, hK]

private theorem helper_stable_834.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment R A →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    (∀ (f : E), TreeIncidentEdge R f → sigma f = phi f) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet R →
    ∀ (D : Finset (Fin k)),
    StableColoring S D phi sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H R q A ib vb RToA sigma missingA
      incidentFixed S hS D
  refine ⟨?_, fun v hv => missingA v (TreeSequenceInitialSegmentVertexSetSubset RToA (hS hv))⟩
  intro f hf _
  obtain ⟨v, hv, hvf⟩ := hf
  exact incidentFixed f ⟨v, hS hv, hvf⟩

private theorem helper_displayedIncident_896.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    ∀ (S : TreeSequence G e0),
    TreeSequenceInitialSegment S R →
    ∀ (t : Fin S.length),
    TreeIncidentEdge R (S.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C r H R S hSA t
  obtain ⟨i, hi⟩ := S.attaches t
  refine ⟨S.vertex t.succ, TreeSequenceInitialSegmentVertexSetSubset hSA
    (by simp [TreeSequenceVertexSet]), ?_⟩
  simp [Incident, hi]

private theorem helper_augmentationFixed_904.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    TreeSequenceInitialSegment R A →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    (∀ (i : Fin (T.length + (1 : ℕ))),
        (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
    vb ∈ TreeSequenceVertexSet Y →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    alpha ∉
        ({c : Fin k | ∃ (t : Fin A.length), R.length ≤ (↑t : ℕ) ∧ phi (A.edge t) = some c} :
          Finset (Fin k)) →
    TreeVertexOrder T (T.vertex (HierarchyFirstMissingPosition phi T alpha))
          (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        alpha ∉
          ({c : Fin k |
              ∃ (t : Fin T.length),
                (HierarchyStarredStage C.hierarchy
                        (Fin.last C.hierarchy.dividerCount)).length ≤
                    (↑t : ℕ) ∧
                  (↑t : ℕ) < (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ∧
                    phi (T.edge t) = some c} :
            Finset (Fin k)) →
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    TreeSequenceInitialSegment A B →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E), phi f ≠ some alpha → phi f ≠ some beta → sigma f = phi f) →
    (∀ (f : E), TreeIncidentEdge R f → sigma f = phi f) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S R →
          ∀ (t : Fin S.length), TreeIncidentEdge R (S.edge t)) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S B →
    ∀ (t : Fin B.length),
    S.length ≤ (↑t : ℕ) →
    sigma (B.edge t) = phi (B.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H R q A ib vb ell yLength Y
      segRefl segTrans RToA hElementaryY hb vertexY hbY hAib unusedRA horder B BToT AToB sigma
      fixedValue incidentFixed displayedIncident S hseq t ht
  by_cases htA : t.val < R.length
  · have hRB := segTrans RToA AToB
    have he := hRB.2.2 ⟨t.val, htA⟩
    have hi : Fin.castLE hRB.1 ⟨t.val, htA⟩ = t := Fin.ext rfl
    rw [hi] at he
    rw [he]
    exact incidentFixed _ (displayedIncident R (segRefl R) _)
  · have hstep := (TashkinovAugmentationSequencePosition phi S B hseq t ht).1
    obtain ⟨hl, hinit, c, hcol, hm⟩ := hstep
    have hcolB : phi (B.edge t) = some c := by
      convert hcol using 1
      congr 2
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨iv, hiv⟩ := hv
    let ivT : Fin (T.length + 1) := ⟨iv.val, by
      have htB := BToT.1
      have := iv.isLt
      simp only [TreeSequencePrefix] at this
      omega⟩
    have hcvT : c ∈ MissingColors G phi (T.vertex ivT) := by
      have he : (TreeSequencePrefix B t.val (le_trans S.positive ht)
          (Nat.le_of_lt t.isLt)).vertex iv = T.vertex ivT := rfl
      rw [← he, hiv]
      exact hcv
    have hnotA : c ≠ alpha := by
      intro he
      subst c
      by_cases htLast : t.val < A.length
      · apply unusedRA
        let u : Fin A.length := ⟨t.val, htLast⟩
        have he := AToB.2.2 u
        have hi : Fin.castLE AToB.1 u = t := Fin.ext rfl
        rw [hi] at he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u,
          by change R.length ≤ t.val; omega,
          by rw [← he]; exact hcolB⟩
      · apply horder.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.castLE BToT.1 t,
          by change A.length ≤ t.val; omega, t.isLt,
          by rw [BToT.2.2 t]; exact hcolB⟩
    have hnotB : c ≠ beta := by
      intro he
      subst c
      have hivB : ivT.val < ib.val := by
        have := iv.isLt
        simp only [TreeSequencePrefix] at this
        have htB : t.val < ib.val := t.isLt
        dsimp [ivT]
        omega
      have hvY := vertexY ivT (by omega)
      have hneV : T.vertex ivT ≠ vb := by
        intro he
        have hi := congrArg Fin.val (T.vertex_injective he)
        omega
      exact Finset.disjoint_left.mp (hElementaryY hvY hbY hneV) hcvT hb.1
    exact fixedValue _ (fun hc => hnotA (Option.some.inj (hcolB.symm.trans hc)))
      (fun hc => hnotB (Option.some.inj (hcolB.symm.trans hc)))

private theorem helper_seedFixed_967.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn R →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E), TreeIncidentEdge R f → sigma f = phi f) →
    ∀ (f : E) (seed : TreeSequence G e0),
    TreeSequenceAdjoinEdge Tn f seed →
    sigma f = phi f := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H R n Tn ib vb TnToR sigma
      incidentFixed f seed hadjoin
  obtain ⟨i, hi⟩ := seed.attaches (Fin.cast hadjoin.1.symm (Fin.last Tn.length))
  let j : Fin (Tn.length + 1) := ⟨i.val, by have := i.isLt; simpa using this⟩
  have hv : seed.vertex (Fin.castLT i
      (Nat.lt_trans i.isLt (Nat.succ_lt_succ
        (Fin.cast hadjoin.1.symm (Fin.last Tn.length)).isLt))) = Tn.vertex j :=
    hadjoin.2.1.2.1 j
  apply incidentFixed
  refine ⟨Tn.vertex j, TreeSequenceInitialSegmentVertexSetSubset TnToR
    (by simp [TreeSequenceVertexSet]), ?_⟩
  rw [← hadjoin.2.2, Incident, hi]
  simp [← hv]

private theorem helper_edgesFixed_981.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn R →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E), TreeIncidentEdge R f → sigma f = phi f) →
    TreeSequenceInitialSegment Tn B →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence phi seed B) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceInitialSegment S R →
          ∀ (t : Fin S.length), TreeIncidentEdge R (S.edge t)) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B →
          ∀ (t : Fin B.length), S.length ≤ (↑t : ℕ) → sigma (B.edge t) = phi (B.edge t)) →
    (∀ (f : E) (seed : TreeSequence G e0),
        TreeSequenceAdjoinEdge Tn f seed → sigma f = phi f) →
    ∀ (t : Fin B.length),
    sigma (B.edge t) = phi (B.edge t) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H R q A n Tn ib vb TnToR hAib B
      sigma incidentFixed TnToB terminalRoute displayedIncident augmentationFixed seedFixed t
  by_cases ht : t.val < Tn.length
  · have he := TnToB.2.2 ⟨t.val, ht⟩
    have hi : Fin.castLE TnToB.1 ⟨t.val, ht⟩ = t := Fin.ext rfl
    rw [hi] at he
    rw [he]
    exact incidentFixed _ (displayedIncident Tn TnToR _)
  · rcases terminalRoute with ⟨hp, hs⟩ | ⟨hk, f, seed, hedges, hadjoin, hs⟩
    · exact augmentationFixed Tn hs t (by omega)
    · by_cases he : t.val = Tn.length
      · have hSB := TashkinovAugmentationSequenceInitialSegment phi seed B hs
        have hi := hSB.2.2 (Fin.cast hadjoin.1.symm (Fin.last Tn.length))
        have hj : Fin.castLE hSB.1 (Fin.cast hadjoin.1.symm (Fin.last Tn.length)) = t :=
          Fin.ext (by simpa using he.symm)
        rw [hj, hadjoin.2.2] at hi
        simpa [hi] using seedFixed f seed hadjoin
      · exact augmentationFixed seed hs t (by have := hadjoin.1; omega)

private theorem helper_routeTransport_1000.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (_ : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet B,
        v ≠ vb → MissingColors G sigma v = MissingColors G phi v) →
    (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S B →
    TashkinovAugmentationSequence sigma S B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H q A ib vb segTrans hAib B BToT
      sigma missingBefore edgesFixed S hs
  clear * - S hs edgesFixed BToT segTrans missingBefore
  unfold TashkinovAugmentationSequence at hs ⊢
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head U W hstep htail ih =>
    have hWB := TashkinovAugmentationSequenceInitialSegment phi W B htail
    obtain ⟨hlen, hUW, c, hcol, hm⟩ := hstep
    have hUB := segTrans hUW hWB
    have hlt : U.length < B.length := by have := hWB.1; omega
    refine Relation.ReflTransGen.head ⟨hlen, hUW, c, ?_, ?_⟩ ih
    · have hf := edgesFixed (Fin.castLE hWB.1 (Fin.cast hlen.symm (Fin.last U.length)))
      rw [hWB.2.2] at hf
      exact hf.trans hcol
    · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      have hvB := TreeSequenceInitialSegmentVertexSetSubset hUB hv
      have hvb : v ≠ vb := by
        intro he
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
        obtain ⟨i, hi⟩ := hv
        have ht := hUB.2.1 i
        have htT := BToT.2.1 (Fin.castLE (Nat.succ_le_succ hUB.1) i)
        have eqv : T.vertex (Fin.castLE (Nat.succ_le_succ BToT.1)
            (Fin.castLE (Nat.succ_le_succ hUB.1) i)) = T.vertex ib := htT.trans (ht.trans
                (hi.trans he))
        have hh := congrArg Fin.val (T.vertex_injective eqv)
        have := i.isLt
        change i.val = ib.val at hh
        change U.length < ib.val at hlt
        omega
      exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [missingBefore v hvB hvb]; exact hcv⟩

private theorem helper_minusEq_1160.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment R A →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    (∀ (f : E), TreeIncidentEdge R f → sigma f = phi f) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet R →
    ∀ (D : Finset (Fin k)),
    TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H R q A ib vb RToA sigma
      treeMissingEq incidentFixed S hS D
  unfold TreeColorSetMinusClosed TreeColorSetClosed
  rw [treeMissingEq S (fun v hv => TreeSequenceInitialSegmentVertexSetSubset RToA (hS hv))]
  have boundaryEq (c : Fin k) (hc : c ∈ TreeMissingColors phi S) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet S) c =
        BoundaryColorEdges G phi (TreeSequenceVertexSet S) c := by
    ext f
    simp only [BoundaryColorEdges, Finset.mem_filter]
    apply and_congr_right
    intro hf
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨u, hu, v, hv, he⟩ := hf
    have hfix : sigma f = phi f := incidentFixed f ⟨u, hS hu, by simp [Incident, he]⟩
    rw [hfix]
  exact ⟨fun hs c hc => (boundaryEq c (Finset.mem_sdiff.mp hc).1).symm.trans (hs c hc),
    fun hs c hc => (boundaryEq c (Finset.mem_sdiff.mp hc).1).trans (hs c hc)⟩

private theorem helper_hinter_3502.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (other : ExtendedTashkinovTree G k e0 input' T' generating'),
        other.rounds = ett.rounds →
          MaximumProperty other →
            ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
              (_ : GoodHierarchy K),
              K.dividerCount < C.hierarchy.dividerCount →
                ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
    (let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
      let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
      (2 : ℕ) * ett.rounds + (11 : ℕ) ≤ (TreeMissingColors phi Tn).card) →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (r : Fin (C.hierarchy.dividerCount + (1 : ℕ))),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let R : TreeSequence G e0 := HierarchyStarredStage H r;
    (0 : ℕ) < H.dividerCount →
    (↑r : ℕ) < H.dividerCount →
    TreeColorSetClosed G phi R ({ alpha } : Finset (Fin k)) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    ((↑r : ℕ) = (0 : ℕ) → R = base.core) →
    ((↑r : ℕ) ≠ (0 : ℕ) → R = H.stage r.castSucc) →
    alpha ∈ TreeMissingColors phi R →
    TreeInterchangeable G R phi alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hlarge alpha beta
      hne r H R hq hrq hclosed n Tn Dn rZero rPositive halphaR
  by_cases hz : r.val = 0
  · rw [rZero hz]
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact helper_branch_561 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
        (@hone) (@hlower) (@alpha) (@beta) (@r) (@hclosed) (@rZero) (@halphaR) (@hz) (@hp)
    · rw [base.nonparallel hp]
      apply ett.nonparallel_interchangeable C.maximum hproper hone hlower hp alpha beta
      exact Or.inl (by simpa only [rZero hz, base.nonparallel hp] using halphaR)
  · exact helper_branch_650 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
      (@hone) (@hlower) (@hfewer) (@hlarge) (@alpha) (@beta) (@hne) (@r) (@hrq) (@hclosed)
      (@rPositive) (@halphaR) (@hz)

private theorem helper_parallelBase_6126.{u_1, u_2} :
    helperParallelBase6126Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta r H R q A n Tn ib vb TnToA coreToR
      hAib B rpB aboveB strictB belowB genB baseB hcoreB ettB sigma treeMissingEq corr baseS
      closureBToA minusEq count stages hbbase hbterminal hbnested hbstrict positions hbpositive
      hbincreasing hbdivider hbcore goodB hcore hpe hclosure positionsS hspositive hsincreasing
      hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS storedEq
  dsimp only
  intro hp
  have hpOld := hpe.mpr hp
  have hc := hclosure hpOld
  have htree : corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc = Tn := hsbase.symm.trans hbbase
  change ¬TreeColorSetMinusClosed G sigma baseS.core
      ((HierarchyStoredColorsAt HS 0).biUnion (goodB.gamma 0)) ∧
    4 ≤ ((TreeMissingColors sigma (corr.replacementETT.series.data.tree
      (Fin.last corr.replacementETT.rounds).castSucc) ∩
      TreeMissingColors sigma baseS.closure) \
      (HierarchyStoredColorsAt HS 0).biUnion (goodB.gamma 0)).card
  rw [← hcore, ← hc, storedEq, htree,
    treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset TnToA),
    treeMissingEq _ (closureBToA hpOld),
    minusEq _ (by rw [hcoreB]; exact TreeSequenceInitialSegmentVertexSetSubset coreToR)]
  exact goodB.parallelBase hpOld

private theorem helper_continuation_5082.{u_1, u_2} :
    helperContinuation5082Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hminimal alpha beta hne r H R hmaximal q A n Tn
      Dn ib vb ell yLength Y segRefl segTrans coreToA TnToA AToT ordinaryToA starredToA
      starPositive RToA coreToR ordinaryToR hb hAib missingStar hbetaA B BToT ABstrict BstrictT
      rpB aboveB strictB belowB genB baseB hcoreB HB hcountB hstagesB hdividersB goodB hgoodB
      ettB sigma unaffected missingBefore sigmaNotElementary missingA treeMissingEq incidentFixed
      edgesFixed corr hMPS baseS HS hsame storedS
  have hrS : corr.replacementETT.rounds = ett.rounds := corr.rungAgreement
  have stageBToA (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HB.stage j.castSucc) A := by
    clear * - hstagesB ordinaryToA j
    rw [(hstagesB j).1]
    exact ordinaryToA _
  have starBToA (j : Fin (HB.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage HB j) A := by
    clear * - hstagesB starredToA j
    rw [(hstagesB j).2]
    exact starredToA _
  have stageBToB := HB.stageInitialSegment
  have closureBToA (parallel : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE) :
      TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
    have coreBToA : TreeSequenceInitialSegment baseB.core A := by
      rw [hcoreB]
      exact coreToA
    exact (baseB.closure_vertexSet_subset_core parallel).trans coreBToA.vertexSet_subset
  have minusEq :=
    helper_minusEq_1160 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
        (@beta) (@r) (@RToA)
        (@treeMissingEq) (@incidentFixed)
  rcases HB with ⟨count, stages, hbbase, hbterminal, hbnested, hbstrict, positions,
    hbpositive, hbincreasing, hbdivider, hbcore⟩
  rcases HS with ⟨countS, stagesS, hsbase, hsterminal, hsnested, hsstrict, positionsS,
    hspositive, hsincreasing, hsdivider, hscore⟩
  rcases hsame with ⟨hcore, hcount, hstages, hpositions, hpe, hclosure⟩
  dsimp only at hcount hstages hpositions
  cases hcount
  have hstage : stages = stagesS := eq_of_heq hstages
  cases hstage
  let HB : TashkinovHierarchy ettB baseB :=
    ⟨count, stages, hbbase, hbterminal, hbnested, hbstrict, positions,
      hbpositive, hbincreasing, hbdivider, hbcore⟩
  let HS : TashkinovHierarchy corr.replacementETT baseS :=
    ⟨count, stages, hsbase, hsterminal, hsnested, hsstrict, positionsS,
      hspositive, hsincreasing, hsdivider, hscore⟩
  have starEq (j : Fin (count + 1)) :
      HierarchyStarredStage HS j = HierarchyStarredStage HB j := by
    exact Fin.cases hcore.symm (fun i => rfl) j
  have storedEq (j : Fin (count + 1)) :
      HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j := by
    exact HB.storedColors_eq_of_agreement HS j j storedS (starEq j)
      (treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (starBToA j)))
  have missingEq (j : Fin (count + 1)) :
      HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
    exact HB.stageMissingColors_eq_of_agreement HS j j rfl
      (treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBToA j)))
  have firstEq (eta : Fin k) :
      HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta := by
    have lastVertex : B.vertex (Fin.last B.length) = vb := by
      have index : Fin.castLE (Nat.succ_le_succ BToT.1) (Fin.last B.length) = ib :=
        Fin.ext rfl
      exact (BToT.2.1 _).symm.trans (congrArg T.vertex index)
    exact B.firstMissingPosition_eq_of_except_last
      (fun v hv different => missingBefore v hv
        (fun equal => different (equal.trans lastVertex.symm))) eta
  have segmentEq (j : Fin (count + 1)) (eta : Fin k) :
      HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
    apply HB.segmentColors_eq_of_agreement HS j j eta rfl (starEq j)
      (congrArg Fin.val (firstEq eta))
    intro index
    have initial := stageBToB j.succ
    have fixed := edgesFixed (Fin.castLE initial.1 index)
    rw [initial.2.2] at fixed
    exact fixed
  have refreshEq (i : Fin count) :
      ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
          fun v => MissingColors G sigma v) =
      ((TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
          fun v => MissingColors G phi v) := by
    exact HB.segmentMissingColors_eq_of_agreement HS i i rfl (starEq i.castSucc)
      (fun v hv => missingA v (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ)
        (Finset.mem_sdiff.mp hv).1))
  let goodS : GoodHierarchy HS :=
    { gamma := goodB.gamma
      twoColors := by intro j eta he; exact goodB.twoColors j eta (storedEq j ▸ he)
      avoidance := by
        intro j eta he
        rw [missingEq, segmentEq j eta]
        exact goodB.avoidance j eta (storedEq j ▸ he)
      disjointPairs := by
        intro j eta theta he ht hne
        exact goodB.disjointPairs j eta theta (storedEq j ▸ he) (storedEq j ▸ ht) hne
      uniqueRefresh := by
        intro i
        simpa only [storedEq, refreshEq] using goodB.uniqueRefresh i
      parallelBase := by
        exact helper_parallelBase_6126 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
            (@alpha) (@beta) (@r) (@TnToA) (@coreToR) (@hAib) (@rpB) (@aboveB) (@strictB)
            (@belowB) (@genB) (@baseB) (@hcoreB) (@treeMissingEq) (@corr) (@baseS) (@closureBToA)
            (@minusEq) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
            (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@goodB) (@hcore)
            (@hpe) (@hclosure) (@positionsS) (@hspositive) (@hsincreasing) (@hsbase)
            (@hsterminal) (@hsnested) (@hsstrict) (@hsdivider) (@hscore) (@storedEq)
      minusClosed := by
        intro i
        rw [storedEq]
        let jo := Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB) i.succ
        have hstage : HB.stage i.succ.castSucc = H.stage jo.castSucc := (hstagesB i.succ).1
        by_cases hj : jo.val ≤ r.val
        · have hsub : TreeSequenceVertexSet (HB.stage i.succ.castSucc) ⊆
              TreeSequenceVertexSet R := by
            rw [hstage]
            exact TreeSequenceInitialSegmentVertexSetSubset (ordinaryToR jo hj)
          rw [minusEq _ hsub]
          exact goodB.minusClosed i
        · have hjpos : jo.val ≠ 0 := by omega
          have hm : alpha ∈ TreeMissingColors phi (HB.stage i.succ.castSucc) := by
            rw [hstage, ← starPositive jo hjpos]
            exact missingStar jo (by omega)
          have hn : ¬ TreeColorSetClosed G phi (HB.stage i.succ.castSucc) {alpha} := by
            rw [hstage, ← starPositive jo hjpos]
            exact hmaximal jo (by omega)
          have reserved : alpha ∈ (HierarchyStoredColorsAt HB i.succ).biUnion
              (goodB.gamma i.castSucc) := by
            by_contra hh
            apply hn
            intro c hc
            have he : c = alpha := Finset.mem_singleton.mp hc
            subst c
            exact goodB.minusClosed i alpha (Finset.mem_sdiff.mpr ⟨hm, hh⟩)
          unfold TreeColorSetMinusClosed TreeColorSetClosed
          rw [treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ))]
          intro c hc
          have hca : c ≠ alpha := by
            intro he
            subst c
            exact (Finset.mem_sdiff.mp hc).2 reserved
          have hcb : c ≠ beta := by
            intro he
            subst c
            apply hbetaA
            obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hc).1
            exact Finset.mem_biUnion.mpr ⟨v,
              TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ) hv, hcv⟩
          have old := goodB.minusClosed i c hc
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro f hf
          apply Finset.notMem_empty f
          rw [← old]
          obtain ⟨hb, hfc⟩ := Finset.mem_filter.mp hf
          exact Finset.mem_filter.mpr ⟨hb, (unaffected f c hca hcb).mp hfc⟩ }
  let CS : HierarchyCounterexample baseS :=
    { positive := by rw [hrS]; exact C.positive
      hierarchy := HS
      good := goodS
      maximum := hMPS
      notElementary := sigmaNotElementary }
  have hstarLast : HierarchyStarredStage HS (Fin.last count) = A := by
    exact (starEq _).trans
      (H.lastStarredStage_eq_of_agreement HB hcountB (fun j => (hstagesB j).2))
  have hlastOrd : HS.stage (Fin.last count).castSucc = H.stage q.castSucc := by
    have hs := (hstagesB (Fin.last count)).1
    have hj : Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB) (Fin.last count) = q :=
      Fin.ext (by simp [q])
    simpa only [hj] using hs
  -- Path candidates restrict to the shorter prefix; the second measure decreases strictly.
  have pathLe :=
    H.pathNumber_le_of_prefix HS
      (congrArg (fun S : TreeSequence G e0 => S.length) hstarLast) BToT ABstrict
  have tailLess : B.length - (HS.stage (Fin.last count).castSucc).length <
      T.length - (H.stage q.castSucc).length := by
    clear * - hlastOrd ordinaryToA BstrictT ABstrict AToT
    rw [hlastOrd]
    have hlen := (ordinaryToA q).1
    omega
  exact hminimal CS hrS hcountB (lexicographicMeasureDecreases pathLe tailLess)

private theorem helper_continuation_4559.{u_1, u_2} :
    helperContinuation4559Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal hlarge
      alpha beta hne r H R hq hrq hclosed hmaximal q A n Tn Dn ia ib va vb ell yLength Y segRefl
      segTrans commonPrefix coreToA TnToA AToT ordinaryToA starredToA starPositive rZero
      rPositive RToA coreToR TnToR ordinaryToR hElementaryY ha hb vertexY haY hbY hout hAib
      missingStar halphaR haR unusedRA hbetaA horder habIndex havb B BToT AToB ABstrict BToY
      BstrictT rpB aboveB strictB belowB genB hMPB baseB hcoreB HB hcountB hstagesB hdividersB
      goodB hgoodB ettB
  have hinter :=
    helper_hinter_3502 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
        (@hone) (@hlower) (@hfewer) (@hlarge) (@alpha) (@beta) (@hne) (@r) (@hq) (@hrq)
        (@hclosed) (@rZero) (@rPositive) (@halphaR)
  by_contra hcomponents
  let K := TwoColorComponent G phi alpha beta (Sum.inl vb)
  let sigma := TwoColorComponentSwap G phi alpha beta (Sum.inl vb)
  have pathA : TwoColorPathComponent G phi alpha beta (Sum.inl va) :=
    TwoColorPathComponent.of_missing hproper hne ha.1
  have pathB : TwoColorPathComponent G phi alpha beta (Sum.inl vb) :=
    TwoColorPathComponent.swap G phi beta alpha (Sum.inl vb)
      (TwoColorPathComponent.of_missing hproper hne.symm hb.1)
  have avoidR (v : V) (hv : v ∈ TreeSequenceVertexSet R) : Sum.inl v ∉ K := by
    clear * - hcomponents hinter haR pathA pathB K hv
    intro hK
    exact hcomponents (hinter _ _ pathA pathB ⟨va, haR, rfl⟩ ⟨v, hv, hK⟩)
  have haK : Sum.inl va ∉ K := avoidR va haR
  have behavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper
    (Sum.inl vb)
  have edgeOfVertex {v : V} {f : E} (hv : Sum.inl v ∈ K)
      (hf : Incident G v f) (hc : phi f = some alpha ∨ phi f = some beta) :
      Sum.inr f ∈ K := by
    clear * - hv hf hc K
    have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inr f) (Sum.inl v) :=
      ⟨hf, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  have unaffected :=
    helper_unaffected_722 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
        (@beta)
        (@hne) (@r) (@ha) (@hb)
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    clear * - ha hb sigma
    simp [sigma, TwoColorComponentSwap, ha, hb]
  have sigmaProper : IsProperEdgeColoring G sigma :=
    TwoColorComponentSwapProper G phi alpha beta hne hproper _
  have sigmaOne :=
    helper_sigmaOne_739 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hone)
        (@alpha) (@beta) (@hne)
        (@r) (@ha) (@hb) (@unaffected)
  have vertexB (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
      T.vertex i ∈ TreeSequenceVertexSet B := by
    clear * - i hi B
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haB : va ∈ TreeSequenceVertexSet B := vertexB ia (le_of_lt habIndex)
  have hbB : vb ∈ TreeSequenceVertexSet B := vertexB ib le_rfl
  -- Elementarity fixes missing sets before the swapped endpoint, even inside its component.
  have missingBefore (v : V) (hv : v ∈ TreeSequenceVertexSet B) (hvb : v ≠ vb) :=
    helper_missingBefore_764 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@alpha) (@beta) (@hne) (@r) (@hElementaryY) (@ha) (@hb) (@haY) (@hbY) (@hAib) (@BToY)
        (@haK) (@behavior) (@edgeOfVertex) (@v) (@hv) (@hvb)
  have hnewa : alpha ∈ MissingColors G sigma va := by
    rw [behavior.1 va haK]
    exact ha.1
  have hnewb : alpha ∈ MissingColors G sigma vb :=
    behavior.2.2.1 vb (show Sum.inl vb ∈ K from rfl) hb.1
  have sigmaNotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet B) :=
    fun he => Finset.disjoint_left.mp (he haB hbB havb) hnewa hnewb
  have missingA (v : V) (hv : v ∈ TreeSequenceVertexSet A) :
      MissingColors G sigma v = MissingColors G phi v :=
    missingBefore v (TreeSequenceInitialSegmentVertexSetSubset AToB hv)
      (by intro he; exact hout.2 (he ▸ hv))
  have treeMissingEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A) :
      TreeMissingColors sigma S = TreeMissingColors phi S := by
    clear * - hS missingA
    unfold TreeMissingColors
    exact Finset.biUnion_congr rfl (fun v hv => missingA v (hS hv))
  have incidentFixed :=
    helper_incidentFixed_818 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@alpha) (@beta) (@r) (@ha) (@hb) (@avoidR) (@fixedValue)
  have stable :=
    helper_stable_834 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
        (@beta) (@r) (@RToA)
        (@missingA) (@incidentFixed)
  have stableTn : StableColoring Tn Dn phi sigma :=
    stable Tn (TreeSequenceInitialSegmentVertexSetSubset TnToR) Dn
  have TnToB := segTrans TnToA AToB
  have TnStrictB : Tn.length < B.length := lt_of_le_of_lt TnToA.1 ABstrict
  have BToFinal := segTrans BToT ett.belowFinal
  -- Nonparallel extensions retain the certified connecting edge and one-edge seed.
  have terminalRoute := ett.series.terminalRoute C.positive phi ett.generatingColoring B
    TnToB TnStrictB BToFinal
  have displayedIncident :=
    helper_displayedIncident_896 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@r)
  have augmentationFixed :=
    helper_augmentationFixed_904 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@alpha) (@beta) (@r) (@segRefl) (@segTrans) (@RToA) (@hElementaryY) (@hb) (@vertexY)
        (@hbY) (@hAib) (@unusedRA) (@horder) (@BToT) (@AToB) (@fixedValue) (@incidentFixed)
        (@displayedIncident)
  have seedFixed :=
    helper_seedFixed_967 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
        (@beta) (@r) (@TnToR)
        (@incidentFixed)
  have edgesFixed :=
    helper_edgesFixed_981 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
        (@beta) (@r) (@TnToR) (@hAib) (@incidentFixed) (@TnToB) (@terminalRoute)
        (@displayedIncident)
        (@augmentationFixed) (@seedFixed)
  have routeTransport :=
    helper_routeTransport_1000 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@alpha) (@beta) (@r) (@segTrans) (@hAib) (@BToT) (@missingBefore) (@edgesFixed)
  have replacement := HB.stableReplacement hMPB hlower R
    (by rw [hcoreB]; exact coreToR) sigma hproper hone sigmaProper sigmaOne
    stable stableTn terminalRoute routeTransport
  obtain ⟨corr, hMPS, baseS, HS, hsame⟩ := replacement
  have storedS : TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) = Dn := corr.terminalData.2.2
  exact helper_continuation_5082 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
      (@hminimal) (@alpha) (@beta) (@hne) (@r) (@hmaximal) (@segRefl) (@segTrans) (@coreToA)
      (@TnToA) (@AToT) (@ordinaryToA) (@starredToA) (@starPositive) (@RToA) (@coreToR)
      (@ordinaryToR) (@hb) (@hAib) (@missingStar) (@hbetaA) (@BToT) (@ABstrict) (@BstrictT)
      (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@hcoreB) (@HB) (@hcountB)
      (@hstagesB) (@hdividersB) (@goodB) (@hgoodB) (@unaffected) (@missingBefore)
      (@sigmaNotElementary) (@missingA) (@treeMissingEq) (@incidentFixed) (@edgesFixed) (@corr)
      (@hMPS) (@baseS) (@HS) (@hsame) (@storedS)
private theorem helper_continuation_4549.{u_1, u_2} :
    helperContinuation4549Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hminimal
      hprefixElementary hlarge alpha beta hne horderedUnused hlocation r H R hq hrq hclosed
      hmaximal q A n Tn Dn ia ib va vb ell yLength Y segRefl segTrans commonPrefix coreToA TnToA
      AToT ordinaryToA starredToA starPositive rZero rPositive RToA coreToR TnToR ordinaryToR
      YToT hmissingY hElementaryY firstMissing
  have ha := firstMissing alpha hmissingY.1
  have hb := firstMissing beta hmissingY.2
  have vertexY (i : Fin (T.length + 1)) (hi : i.val ≤ Y.length) :
      T.vertex i ∈ TreeSequenceVertexSet Y := by
    clear * - i hi Y
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haY : va ∈ TreeSequenceVertexSet Y := vertexY ia ha.2
  have hbY : vb ∈ TreeSequenceVertexSet Y := vertexY ib hb.2
  have hout : va ∈ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A := hlocation
  have outsideIndex (i : Fin (T.length + 1))
      (hi : T.vertex i ∉ TreeSequenceVertexSet A) : A.length < i.val := by
    exact SharedFacts.MixedChangeTransport.missingPositionOutsidePrefix (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@ett) (@base) (@C)
        (@AToT) (@i) (@hi)
  have hAib := outsideIndex ib hout.2
  have AToY : TreeSequenceInitialSegment A Y :=
    commonPrefix AToT YToT (by omega)
  have missingNotA : ∀ (c : Fin k) (i : Fin (T.length + 1)),
      c ∈ MissingColors G phi (T.vertex i) → T.vertex i ∈ TreeSequenceVertexSet Y →
      T.vertex i ∉ TreeSequenceVertexSet A → c ∉ TreeMissingColors phi A := by
    intro c i missing member outside
    exact hElementaryY.missing_not_mem_biUnion
      (TreeSequenceInitialSegmentVertexSetSubset AToY) member outside missing
  have halphaA : alpha ∈ TreeMissingColors phi A :=
    Finset.mem_biUnion.mpr ⟨va, hout.1, ha.1⟩
  have elementaryStar (j : Fin (H.dividerCount + 1)) :
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet (HierarchyStarredStage H j)) := by
    exact hElementaryY.mono
      (TreeSequenceInitialSegmentVertexSetSubset ((starredToA j).trans AToY))
  -- Missingness descends from an actual final-stage witness.
  have descend : ∀ d (j : Fin (H.dividerCount + 1)),
      H.dividerCount ≤ j.val + d → r.val ≤ j.val →
      alpha ∈ TreeMissingColors phi (HierarchyStarredStage H j) := by
    exact helper_descend_417 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
        (@beta) (@hne) (@r)
        (@hmaximal) (@halphaA) (@elementaryStar)
  have missingStar (j : Fin (H.dividerCount + 1)) (hj : r.val ≤ j.val) :
      alpha ∈ TreeMissingColors phi (HierarchyStarredStage H j) :=
    descend H.dividerCount j (by omega) hj
  have halphaR : alpha ∈ TreeMissingColors phi R := missingStar r le_rfl
  have haR : va ∈ TreeSequenceVertexSet R := by
    exact TreeSequenceFirstMissingVertexMemOfPrefix (segTrans RToA AToT) halphaR
  have preStepElementary :
      let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
      ColoredVertexSetElementary G (ett.series.data.coloring j.castSucc)
        (TreeSequenceVertexSet Tn) := by
    clear * - ett C hlower Tn n
    let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
    change ColoredVertexSetElementary G (ett.series.data.coloring j.castSucc)
      (TreeSequenceVertexSet Tn)
    intro u hu v hv huv
    by_cases hn : 1 < ett.rounds
    · exact @helper_branch_487 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hlower) (@u) (@hu) (@v) (@hv)
        (@huv) (@hn)
    · exact @helper_branch_501 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@u) (@hu) (@v) (@hv) (@huv) (@hn)
  have unusedRA : alpha ∉ (Finset.univ.filter fun c =>
      ∃ t : Fin A.length, R.length ≤ t.val ∧ phi (A.edge t) = some c) :=
    (rutcor G k e0 input T phi ett base H C.good hq hprefixElementary
      preStepElementary alpha halphaA).1 ⟨r, hclosed⟩ r hclosed hmaximal
  have hbetaA : beta ∉ TreeMissingColors phi A := missingNotA beta ib hb.1 hbY hout.2
  have horder := horderedUnused (Or.inr hbetaA)
  have habIndex :=
    SharedFacts.MixedChangeTransport.distinctMissingPositionIndices (@G) (@k) (@e0) (@input)
        (@T) (@phi) (@ett) (@base) (@C) (@alpha)
        (@beta) (@horder)
  have havb : va ≠ vb := by
    clear * - habIndex
    intro he
    have hi := congrArg Fin.val (T.vertex_injective he)
    omega
  -- Keep the exact ordered prefix ending at the beta-missing vertex.
  let B := TreeSequencePrefix T ib.val (by have := A.positive; omega)
    (Nat.le_of_lt_succ ib.isLt)
  have BToT : TreeSequenceInitialSegment B T :=
    ⟨Nat.le_of_lt_succ ib.isLt, (by intro i; rfl), (by intro i; rfl)⟩
  have AToB : TreeSequenceInitialSegment A B := commonPrefix AToT BToT (by exact le_of_lt hAib)
  have ABstrict : A.length < B.length := hAib
  have BToY : TreeSequenceInitialSegment B Y := commonPrefix BToT YToT hb.2
  have BstrictT :=
    helper_BstrictT_538 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
        (@beta) (@r) (@AToT)
        (@hAib) (@ABstrict) (@BToY)
  obtain ⟨ettB, hMPB, hrB, hsB, baseB, hcoreB, hclosureB, hsupportB,
      HB, hcountB, hstagesB, hdividersB, goodB, hgoodB⟩ :=
    GoodHierarchyTerminalPrefixRepackage G k e0 input T phi phi ett C.maximum
      base H C.good B AToB ABstrict BToT
  rcases ettB with ⟨rB, rpB, seriesB, aboveB, strictB, belowB, genB⟩
  cases hrB
  have heqB : seriesB = ett.series := eq_of_heq hsB
  cases heqB
  let ettB : ExtendedTashkinovTree G k e0 input B phi :=
    ⟨ett.rounds, rpB, ett.series, aboveB, strictB, belowB, genB⟩
  exact helper_continuation_4559 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
      (@hproper) (@hone) (@hlower) (@hfewer) (@hminimal) (@hlarge) (@alpha) (@beta) (@hne) (@r)
      (@hq) (@hrq) (@hclosed) (@hmaximal) (@segRefl) (@segTrans) (@commonPrefix) (@coreToA)
      (@TnToA) (@AToT) (@ordinaryToA) (@starredToA) (@starPositive) (@rZero) (@rPositive) (@RToA)
      (@coreToR) (@TnToR) (@ordinaryToR) (@hElementaryY) (@ha) (@hb) (@vertexY) (@haY) (@hbY)
      (@hout) (@hAib) (@missingStar) (@halphaR) (@haR) (@unusedRA) (@hbetaA) (@horder)
      (@habIndex) (@havb) (@BToT) (@AToB) (@ABstrict) (@BToY) (@BstrictT) (@rpB) (@aboveB)
      (@strictB) (@belowB) (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@hcountB) (@hstagesB)
      (@hdividersB) (@goodB) (@hgoodB)
theorem ChangeLemmaMixedLargestClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < C.hierarchy.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hminimal : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      {other : ExtendedTashkinovTree G k e0 input' T' generating'}
      {base' : HierarchyBase other generating'}
      (C' : HierarchyCounterexample base'),
      other.rounds = ett.rounds →
      C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬ HierarchyCounterexampleLess
        (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C))
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (hlarge :
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      2 * ett.rounds + 11 ≤ (TreeMissingColors phi Tn).card)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      alpha ∈ TreeMissingColors phi Ty ∧
        beta ∈ TreeMissingColors phi Ty)
    (horderedUnused :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let ia := HierarchyFirstMissingPosition phi T alpha
      let ib := HierarchyFirstMissingPosition phi T beta
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T (T.vertex ia) (T.vertex ib) ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              A.length ≤ t.val ∧ t.val < ib.val ∧
                phi (T.edge t) = some c))
    (hlocation :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let A := HierarchyStarredStage H q
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
      va ∈ TreeSequenceVertexSet A ∧
        vb ∉ TreeSequenceVertexSet A)
    (r : Fin (C.hierarchy.dividerCount + 1))
    (hbranch :
      let H := C.hierarchy
      0 < H.dividerCount ∧
        r.val < H.dividerCount ∧
        TreeColorSetClosed G phi (HierarchyStarredStage H r) {alpha} ∧
        ∀ s : Fin (H.dividerCount + 1), r.val < s.val →
          ¬ TreeColorSetClosed G phi
            (HierarchyStarredStage H s) {alpha})
 :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let _ := HierarchyStarredStage H q
    let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
    let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
    let sameComponent :=
      TwoColorComponent G phi alpha beta (Sum.inl va) =
        TwoColorComponent G phi alpha beta (Sum.inl vb)
    sameComponent := by
  classical
  let H := C.hierarchy
  let R := HierarchyStarredStage H r
  have hq : 0 < H.dividerCount := hbranch.1
  have hrq : r.val < H.dividerCount := hbranch.2.1
  have hclosed : TreeColorSetClosed G phi R {alpha} := hbranch.2.2.1
  have hmaximal : ∀ s : Fin (H.dividerCount + 1), r.val < s.val →
      ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {alpha} := hbranch.2.2.2
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors ett.series.data n
  let ia := HierarchyFirstMissingPosition phi T alpha
  let ib := HierarchyFirstMissingPosition phi T beta
  let va := T.vertex ia
  let vb := T.vertex ib
  let ell := T.length - A.length
  let yLength := min (A.length + (ell - 1)) T.length
  let Y := TreeSequencePrefix T yLength
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :=
    SharedFacts.MixedChangeTransport.initialSegmentTransitive (@G) (@e0) (@hSU) (@hUW)
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :=
    SharedFacts.MixedChangeTransport.comparableInitialSegments (@G) (@e0) (@hSW) (@hUW) (@hlen)
  have coreToA := H.coreInitialSegmentOfStarredStage (Fin.last H.dividerCount)
  have TnToCore :=
    SharedFacts.MixedChangeTransport.terminalStageInitialSegmentOfCore (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@ett) (@base) (@segRefl)
  have TnToA := segTrans TnToCore coreToA
  have AToT := H.lastStarredInitialSegment
  have ordinaryToA (index : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage index.castSucc) A :=
    H.stageInitialSegmentOfStarredStage index (Fin.last _) (Fin.le_last _)
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    exact Fin.cases coreToA (fun i => ordinaryToA i.succ) j
  have starPositive :=
    helper_starPositive_301 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
  have coreToStar := H.coreInitialSegmentOfStarredStage
  have rZero (hz : r.val = 0) : R = base.core := by
    have hr : r = 0 := Fin.ext hz
    simp [R, hr, HierarchyStarredStage]
  have rPositive (hz : r.val ≠ 0) : R = H.stage r.castSucc :=
    starPositive r hz
  have RToA : TreeSequenceInitialSegment R A := starredToA r
  have coreToR : TreeSequenceInitialSegment base.core R := coreToStar r
  have TnToR := segTrans TnToCore coreToR
  have ordinaryToR (index : Fin (H.dividerCount + 1)) (ordered : index.val ≤ r.val) :
      TreeSequenceInitialSegment (H.stage index.castSucc) R :=
    H.stageInitialSegmentOfStarredStage index r ordered
  have YToT : TreeSequenceInitialSegment Y T :=
    ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
  have hmissingY : alpha ∈ TreeMissingColors phi Y ∧ beta ∈ TreeMissingColors phi Y :=
    hmissingPrefix
  have hElementaryY : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) :=
    hprefixElementary
  have firstMissing (c : Fin k) (missing : c ∈ TreeMissingColors phi Y) :
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
        (HierarchyFirstMissingPosition phi T c).val ≤ Y.length := by
    exact TreeSequenceFirstMissingPositionPrefixWitness YToT missing
  exact helper_continuation_4549 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
      (@hproper) (@hone) (@hlower) (@hfewer) (@hminimal) (@hprefixElementary) (@hlarge) (@alpha)
      (@beta) (@hne) (@horderedUnused) (@hlocation) (@r) (@hq) (@hrq) (@hclosed) (@hmaximal)
      (@segRefl) (@segTrans) (@commonPrefix) (@coreToA) (@TnToA) (@AToT) (@ordinaryToA)
      (@starredToA) (@starPositive) (@rZero) (@rPositive) (@RToA) (@coreToR) (@TnToR)
      (@ordinaryToR) (@YToT) (@hmissingY) (@hElementaryY) (@firstMissing)
end GoldbergSeymour

end
