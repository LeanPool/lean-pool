/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.ChangeLemmaBothOutsidePreparation1

public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.SameHierarchyStages
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequencePosition
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis
public import LeanPool.GoldbergSeymour.SharedFacts.MixedChangeTransport.Preparation2

/-!
# ChangeLemmaBothOutside: supporting constructions, part 1

Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
This module separates dependent data constructors from their supporting proofs.
-/

@[expose] public section

namespace GoldbergSeymour.ChangeLemmaBothOutsidePreparation

/-- Dependent contract shared by the outside change lemma proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperFinish4308Conditions.{u_1, u_2} : Prop :=
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
    {other : ExtendedTashkinovTree G k e0 input' T' generating'}
    {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
    other.rounds = ett.rounds →
     C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C)) →
  ∀ (alpha beta : Fin k),
  alpha ≠ beta →
  (let H : TashkinovHierarchy ett base := C.hierarchy;
   let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
   let ell : ℕ := T.length - A.length;
   let Ty : TreeSequence G e0 :=
    TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
     (have this : (1 : ℕ) ≤ A.length := A.positive;
     have this_1 : (1 : ℕ) ≤ T.length := T.positive;
     Decidable.byContradiction
      fun (a : ¬(1 : ℕ) ≤ min (A.length + (ell - (1 : ℕ))) T.length) ↦
      by
      have := GoldbergSeymour.TreeSequence.positive T
      have := GoldbergSeymour.TreeSequence.positive A
      omega)
     (by
      have := GoldbergSeymour.TreeSequence.positive T
      have := GoldbergSeymour.TreeSequence.positive A
      omega);
   alpha ∈ TreeMissingColors phi Ty ∧ beta ∈ TreeMissingColors phi Ty) →
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
   va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
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
  alpha ∈ TreeMissingColors phi Y ∧ beta ∈ TreeMissingColors phi Y →
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
  va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A →
  A.length < (↑ia : ℕ) →
  ∀ (hAib : A.length < (↑ib : ℕ)),
  alpha ∉ TreeMissingColors phi A →
  beta ∉ TreeMissingColors phi A →
  TreeVertexOrder T
     (T.vertex (HierarchyFirstMissingPosition phi T alpha))
     (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
    alpha ∉
     ({c : Fin k |
       ∃ (t : Fin T.length),
        (HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length ≤
          (↑t : ℕ) ∧
         (↑t : ℕ) <
           (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ∧
          phi (T.edge t) = some c} :
      Finset (Fin k)) →
  (↑ia : ℕ) < (↑ib : ℕ) →
  va ≠ vb →
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (↑ib : ℕ)
    (have this : (1 : ℕ) ≤ A.length := A.positive;
    Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦
     by
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive A
     omega)
    (by
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive A
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
      (⟨ett.1,
        by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        have := GoldbergSeymour.TreeSequence.positive Tn
        have := GoldbergSeymour.TreeSequence.positive Y
        have := GoldbergSeymour.TreeSequence.positive B
        omega⟩ :
       Fin (ett.1 + (2 : ℕ))))
     B)
   (strictB :
    (ett.series.data.tree
       (⟨ett.1,
         by
         have := GoldbergSeymour.TreeSequence.positive T
         have := GoldbergSeymour.TreeSequence.positive A
         have := GoldbergSeymour.TreeSequence.positive Tn
         have := GoldbergSeymour.TreeSequence.positive Y
         have := GoldbergSeymour.TreeSequence.positive B
         omega⟩ :
        Fin (ett.1 + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
   (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
  MaximumProperty
    {
     rounds := ett.1, roundsPositive := rpB,
     series := ett.series, abovePenultimate := aboveB,
     strictAbovePenultimate := strictB, belowFinal := belowB,
     generatingColoring := genB :
     ExtendedTashkinovTree G k e0 input B phi } →
  { rounds := ett.1, roundsPositive := rpB,
      series := ett.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB,
      belowFinal := belowB, generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B phi }.series ≍
    ett.series →
  ∀
   (baseB :
    HierarchyBase
     {
      rounds := ett.1, roundsPositive := rpB,
      series := ett.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB,
      belowFinal := belowB, generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B phi }
     phi),
  baseB.core = base.core →
  baseB.closure = base.closure →
  (↑baseB.supportPosition : ℕ) =
    (↑base.supportPosition : ℕ) →
  ∀
   (HB :
    TashkinovHierarchy
     {
      rounds := ett.1, roundsPositive := rpB,
      series := ett.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB,
      belowFinal := belowB,
      generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B phi }
     baseB)
   (hcountB : HB.dividerCount = H.dividerCount),
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
    have jo : Fin (H.dividerCount + (1 : ℕ)) :=
     Fin.cast
      (by
       have := GoldbergSeymour.TreeSequence.positive T
       have := GoldbergSeymour.TreeSequence.positive A
       have :=
        GoldbergSeymour.TreeSequence.positive Tn
       have := GoldbergSeymour.TreeSequence.positive Y
       have := GoldbergSeymour.TreeSequence.positive B
       omega)
      j;
    HB.stage j.castSucc = H.stage jo.castSucc ∧
     HierarchyStarredStage HB j =
      HierarchyStarredStage H jo) →
  (∀ (i : Fin HB.dividerCount),
    (↑(HB.dividerPosition i) : ℕ) =
     (↑(H.dividerPosition (Fin.cast hcountB i)) :
      ℕ)) →
  ∀ (goodB : GoodHierarchy HB),
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
    have jo : Fin (H.dividerCount + (1 : ℕ)) :=
     Fin.cast
      (by
       have :=
        GoldbergSeymour.TreeSequence.positive T
       have :=
        GoldbergSeymour.TreeSequence.positive A
       have :=
        GoldbergSeymour.TreeSequence.positive Tn
       have :=
        GoldbergSeymour.TreeSequence.positive Y
       have :=
        GoldbergSeymour.TreeSequence.positive B
       omega)
      j;
    HierarchyStoredColorsAt HB j =
      HierarchyStoredColorsAt H jo ∧
     HierarchyStageMissingColors HB j =
       HierarchyStageMissingColors H jo ∧
      ∀ (eta : Fin k),
       goodB.gamma j eta = C.good.gamma jo eta ∧
        HierarchySegmentColors HB j eta ⊆
         HierarchySegmentColors H jo eta) →
  let ettB :
   ExtendedTashkinovTree G k e0 input B phi :=
   {
    rounds := ett.rounds, roundsPositive := rpB,
    series := ett.series,
    abovePenultimate := aboveB,
    strictAbovePenultimate := strictB,
    belowFinal := belowB,
    generatingColoring := genB :
    ExtendedTashkinovTree G k e0 input B phi };
  (∀ {S U : TreeSequence G e0},
    TreeSequenceInitialSegment S U →
     TreeMissingColors phi S ⊆
      TreeMissingColors phi U) →
  ((0 : ℕ) < H.dividerCount ∧
      (alpha ∈
        TreeMissingColors phi
         (H.stage
          (⟨H.dividerCount,
            by
            have :=
             GoldbergSeymour.TreeSequence.positive
              T
            have :=
             GoldbergSeymour.TreeSequence.positive
              A
            have :=
             GoldbergSeymour.TreeSequence.positive
              Tn
            have :=
             GoldbergSeymour.TreeSequence.positive
              Y
            have :=
             GoldbergSeymour.TreeSequence.positive
              B
            omega⟩ :
           Fin (H.dividerCount + (2 : ℕ)))) ∨
       Disjoint
        (insert alpha
          ({ beta } : Finset (Fin k)) :
         Finset (Fin k))
        (HierarchyStoredColorsAt H q)) ∨
     H.dividerCount = (0 : ℕ) ∧
      (alpha ∈ TreeMissingColors phi Tn ∨
       Disjoint
        (insert alpha
          ({ beta } : Finset (Fin k)) :
         Finset (Fin k))
        Dn) →
    alpha ∉ Dn ∧ beta ∉ Dn) →
  alpha ∉ Dn ∧ beta ∉ Dn →
  TwoColorComponent G phi alpha beta
    (Sum.inl va) =
   TwoColorComponent G phi alpha beta
    (Sum.inl vb)

/-- Dependent contract shared by the outside change lemma proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation4272Conditions.{u_1, u_2} : Prop :=
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
    {other : ExtendedTashkinovTree G k e0 input' T' generating'}
    {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
    other.rounds = ett.rounds →
     C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C)) →
  ∀ (alpha beta : Fin k),
  alpha ≠ beta →
  (let H : TashkinovHierarchy ett base := C.hierarchy;
   let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
   let ell : ℕ := T.length - A.length;
   let Ty : TreeSequence G e0 :=
    TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
     (by
      have := A.positive
      have := T.positive
      omega)
     (by omega);
   alpha ∈ TreeMissingColors phi Ty ∧ beta ∈ TreeMissingColors phi Ty) →
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
   va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  let _ : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
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
  (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
  (∀ {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S U →
     TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
  (∀ {S U W : TreeSequence G e0},
    TreeSequenceInitialSegment S W →
     TreeSequenceInitialSegment U W →
      S.length ≤ U.length → TreeSequenceInitialSegment S U) →
  (H.dividerCount ≠ (0 : ℕ) →
    A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
  TreeSequenceInitialSegment base.core A →
  TreeSequenceInitialSegment Tn A →
  TreeSequenceInitialSegment A T →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (H.stage j.castSucc) A) →
  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (HierarchyStarredStage H j) A) →
  TreeSequenceInitialSegment Y T →
  alpha ∈ TreeMissingColors phi Y ∧ beta ∈ TreeMissingColors phi Y →
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
  va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A →
  A.length < (↑ia : ℕ) →
  A.length < (↑ib : ℕ) →
  (∀ (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
    c ∈ MissingColors G phi (T.vertex i) →
     T.vertex i ∈ TreeSequenceVertexSet Y →
      T.vertex i ∉ TreeSequenceVertexSet A →
       c ∉ TreeMissingColors phi A) →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let _ : TreeSequence G e0 := HierarchyStarredStage H q;
  let Tnq : TreeSequence G e0 :=
   H.stage
    (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)));
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  let Dnq : Finset (Fin k) := HierarchyStoredColorsAt H q;
  let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
  let vb : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
  let sameComponent : Prop :=
   TwoColorComponent G phi alpha beta (Sum.inl va) =
    TwoColorComponent G phi alpha beta (Sum.inl vb);
  ((0 : ℕ) < H.dividerCount ∧
     (alpha ∈ TreeMissingColors phi Tnq ∨
      Disjoint
       (insert alpha ({ beta } : Finset (Fin k)) : Finset (Fin k))
       Dnq) →
    sameComponent) ∧
   (H.dividerCount = (0 : ℕ) ∧
     (alpha ∈ TreeMissingColors phi Tn ∨
      Disjoint
       (insert alpha ({ beta } : Finset (Fin k)) : Finset (Fin k))
       Dn) →
    sameComponent)

/-- Dependent contract shared by the outside change lemma proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperHstarLast5289Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
   (C : HierarchyCounterexample base) (alpha beta : Fin k),
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
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
    by
    have := GoldbergSeymour.TreeSequence.positive T
    have := GoldbergSeymour.TreeSequence.positive A
    omega)
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    by
    have := GoldbergSeymour.TreeSequence.positive T
    have := GoldbergSeymour.TreeSequence.positive A
    omega);
  ∀ (hAib : A.length < (↑ib : ℕ)),
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (↑ib : ℕ)
    (have this : (1 : ℕ) ≤ A.length := A.positive;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive;
    Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    by
    have := GoldbergSeymour.TreeSequence.positive T
    omega);
  ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (ett.series.data.tree
      (⟨ett.rounds,
        have this : (1 : ℕ) ≤ T.length := T.positive;
        have this : (1 : ℕ) ≤ A.length := A.positive;
        have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
        have this : (1 : ℕ) ≤ Y.length := Y.positive;
        have this : (1 : ℕ) ≤ B.length := B.positive;
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
       Fin (ett.rounds + (2 : ℕ))))
     B)
   (strictB :
    (ett.series.data.tree
       (⟨ett.rounds,
         have this : (1 : ℕ) ≤ T.length := T.positive;
         have this : (1 : ℕ) ≤ A.length := A.positive;
         have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
         have this : (1 : ℕ) ≤ Y.length := Y.positive;
         have this : (1 : ℕ) ≤ B.length := B.positive;
         by
         have := GoldbergSeymour.TreeSequence.positive T
         omega⟩ :
        Fin (ett.rounds + (2 : ℕ)))).length <
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
     phi),
  let ettB : ExtendedTashkinovTree G k e0 input B phi :=
   {
    rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
    abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
    generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
  let sigma : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
  ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
   (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
   (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
   (hbbase :
    stages (0 : Fin (count + (2 : ℕ))) =
     { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
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
       (by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        have := GoldbergSeymour.TreeSequence.positive B
        omega))
   (hbcore :
    TreeSequenceInitialSegment baseB.core (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
   (hcountB :
    { dividerCount := count, stage := stages, baseStage := hbbase, terminalStage := hbterminal,
       nested := hbnested, strict := hbstrict, dividerPosition := positions,
       dividerPositive := hbpositive, dividerIncreasing := hbincreasing,
       dividerStage := hbdivider, coreInsideFirst := hbcore :
       TashkinovHierarchy
        {
         rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
         abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
         generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
        baseB }.dividerCount =
     H.dividerCount),
  (∀
    (j :
     Fin
      ({ dividerCount := count, stage := stages, baseStage := hbbase,
         terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
         dividerPosition := positions, dividerPositive := hbpositive,
         dividerIncreasing := hbincreasing, dividerStage := hbdivider,
         coreInsideFirst := hbcore :
         TashkinovHierarchy
          {
           rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
           abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
           generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
          baseB }.dividerCount +
       (1 : ℕ))),
    have jo : Fin (H.dividerCount + (1 : ℕ)) :=
     Fin.cast
      (have this : (1 : ℕ) ≤ T.length := T.positive;
      have this : (1 : ℕ) ≤ A.length := A.positive;
      have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
      have this : (1 : ℕ) ≤ Y.length := Y.positive;
      have this : (1 : ℕ) ≤ B.length := B.positive;
      by
      have := GoldbergSeymour.TreeSequence.positive T
      have := GoldbergSeymour.TreeSequence.positive A
      have := GoldbergSeymour.TreeSequence.positive B
      omega)
      j;
    { dividerCount := count, stage := stages, baseStage := hbbase, terminalStage := hbterminal,
         nested := hbnested, strict := hbstrict, dividerPosition := positions,
         dividerPositive := hbpositive, dividerIncreasing := hbincreasing,
         dividerStage := hbdivider, coreInsideFirst := hbcore :
         TashkinovHierarchy
          {
           rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
           abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
           generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
          baseB }.stage
       j.castSucc =
      H.stage jo.castSucc ∧
     HierarchyStarredStage
       {
        dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore :
        TashkinovHierarchy
         {
          rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
          generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi }
         baseB }
       j =
      HierarchyStarredStage H jo) →
  ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
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
       (by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        have := GoldbergSeymour.TreeSequence.positive B
        omega))
   (hscore :
    TreeSequenceInitialSegment baseS.core
     (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
  let HB : TashkinovHierarchy ettB baseB :=
   {
    dividerCount := count, stage := stages, baseStage := hbbase, terminalStage := hbterminal,
    nested := hbnested, strict := hbstrict, dividerPosition := positions,
    dividerPositive := hbpositive, dividerIncreasing := hbincreasing,
    dividerStage := hbdivider, coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
  let HS : TashkinovHierarchy corr.replacementETT baseS :=
   {
    dividerCount := count, stage := stages, baseStage := hsbase, terminalStage := hsterminal,
    nested := hsnested, strict := hsstrict, dividerPosition := positionsS,
    dividerPositive := hspositive, dividerIncreasing := hsincreasing,
    dividerStage := hsdivider, coreInsideFirst := hscore :
    TashkinovHierarchy corr.replacementETT baseS };
  (∀ (j : Fin (count + (1 : ℕ))), HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
  HierarchyStarredStage HS (Fin.last count) = A

/-- Dependent contract shared by the outside change lemma proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation4653Conditions.{u_1, u_2} : Prop :=
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
    {other : ExtendedTashkinovTree G k e0 input' T' generating'}
    {base' : HierarchyBase other generating'} (C' : HierarchyCounterexample base'),
    other.rounds = ett.rounds →
     C'.hierarchy.dividerCount = C.hierarchy.dividerCount →
      ¬HierarchyCounterexampleLess (HierarchyCounterexampleMeasure C')
        (HierarchyCounterexampleMeasure C)) →
  ∀ (alpha beta : Fin k),
  alpha ≠ beta →
  let H : TashkinovHierarchy ett base := C.hierarchy;
  let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
  let A : TreeSequence G e0 := HierarchyStarredStage H q;
  let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
  let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
  let ia : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T alpha;
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
  ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
  beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
    (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
  (∀ (i : Fin (T.length + (1 : ℕ))),
    (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
  vb ∈ TreeSequenceVertexSet Y →
  A.length < (↑ia : ℕ) →
  ∀ (hAib : A.length < (↑ib : ℕ)),
  alpha ∉ TreeMissingColors phi A →
  beta ∉ TreeMissingColors phi A →
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
  (↑ia : ℕ) < (↑ib : ℕ) →
  let B : TreeSequence G e0 :=
   TreeSequencePrefix T (↑ib : ℕ)
    (have this : (1 : ℕ) ≤ A.length := A.positive;
    by
    have := GoldbergSeymour.TreeSequence.positive T
    omega)
    (have this : (1 : ℕ) ≤ T.length := T.positive;
    have this : (1 : ℕ) ≤ A.length := A.positive;
    Decidable.byContradiction fun (a : ¬(↑ib : ℕ) ≤ T.length) ↦ by omega);
  TreeSequenceInitialSegment B T →
  A.length < B.length →
  B.length < T.length →
  ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
   (aboveB :
    TreeSequenceInitialSegment
     (ett.series.data.tree
      (⟨ett.rounds,
        have this : (1 : ℕ) ≤ T.length := T.positive;
        have this : (1 : ℕ) ≤ A.length := A.positive;
        have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
        have this : (1 : ℕ) ≤ Y.length := Y.positive;
        have this : (1 : ℕ) ≤ B.length := B.positive;
        Decidable.byContradiction
         fun (a : ¬ett.rounds < ett.rounds + (2 : ℕ)) ↦ by omega⟩ :
       Fin (ett.rounds + (2 : ℕ))))
     B)
   (strictB :
    (ett.series.data.tree
       (⟨ett.rounds,
         have this : (1 : ℕ) ≤ T.length := T.positive;
         have this : (1 : ℕ) ≤ A.length := A.positive;
         have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
         have this : (1 : ℕ) ≤ Y.length := Y.positive;
         have this : (1 : ℕ) ≤ B.length := B.positive;
         Decidable.byContradiction
          fun (a : ¬ett.rounds < ett.rounds + (2 : ℕ)) ↦ by omega⟩ :
        Fin (ett.rounds + (2 : ℕ)))).length <
     B.length)
   (belowB :
    TreeSequenceInitialSegment B
     (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
   (genB : phi = ett.series.data.coloring (Fin.last ett.rounds)),
  MaximumProperty
    {
     rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
     abovePenultimate := aboveB, strictAbovePenultimate := strictB,
     belowFinal := belowB, generatingColoring := genB :
     ExtendedTashkinovTree G k e0 input B phi } →
  ∀
   (baseB :
    HierarchyBase
     {
      rounds := ett.rounds, roundsPositive := rpB,
      series := ett.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B phi }
     phi),
  baseB.core = base.core →
  ∀
   (HB :
    TashkinovHierarchy
     {
      rounds := ett.rounds, roundsPositive := rpB,
      series := ett.series, abovePenultimate := aboveB,
      strictAbovePenultimate := strictB, belowFinal := belowB,
      generatingColoring := genB :
      ExtendedTashkinovTree G k e0 input B phi }
     baseB)
   (hcountB : HB.dividerCount = H.dividerCount),
  (∀ (j : Fin (HB.dividerCount + (1 : ℕ))),
    have jo : Fin (H.dividerCount + (1 : ℕ)) :=
     Fin.cast
      (have this : (1 : ℕ) ≤ T.length := T.positive;
      have this : (1 : ℕ) ≤ A.length := A.positive;
      have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
      have this : (1 : ℕ) ≤ Y.length := Y.positive;
      have this : (1 : ℕ) ≤ B.length := B.positive;
      Decidable.byContradiction
       fun
        (a :
         ¬HB.dividerCount + (1 : ℕ) = H.dividerCount + (1 : ℕ)) ↦
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
      have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
      have this : (1 : ℕ) ≤ Y.length := Y.positive;
      have this : (1 : ℕ) ≤ B.length := B.positive;
      Decidable.byContradiction
       fun
        (a :
         ¬HB.dividerCount + (1 : ℕ) = H.dividerCount + (1 : ℕ)) ↦
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
  ((0 : ℕ) < H.dividerCount ∧
      (alpha ∈
        TreeMissingColors phi
         (H.stage
          (⟨H.dividerCount,
            have this : (1 : ℕ) ≤ T.length := T.positive;
            have this : (1 : ℕ) ≤ A.length := A.positive;
            have this : (1 : ℕ) ≤ Tn.length := Tn.positive;
            have this : (1 : ℕ) ≤ Y.length := Y.positive;
            have this : (1 : ℕ) ≤ B.length := B.positive;
            Decidable.byContradiction
             fun
              (a : ¬H.dividerCount < H.dividerCount + (2 : ℕ)) ↦
             by omega⟩ :
           Fin (H.dividerCount + (2 : ℕ)))) ∨
       Disjoint
        (insert alpha ({ beta } : Finset (Fin k)) :
         Finset (Fin k))
        (HierarchyStoredColorsAt H q)) ∨
     H.dividerCount = (0 : ℕ) ∧
      (alpha ∈ TreeMissingColors phi Tn ∨
       Disjoint
        (insert alpha ({ beta } : Finset (Fin k)) :
         Finset (Fin k))
        Dn) →
    alpha ∉ Dn ∧ beta ∉ Dn) →
  alpha ∉ Dn ∧ beta ∉ Dn →
  let sigma : PartialEdgeColoring E k :=
   TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
  (have C : Set (V ⊕ E) :=
    TwoColorComponent G phi alpha beta (Sum.inl vb);
   have phi' : PartialEdgeColoring E k :=
    TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
   (∀ (v : V),
     Sum.inl v ∉ C →
      MissingColors G phi' v = MissingColors G phi v) ∧
    (∀ (v : V),
      Sum.inl v ∈ C →
       alpha ∈ MissingColors G phi v →
        beta ∈ MissingColors G phi' v) ∧
     (∀ (v : V),
       Sum.inl v ∈ C →
        beta ∈ MissingColors G phi v →
         alpha ∈ MissingColors G phi' v) ∧
      ∀ (v : V) (c : Fin k),
       c ≠ alpha →
        c ≠ beta →
         (c ∈ MissingColors G phi' v ↔
          c ∈ MissingColors G phi v)) →
  (∀ (f : E) (c : Fin k),
    c ≠ alpha →
     c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
  (∀ (f : E),
    phi f ≠ some alpha →
     phi f ≠ some beta → sigma f = phi f) →
  IsProperEdgeColoring G sigma →
  IsOneEdgeUncolored sigma e0 →
  (∀ v ∈ TreeSequenceVertexSet B,
    v ≠ vb →
     MissingColors G sigma v = MissingColors G phi v) →
  ¬ColoredVertexSetElementary G sigma
     (TreeSequenceVertexSet B) →
  (∀ v ∈ TreeSequenceVertexSet A,
    MissingColors G sigma v = MissingColors G phi v) →
  (∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆
      TreeSequenceVertexSet A →
     TreeMissingColors sigma S =
      TreeMissingColors phi S) →
  (∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆
      TreeSequenceVertexSet A →
     ∀ (D : Finset (Fin k)),
      alpha ∉ D ∧ beta ∉ D →
       StableColoring S D phi sigma) →
  StableColoring Tn Dn phi sigma →
  TreeSequenceInitialSegment Tn B →
  Tn.length < B.length →
  (∀ (c : Fin k),
    c = alpha ∨ c = beta →
     c ∉ TreeMissingColors phi Tn ∪ Dn) →
  (ett.series.data.kind n =
      some TashkinovExtensionKind.PE ∧
     TashkinovAugmentationSequence phi Tn B ∨
    (ett.series.data.kind n =
       some TashkinovExtensionKind.SE ∨
      ett.series.data.kind n =
       some TashkinovExtensionKind.RE) ∧
     ∃ (f : E) (seed : TreeSequence G e0),
      ett.series.data.connectingEdges n =
        ({ f } : Finset E) ∧
       TreeSequenceAdjoinEdge Tn f seed ∧
        TashkinovAugmentationSequence phi seed
          B ∧
         phi f ≠ some alpha ∧
          phi f ≠ some beta) →
  False

theorem helper_missingBefore_438.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k)
      (_ : alpha ≠ beta),
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
    ∀ (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y))
      (_ :
        alpha ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T alpha)) ∧
          (↑(HierarchyFirstMissingPosition phi T alpha) : ℕ) ≤ Y.length)
      (_ :
        beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
          (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length)
      (_ : va ∈ TreeSequenceVertexSet Y) (_ : vb ∈ TreeSequenceVertexSet Y)
      (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (_ : TreeSequenceInitialSegment B Y),
    let K : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (_ : Sum.inl va ∉ K)
      (_ :
        (have C : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl vb);
        have phi' : PartialEdgeColoring E k :=
          TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
        (∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G phi v) ∧
          (∀ (v : V),
              Sum.inl v ∈ C →
                alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v) ∧
            (∀ (v : V),
                Sum.inl v ∈ C →
                  beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi' v) ∧
              ∀ (v : V) (c : Fin k),
                c ≠ alpha →
                  c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G phi v)))
      (_ :
        (∀ {v : V} {f : E} (_ : Sum.inl v ∈ K) (_ : Incident G v f)
          (_ : phi f = some alpha ∨ phi f = some beta), Sum.inr f ∈ K)),
    ∀ v ∈ TreeSequenceVertexSet B,
    v ≠ vb →
    MissingColors G sigma v = MissingColors G phi v := by
  exact @GoldbergSeymour.SharedFacts.MixedChangeTransport.notMissingBeforeFirstPosition

theorem helper_terminalRoute_532.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀
      (_ :
        (∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S W)
          (_ : TreeSequenceInitialSegment U W) (_ : S.length ≤ U.length),
          TreeSequenceInitialSegment S U))
      (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB)
      (_ : TreeSequenceInitialSegment Tn B) (_ : Tn.length < B.length)
      (_ :
        TreeSequenceInitialSegment B
          (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
      (_ : (∀ (c : Fin k) (_ : c = alpha ∨ c = beta), c ∉ TreeMissingColors phi Tn ∪ Dn))
      (_ : (∀ c ∈ ett.series.data.stored n, c ∈ TreeMissingColors phi Tn ∪ Dn)),
    ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn B ∨
      (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
            TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence phi seed B ∧
                phi f ≠ some alpha ∧ phi f ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn Dn ib commonPrefix hAib B
      rpB aboveB strictB belowB genB baseB HB TnToB TnStrictB BToFinal notControlled storedOrMissing
  have step := ett.series.certified n
  generalize hi : n = i at step
  cases step with
  | initial => have hv := congrArg Fin.val hi; simp [n] at hv; have := C.positive; omega
  | SE j _ _ _ _ _ choice _ coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
    have hseedB : TreeSequenceInitialSegment seed B :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
        BToFinal (by
            have hl := adjoin.1
            rw [hj] at hl
            change seed.length = Tn.length + 1 at hl
            omega)
    have hcol : phi choice.edge = some choice.color := by
      have hg : phi = choice.selected := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simpa only [hg] using choice.edgeColor
    have hc : choice.color ∈ ett.series.data.stored n := by rw [← hj, stored]; simp
    have hnot (c : Fin k) (he : c = alpha ∨ c = beta) : phi choice.edge ≠ some c := by
      intro hc'
      have heq := Option.some.inj (hcol.symm.trans hc')
      exact notControlled c he (heq ▸ storedOrMissing choice.color hc)
    exact Or.inr ⟨Or.inl (by simpa [hj] using kind), choice.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      TashkinovAugmentationSequenceRestrict phi seed B _ hroute hseedB BToFinal,
      hnot alpha (Or.inl rfl), hnot beta (Or.inr rfl)⟩
  | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
      edges kind vertex outside delta gammaEq closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    refine Or.inl ⟨by simpa [hj] using kind, ?_⟩
    apply TashkinovAugmentationSequenceRestrict phi Tn B _ _ TnToB BToFinal
    simpa [Tn, hj, hlast, ← ett.generatingColoring, n] using closure.1
  | RE j _ _ _ _ available coloring stored edges kind vertex outside delta gamma
      seed adjoin closure ordered strict =>
    have hj : j.succ = n := hi.symm
    have hlast : j.succ.succ = Fin.last (ett.rounds + 1) :=
      Fin.ext (by have hv := congrArg Fin.val hj; simp [n] at hv ⊢; omega)
    have hroute : TashkinovAugmentationSequence phi seed
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
      simpa [hj, hlast, ← ett.generatingColoring, n] using closure.1
    have hseedB : TreeSequenceInitialSegment seed B :=
      commonPrefix (TashkinovAugmentationSequenceInitialSegment phi _ _ hroute)
        BToFinal (by
            have hl := adjoin.1
            rw [hj] at hl
            change seed.length = Tn.length + 1 at hl
            omega)
    have hcol : phi available.edge = some available.gamma ∨
        phi available.edge = some available.delta := by
      have hg : phi = ett.series.data.coloring j.castSucc := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simp only [hg]
      have hadj := available.returnPath.adj_snd
        (SimpleGraph.Walk.not_nil_of_ne (by intro he; cases he))
      cases hh : available.returnPath.snd with
      | inl v =>
        have hc : (TwoColorIncidenceGraph G (ett.series.data.coloring j.castSucc)
            available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inl v) :=
          hh ▸ hadj
        exact hc.2
      | inr f =>
        have hc : (TwoColorIncidenceGraph G (ett.series.data.coloring j.castSucc)
            available.gamma available.delta).Adj (Sum.inr available.edge) (Sum.inr f) :=
          hh ▸ hadj
        exact False.elim hc
    have hcontrol : ∃ c, phi available.edge = some c ∧
        c ∈ TreeMissingColors phi Tn ∪ Dn := by
      rcases hcol with h | h
      · exact ⟨available.gamma, h, storedOrMissing _ (by rw [← hj, stored]; simp)⟩
      · exact ⟨available.delta, h, storedOrMissing _ (by rw [← hj, stored]; simp)⟩
    have hnot (c : Fin k) (he : c = alpha ∨ c = beta) : phi available.edge ≠ some c := by
      intro hc'
      obtain ⟨d, hd, hdmem⟩ := hcontrol
      have heq := Option.some.inj (hd.symm.trans hc')
      exact notControlled c he (heq ▸ hdmem)
    exact Or.inr ⟨Or.inr (by simpa [hj] using kind), available.edge, seed,
      by simpa [hj] using edges, by simpa [Tn, hj] using adjoin,
      TashkinovAugmentationSequenceRestrict phi seed B _ hroute hseedB BToFinal,
      hnot alpha (Or.inl rfl), hnot beta (Or.inr rfl)⟩

theorem helper_augmentationControlled_640.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
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
    ∀ (_ : TreeSequenceInitialSegment A T)
      (_ : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y))
      (_ :
        beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
          (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length)
      (_ :
        (∀ (i : Fin (T.length + (1 : ℕ))) (_ : (↑i : ℕ) ≤ Y.length),
          T.vertex i ∈ TreeSequenceVertexSet Y))
      (_ : vb ∈ TreeSequenceVertexSet Y) (hAib : A.length < (↑ib : ℕ))
      (_ : alpha ∉ TreeMissingColors phi A)
      (_ :
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
              Finset (Fin k))),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : B.length < T.length) (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB)
      (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence phi S B) (t : Fin B.length)
      (_ : S.length ≤ (↑t : ℕ)),
    phi (B.edge t) ≠ some alpha ∧
    phi (B.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb ell yLength Y AToT
      hElementaryY hb vertexY hbY hAib halphaA horder B BToT BstrictT rpB aboveB strictB belowB
      genB baseB HB S hseq t ht
  have hstep := (TashkinovAugmentationSequencePosition phi S B hseq t ht).1
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
    have he : (TreeSequencePrefix B t.val (le_trans S.positive ht) (Nat.le_of_lt
        t.isLt)).vertex iv =
        T.vertex ivT := rfl
    rw [← he, hiv]
    exact hcv
  have hnotA : c ≠ alpha := by
    intro he; subst c
    by_cases htA : t.val ≤ A.length
    · apply halphaA
      have hivA : ivT.val ≤ A.length := by
        change iv.val ≤ A.length
        have hiv : iv.val ≤ t.val := Nat.le_of_lt_succ iv.isLt
        omega
      have hvA : T.vertex ivT ∈ TreeSequenceVertexSet A := by
        simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨ivT.val, by omega⟩, (AToT.2.1 ⟨ivT.val, by omega⟩).symm⟩
      exact Finset.mem_biUnion.mpr ⟨T.vertex ivT, hvA, hcvT⟩
    · apply horder.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.castLE BToT.1 t,
        by change A.length ≤ t.val; omega, t.isLt, by rw [BToT.2.2 t]; exact hcolB⟩
  have hnotB : c ≠ beta := by
    intro he; subst c
    have hivB : ivT.val < ib.val := by
      have := iv.isLt
      simp only [TreeSequencePrefix] at this
      have htB : t.val < ib.val := t.isLt
      dsimp [ivT]
      omega
    have hivY : ivT.val ≤ Y.length := by omega
    have hvY := vertexY ivT hivY
    have hneV : T.vertex ivT ≠ vb := by
      intro he
      have hi := congrArg Fin.val (T.vertex_injective he)
      omega
    exact Finset.disjoint_left.mp (hElementaryY hvY hbY hneV) hcvT hb.1
  exact ⟨fun hc => hnotA (Option.some.inj (hcolB.symm.trans hc)),
    fun hc => hnotB (Option.some.inj (hcolB.symm.trans hc))⟩

theorem helper_routeTransport_711.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀
      (_ :
        (∀ {S U W : TreeSequence G e0} (_ : TreeSequenceInitialSegment S U)
          (_ : TreeSequenceInitialSegment U W), TreeSequenceInitialSegment S W))
      (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (_ : TreeSequenceInitialSegment B T) (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀
      (_ :
        (∀ v ∈ TreeSequenceVertexSet B,
          v ≠ vb → MissingColors G sigma v = MissingColors G phi v))
      (_ : (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)))
      (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence phi S B),
    TashkinovAugmentationSequence sigma S B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb segTrans hAib B BToT rpB
      aboveB strictB belowB genB baseB HB sigma missingBefore edgesFixed S hs
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

theorem helper_replacement_742.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (_ : IsProperEdgeColoring G phi) (_ : IsOneEdgeUncolored phi e0)
      (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (_ : TreeSequenceInitialSegment base.core A) (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (_ :
        MaximumProperty
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi })
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ : baseB.core = base.core)
      (HB :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (_ : IsProperEdgeColoring G sigma) (_ : IsOneEdgeUncolored sigma e0)
      (_ :
        (∀ (S : TreeSequence G e0) (_ : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A)
          (D : Finset (Fin k)) (_ : alpha ∉ D ∧ beta ∉ D), StableColoring S D phi sigma))
      (_ : StableColoring Tn Dn phi sigma) (_ : TreeSequenceInitialSegment Tn B)
      (_ : Tn.length < B.length)
      (_ :
        (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn B ∨
          (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
                TreeSequenceAdjoinEdge Tn f seed ∧
                  TashkinovAugmentationSequence phi seed B ∧
                    phi f ≠ some alpha ∧ phi f ≠ some beta))
      (_ :
        (∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence phi S B),
          TashkinovAugmentationSequence sigma S B)),
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    MaximumProperty corr.replacementETT ∧
    ∃ (baseS : HierarchyBase corr.replacementETT sigma) (HS :
      TashkinovHierarchy corr.replacementETT baseS),
    SameHierarchyStages HB HS := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn Dn ib
      vb coreToA hAib B rpB aboveB strictB belowB genB hMPB baseB hcoreB HB ettB sigma
      sigmaProper sigmaOne stable stableTn TnToB TnStrictB terminalRoute routeTransport
  by_cases hPE : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · have closureSubset : TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
      obtain ⟨_, _, ⟨u⟩⟩ := baseB.parallel hPE
      intro v hv
      apply TreeSequenceInitialSegmentVertexSetSubset coreToA
      rw [← hcoreB, u.vertexSet]
      exact Finset.mem_union_right _ hv
    have hcombined : CombinedStableColoring Tn baseB.closure Dn phi sigma :=
      ⟨stableTn, stable baseB.closure closureSubset ∅ (by simp)⟩
    have hseq : TashkinovAugmentationSequence sigma Tn B := by
      rcases terminalRoute with ⟨_, hs⟩ | ⟨hk, _⟩
      · exact routeTransport Tn hs
      · rcases hk with hk | hk <;> rw [hPE] at hk <;> cases hk
    exact HierarchySplitter G k e0 input B phi sigma ettB hMPB C.positive
      hlower baseB HB hPE hproper hone sigmaProper sigmaOne hcombined hseq
  · have hmod : ModColoring ettB sigma :=
      Td G k e0 input B phi ettB hMPB C.positive hlower sigma sigmaProper sigmaOne
        (by simpa only [ettB, ← ett.generatingColoring, n, Tn, Dn] using stableTn)
    have hroute :
        ((ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence sigma Tn B) ∨
        ((ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.SE ∨
          ettB.series.data.kind (Fin.last ettB.rounds) = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ettB.series.data.connectingEdges (Fin.last ettB.rounds) = {f} ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed B))
               := by
      rcases terminalRoute with ⟨hp, _⟩ | ⟨hk, f, seed, hedges, hadjoin, hs, _⟩
      · exact (hPE hp).elim
      · exact Or.inr ⟨hk, f, seed, hedges, hadjoin, routeTransport seed hs⟩
    obtain ⟨corr⟩ := hmod.2.2 B TnToB TnStrictB hroute
    have hMP := MaximumPropertyTransport G k e0 ettB sigma hmod B corr hMPB
    refine ⟨corr, hMP, ?_⟩
    rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
      hedges, hkinds, hproperSeries, honeSeries, hstableSeries⟩
    rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
    cases hr
    have heq : series = newSeries := eq_of_heq hs
    cases heq
    let rep : ExtendedTashkinovTree G k e0 newInput B sigma :=
      ⟨ett.rounds, rp, newSeries, above, strict, below, gen⟩
    let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
    have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
    have htree : newSeries.data.tree n.castSucc = Tn := by simpa [hj, ettB, Tn] using htrees j
    have hkind := hkinds n
    let pos : Fin ((newSeries.data.tree n.castSucc).length + 1) :=
      Fin.cast (congrArg (fun S : TreeSequence G e0 => S.length + 1) htree.symm)
        baseB.supportPosition
    let baseS : HierarchyBase rep sigma :=
      { core := baseB.core
        closure := baseB.closure
        supportPosition := pos
        supportPositive := by simpa [pos] using baseB.supportPositive
        terminalMissingColors := rfl
        parallel := by
          dsimp only [rep]
          intro hp
          exact (hPE (hkind.symm.trans hp)).elim
        nonparallel := by
          dsimp only [rep]
          intro hp
          exact (baseB.nonparallel hPE).trans htree.symm }
    let HS : TashkinovHierarchy rep baseS :=
      { dividerCount := HB.dividerCount
        stage := HB.stage
        baseStage := HB.baseStage.trans htree.symm
        terminalStage := HB.terminalStage
        nested := HB.nested
        strict := HB.strict
        dividerPosition := HB.dividerPosition
        dividerPositive := HB.dividerPositive
        dividerIncreasing := HB.dividerIncreasing
        dividerStage := HB.dividerStage
        coreInsideFirst := HB.coreInsideFirst }
    refine ⟨baseS, HS, ?_⟩
    refine ⟨rfl, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
    · exact ⟨fun hp => (hPE hp).elim, fun hp => (hPE (hkind.symm.trans hp)).elim⟩
    · intro hp; exact (hPE hp).elim

theorem helper_pathLe_1004.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let _ : ℕ := T.length - A.length;
    ∀ (_ : TreeSequenceInitialSegment A T) (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (_ : TreeSequenceInitialSegment B T) (_ : A.length < B.length) (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (_ :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc)
      (_ : stages (Fin.last (count + (1 : ℕ))) = B)
      (_ :
        (∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ)))
      (_ :
        (∀ (j : Fin (count + (1 : ℕ))),
          (stages j.castSucc).length < (stages j.succ).length))
      (positions : Fin count → Fin (B.length + (1 : ℕ)))
      (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ))
      (_ :
        (∀ (i j : Fin count) (_ : (↑i : ℕ) < (↑j : ℕ)),
          (↑(positions i) : ℕ) < (↑(positions j) : ℕ)))
      (_ :
        (∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega)))
      (_ :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
      (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    ∀ (_ : HierarchyStarredStage HS (Fin.last count) = A),
    HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb ell AToT hAib B BToT
      ABstrict rpB aboveB strictB belowB genB baseB ettB sigma corr baseS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HS hstarLast
  let tailB := B.length - A.length
  let candidatesT := (Finset.Icc 1 ell).filter fun i =>
    ∀ t : Fin T.length, A.length + i ≤ t.val →
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
  let candidatesB := (Finset.Icc 1 tailB).filter fun i =>
    ∀ t : Fin B.length, A.length + i ≤ t.val →
      G.ends (B.edge t) = s(B.vertex t.castSucc, B.vertex t.succ)
  have htail : 1 ≤ tailB := by dsimp [tailB]; omega
  have htailT : 1 ≤ ell := by dsimp [ell]; omega
  have htmem : ell ∈ candidatesT := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htailT, le_rfl⟩, ?_⟩
    intro t ht
    have hAT := AToT.1
    have := t.isLt
    dsimp [ell] at ht
    omega
  have hbmem : tailB ∈ candidatesB := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htail, le_rfl⟩, ?_⟩
    intro t ht
    have := t.isLt
    dsimp [tailB] at ht
    omega
  have hnT : candidatesT.Nonempty := ⟨ell, htmem⟩
  have hnB : candidatesB.Nonempty := ⟨tailB, hbmem⟩
  have hmT := Finset.min'_mem candidatesT hnT
  have hbounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hmT).1
  have hminB : candidatesB.min' hnB ≤ candidatesT.min' hnT := by
    by_cases ht : candidatesT.min' hnT ≤ tailB
    · apply Finset.min'_le
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbounds.1, ht⟩, ?_⟩
      intro t hpos
      have he := (Finset.mem_filter.mp hmT).2 (Fin.castLE BToT.1 t) hpos
      have hv0 := BToT.2.1 t.castSucc
      have hv1 := BToT.2.1 t.succ
      have hi0 : (Fin.castLE BToT.1 t).castSucc =
          Fin.castLE (Nat.succ_le_succ BToT.1) t.castSucc := Fin.ext rfl
      have hi1 : (Fin.castLE BToT.1 t).succ =
          Fin.castLE (Nat.succ_le_succ BToT.1) t.succ := Fin.ext rfl
      simpa only [BToT.2.2, hi0, hi1, hv0, hv1] using he
    · exact le_trans (Finset.min'_le candidatesB tailB hbmem) (by omega)
  unfold HierarchyPathNumber
  rw [hstarLast]
  change (if h : candidatesB.Nonempty then candidatesB.min' h else tailB) ≤
    (if h : candidatesT.Nonempty then candidatesT.min' h else ell)
  rw [dite_eq_left hnB, dite_eq_left hnT]
  exact hminB

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_segTrans_973.{u_1, u_2} :
    SharedFacts.ChangeLemmaBothOutsidePreparation1.initialSegmentTransitiveStatement.{u_1, u_2} :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.initialSegmentTransitive.{u_1, u_2}

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_commonPrefix_982.{u_1, u_2} :
    SharedFacts.ChangeLemmaBothOutsidePreparation1.comparableInitialSegmentsStatement.{u_1, u_2} :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.comparableInitialSegments.{u_1, u_2}

theorem helper_stageToT_998.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    ∀ (j : Fin (H.dividerCount + (2 : ℕ))),
    TreeSequenceInitialSegment (H.stage j) T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H stageSegment j
  have hs := stageSegment j.val (H.dividerCount + 1 - j.val) (by omega)
  have he : (⟨j.val + (H.dividerCount + 1 - j.val), by omega⟩ :
      Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
    Fin.ext (by simp only [Fin.val_last]; have := j.isLt; omega)
  simpa [he, H.terminalStage] using hs

theorem helper_lastPositive_1007.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    H.dividerCount ≠ (0 : ℕ) →
    A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A hz
  obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
  · have hv := congrArg Fin.val hzero
    simp only [Fin.val_last, Fin.coe_ofNat_eq_mod, Nat.zero_mod, q] at hv
    exact (hz hv).elim
  · simp only [A, HierarchyStarredStage, hi, Fin.cases_succ]
    congr 1
    apply Fin.ext
    have hv := congrArg Fin.val hi
    simpa [q] using hv.symm

theorem helper_coreToA_1018.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment base.core A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A segRefl segTrans stageSegment lastZero
      lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]
    exact segRefl _
  · rw [lastPositive hz]
    have hs := stageSegment 1 (H.dividerCount - 1) (by omega)
    have he : 1 + (H.dividerCount - 1) = H.dividerCount := by omega
    simpa [he] using segTrans H.coreInsideFirst hs

theorem helper_AToT_1032.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    (∀ {S U W : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
    (∀ (j : Fin (H.dividerCount + (2 : ℕ))), TreeSequenceInitialSegment (H.stage j) T) →
    (H.dividerCount = (0 : ℕ) → A = base.core) →
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment A T := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A segTrans stageToT lastZero lastPositive
  by_cases hz : H.dividerCount = 0
  · rw [lastZero hz]
    exact segTrans H.coreInsideFirst (stageToT ⟨1, by omega⟩)
  · rw [lastPositive hz]
    exact stageToT _

theorem helper_ordinaryToA_1038.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    (∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + (1 : ℕ)),
        TreeSequenceInitialSegment
          (H.stage (⟨a, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))
          (H.stage (⟨a + d, by omega⟩ : Fin (H.dividerCount + (2 : ℕ))))) →
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment Tn A →
    ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (H.stage j.castSucc) A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n Tn stageSegment lastPositive TnToA j
  by_cases hz : H.dividerCount = 0
  · have hj : j.castSucc = (0 : Fin (H.dividerCount + 2)) := Fin.ext (by simp; omega)
    rw [hj, H.baseStage]
    exact TnToA
  · have hs := stageSegment j.val (H.dividerCount - j.val) (by omega)
    rw [lastPositive hz]
    convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;>
      simp only [Fin.val_castSucc]; omega

theorem helper_firstMissing_1057.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment Y T →
    ∀ c ∈ TreeMissingColors phi Y,
    c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
    (↑(HierarchyFirstMissingPosition phi T c) : ℕ) ≤ Y.length := by
  exact @GoldbergSeymour.SharedFacts.MixedChangeTransport.firstMissingPositionWitness

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_outsideIndex_1087.{u_1, u_2} :
    SharedFacts.ChangeLemmaBothOutsidePreparation1.missingPositionOutsidePrefixStatement.{u_1,
        u_2} :=
  SharedFacts.ChangeLemmaBothOutsidePreparation1.missingPositionOutsidePrefix.{u_1, u_2}

theorem helper_missingNotA_1098.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    alpha ≠ beta →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ yLength) ↦ by omega)
        (by omega);
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    TreeSequenceInitialSegment A Y →
    ∀ (c : Fin k) (i : Fin (T.length + (1 : ℕ))),
    c ∈ MissingColors G phi (T.vertex i) →
    T.vertex i ∈ TreeSequenceVertexSet Y →
    T.vertex i ∉ TreeSequenceVertexSet A →
    c ∉ TreeMissingColors phi A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A ell yLength Y hElementaryY
      AToY c i hmi hiy hia hc
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  have hne : v ≠ T.vertex i := by intro he; exact hia (he ▸ hv)
  exact (Finset.disjoint_left.mp
    (hElementaryY (TreeSequenceInitialSegmentVertexSetSubset AToY hv) hiy hne)) hcv hmi

theorem helper_BstrictT_1127.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
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
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib ell yLength Y AToT hAib B
      ABstrict BToY
  have hAT := AToT.1
  have hY : Y.length = min (A.length + (T.length - A.length - 1)) T.length := rfl
  have hBY := BToY.1
  have hAB := ABstrict
  omega

theorem helper_outsideStored_1149.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    (H.dividerCount ≠ (0 : ℕ) →
        A = H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) →
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    alpha ∉ TreeMissingColors phi A →
    beta ∉ TreeMissingColors phi A →
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    (∀ {S U : TreeSequence G e0},
        TreeSequenceInitialSegment S U →
          TreeMissingColors phi S ⊆ TreeMissingColors phi U) →
    (0 : ℕ) < H.dividerCount ∧
          (alpha ∈
              TreeMissingColors phi
                (H.stage (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + (2 : ℕ)))) ∨
            Disjoint (insert alpha ({ beta } : Finset (Fin k)) : Finset (Fin k))
              (HierarchyStoredColorsAt H q)) ∨
        H.dividerCount = (0 : ℕ) ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            Disjoint (insert alpha ({ beta } : Finset (Fin k)) : Finset (Fin k)) Dn) →
    alpha ∉ Dn ∧
    beta ∉ Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn Dn ib lastPositive TnToA
      hAib halphaA hbetaA B rpB aboveB strictB belowB genB baseB HB missingSubset hcase
  rcases hcase with ⟨hp, hm | hd⟩ | ⟨hz, hm | hd⟩
  · exact (halphaA (by simpa [lastPositive (by omega)] using hm)).elim
  · have hn (c : Fin k) (hc : c ∈ ({alpha, beta} : Finset (Fin k)))
        (hcm : c ∉ TreeMissingColors phi A) : c ∉ Dn := by
      intro hcd
      apply Finset.disjoint_left.mp hd hc
      exact Finset.mem_sdiff.mpr ⟨hcd, hcm⟩
    exact ⟨hn alpha (by simp) halphaA, hn beta (by simp) hbetaA⟩
  · exact (halphaA (missingSubset TnToA hm)).elim
  · exact ⟨fun hc => Finset.disjoint_left.mp hd (by simp) hc,
      fun hc => Finset.disjoint_left.mp hd (by simp) hc⟩

theorem helper_unaffected_1187.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
          PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
          input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta : Fin k),
      alpha ≠ beta →
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
            ∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne H q A ib vb ell yLength Y ha hb
      K sigma f c hca hcb
  by_cases hf : Sum.inr f ∈ K
  · by_cases ha : phi f = some alpha
    · simp [sigma, TwoColorComponentSwap, K, hf, ha, hca.symm, hcb.symm]
    · by_cases hb : phi f = some beta
      · simp [sigma, TwoColorComponentSwap, K, hf, hb, hne.symm,
          hca.symm, hcb.symm]
      · simp [sigma, TwoColorComponentSwap, K, hf, ha, hb]
  · simp [sigma, TwoColorComponentSwap, K, hf]

theorem helper_sigmaOne_1202.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsOneEdgeUncolored phi e0 →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
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
  intro V E _ _ _ _ G k e0 input T phi ett base C hone alpha beta hne H q A ib vb ell yLength Y
      ha hb K sigma unaffected
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

theorem helper_stable_1247.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    alpha ∉ TreeMissingColors phi A →
    beta ∉ TreeMissingColors phi A →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
    ∀ (D : Finset (Fin k)),
    alpha ∉ D ∧ beta ∉ D →
    StableColoring S D phi sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb halphaA hbetaA sigma
      unaffected missingA S hS D hD
  refine ⟨?_, fun v hv => missingA v (hS hv)⟩
  intro f hf hcontrol
  obtain ⟨c, hc, hcol⟩ := hcontrol
  have hnot (d : Fin k) (hdA : d ∉ TreeMissingColors phi A) (hdD : d ∉ D) : c ≠ d := by
    intro he; subst c
    rcases Finset.mem_union.mp hc with hm | hm
    · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hm
      exact hdA (Finset.mem_biUnion.mpr ⟨v, hS hv, hcv⟩)
    · exact hdD hm
  exact ((unaffected f c (hnot alpha halphaA hD.1) (hnot beta hbetaA hD.2)).mpr hcol).trans
    hcol.symm

theorem helper_storedOrMissing_1276.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    ∀ c ∈ ett.series.data.stored n,
    c ∈ TreeMissingColors phi Tn ∪ Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn Dn ib hAib B rpB aboveB
      strictB belowB genB baseB HB c hc
  by_cases hm : c ∈ TreeMissingColors phi Tn
  · exact Finset.mem_union_left _ hm
  · apply Finset.mem_union_right
    unfold Dn TashkinovStoredColors
    have hn : n.val ≠ 0 := by dsimp [n]; have := C.positive; omega
    simp only [ite_eq_right hn]
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_univ _, by simp [hc]⟩
    · have hg : ett.series.data.coloring n = phi := ett.generatingColoring.symm
      simpa only [hg, Tn] using hm

theorem helper_treeControlled_1302.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsOneEdgeUncolored phi e0 →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    (∀ (c : Fin k), c = alpha ∨ c = beta → c ∉ TreeMissingColors phi Tn ∪ Dn) →
    ∀ (t : Fin Tn.length),
    phi (Tn.edge t) ≠ some alpha ∧
    phi (Tn.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hone alpha beta H q A n Tn Dn ib hAib B rpB
      aboveB strictB belowB genB baseB HB notControlled t
  by_cases ht : t.val = 0
  · have he : Tn.edge t = e0 := by
      rw [show t = ⟨0, Tn.positive⟩ from Fin.ext ht]
      exact Tn.first_edge
    simp [he, hone.1]
  · let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
    have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
    have hused (c : Fin k) (hc : phi (Tn.edge t) = some c) :
        c ∈ TreeMissingColors phi Tn ∪ Dn := by
      have hu : c ∈ TreeUsedColors (ett.series.data.coloring j.succ)
          (ett.series.data.tree j.succ.castSucc) := by
        simp only [hj, ← ett.generatingColoring, n]
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨t, by omega, hc⟩
      simpa [hj, ← ett.generatingColoring, Tn, Dn, n] using
        (HkuTreeColorsControlled G k ett.rounds e0 input ett.series j).2.1 hu
    exact ⟨fun hc => notControlled alpha (Or.inl rfl) (hused alpha hc),
      fun hc => notControlled beta (Or.inr rfl) (hused beta hc)⟩

theorem helper_augmentationControlled_1322.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
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
    TreeSequenceInitialSegment A T →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    (∀ (i : Fin (T.length + (1 : ℕ))),
        (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
    vb ∈ TreeSequenceVertexSet Y →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    alpha ∉ TreeMissingColors phi A →
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
    B.length < T.length →
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB)
      (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S B →
    ∀ (t : Fin B.length),
    S.length ≤ (↑t : ℕ) →
    phi (B.edge t) ≠ some alpha ∧
    phi (B.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb ell yLength Y AToT
      hElementaryY hb vertexY hbY hAib halphaA horder B BToT BstrictT rpB aboveB strictB belowB
      genB baseB HB S hseq t ht
  exact @helper_augmentationControlled_640 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
      (@alpha) (@beta) (@AToT) (@hElementaryY) (@hb) (@vertexY) (@hbY) (@hAib) (@halphaA)
      (@horder) (@BToT) (@BstrictT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
      (@HB) (@S) (@hseq) (@t) (@ht)

theorem helper_allControlled_1331.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    TreeSequenceInitialSegment Tn B →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed B ∧
                  phi f ≠ some alpha ∧ phi f ≠ some beta) →
    (∀ (t : Fin Tn.length), phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B →
          ∀ (t : Fin B.length),
            S.length ≤ (↑t : ℕ) →
              phi (B.edge t) ≠ some alpha ∧ phi (B.edge t) ≠ some beta) →
    ∀ (t : Fin B.length),
    phi (B.edge t) ≠ some alpha ∧
    phi (B.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib hAib B rpB aboveB
      strictB belowB genB baseB HB TnToB terminalRoute treeControlled augmentationControlled t
  by_cases ht : t.val < Tn.length
  · have he := TnToB.2.2 ⟨t.val, ht⟩
    have hi : Fin.castLE TnToB.1 ⟨t.val, ht⟩ = t := Fin.ext rfl
    rw [hi] at he
    rw [he]
    exact treeControlled _
  · rcases terminalRoute with ⟨hp, hs⟩ | ⟨hk, f, seed, hedges, hadjoin, hs, hfa, hfb⟩
    · exact augmentationControlled Tn hs t (by omega)
    · by_cases he : t.val = Tn.length
      · have hSB := TashkinovAugmentationSequenceInitialSegment phi seed B hs
        have hi := hSB.2.2 (Fin.cast hadjoin.1.symm (Fin.last Tn.length))
        have hj : Fin.castLE hSB.1 (Fin.cast hadjoin.1.symm (Fin.last Tn.length)) = t :=
          Fin.ext (by simpa using he.symm)
        rw [hj, hadjoin.2.2] at hi
        simpa [hi] using And.intro hfa hfb
      · exact augmentationControlled seed hs t (by have := hadjoin.1; omega)

theorem helper_replacement_1357.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment base.core A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    MaximumProperty
        { rounds := ett.1, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB,
          belowFinal := belowB, generatingColoring := genB :
          ExtendedTashkinovTree G k e0 input B phi } →
    ∀
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    baseB.core = base.core →
    ∀
      (HB :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          ∀ (D : Finset (Fin k)), alpha ∉ D ∧ beta ∉ D → StableColoring S D phi sigma) →
    StableColoring Tn Dn phi sigma →
    TreeSequenceInitialSegment Tn B →
    Tn.length < B.length →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed B ∧
                  phi f ≠ some alpha ∧ phi f ≠ some beta) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B → TashkinovAugmentationSequence sigma S B) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    MaximumProperty corr.replacementETT ∧
    ∃ (baseS : HierarchyBase corr.replacementETT sigma) (HS :
      TashkinovHierarchy corr.replacementETT baseS),
    SameHierarchyStages HB HS := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn Dn ib
      vb coreToA hAib B rpB aboveB strictB belowB genB hMPB baseB hcoreB HB ettB sigma
      sigmaProper sigmaOne stable stableTn TnToB TnStrictB terminalRoute routeTransport
  exact @helper_replacement_742 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
      (@hone) (@hlower) (@alpha) (@beta) (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB)
      (@belowB) (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@sigmaProper) (@sigmaOne) (@stable)
      (@stableTn) (@TnToB) (@TnStrictB) (@terminalRoute) (@routeTransport)

theorem helper_storedS_1369.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (HB :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    MaximumProperty corr.replacementETT →
    ∀ (baseS : HierarchyBase corr.replacementETT sigma)
      (HS : TashkinovHierarchy corr.replacementETT baseS),
    SameHierarchyStages HB HS →
    TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds) =
      Dn := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn Dn ib vb TnToA hAib B rpB
      aboveB strictB belowB genB baseB HB ettB sigma treeMissingEq corr hMPS baseS HS hsame
  rcases corr with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
    hedges, hkinds, hproperSeries, honeSeries, hstableSeries⟩
  rcases newETT with ⟨r, rp, series, above, strict, below, gen⟩
  cases hr
  have heq : series = newSeries := eq_of_heq hs
  cases heq
  let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
  have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
  have htree : newSeries.data.tree n.castSucc = Tn := by simpa [hj, ettB, Tn] using htrees j
  have hm := treeMissingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToA)
  unfold Dn TashkinovStoredColors
  simp only [ettB, hstored, ← hgen, ← ett.generatingColoring, htree, hm, n, Tn]

theorem helper_closureBToA_1398.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (_ beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    TreeSequenceInitialSegment base.core A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    baseB.core = base.core →
    ett.series.data.kind n = some TashkinovExtensionKind.PE →
    TreeSequenceVertexSet baseB.closure ⊆ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n ib coreToA hAib B rpB aboveB
      strictB belowB genB baseB hcoreB hp
  obtain ⟨_, _, ⟨u⟩⟩ := baseB.parallel hp
  intro v hv
  apply TreeSequenceInitialSegmentVertexSetSubset coreToA
  rw [← hcoreB, u.vertexSet]
  exact Finset.mem_union_right _ hv

theorem helper_minusEq_1405.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
      (C : HierarchyCounterexample base) (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    alpha ∉ TreeMissingColors phi A →
    beta ∉ TreeMissingColors phi A →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (f : E) (c : Fin k), c ≠ alpha → c ≠ beta → (sigma f = some c ↔ phi f = some c)) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
    ∀ (D : Finset (Fin k)),
    TreeColorSetMinusClosed G sigma S D ↔ TreeColorSetMinusClosed G phi S D := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb halphaA hbetaA sigma
      unaffected treeMissingEq S hS D
  unfold TreeColorSetMinusClosed TreeColorSetClosed
  rw [treeMissingEq S hS]
  have boundaryEq (c : Fin k) (hc : c ∈ TreeMissingColors phi S) :
      BoundaryColorEdges G sigma (TreeSequenceVertexSet S) c =
        BoundaryColorEdges G phi (TreeSequenceVertexSet S) c := by
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    have hcA : c ∈ TreeMissingColors phi A := Finset.mem_biUnion.mpr ⟨v, hS hv, hcv⟩
    have hca : c ≠ alpha := by intro he; exact halphaA (he ▸ hcA)
    have hcb : c ≠ beta := by intro he; exact hbetaA (he ▸ hcA)
    ext f
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact and_congr_right (fun _ => unaffected f c hca hcb)
  exact ⟨fun hs c hc => (boundaryEq c (Finset.mem_sdiff.mp hc).1).symm.trans (hs c hc),
    fun hs c hc => (boundaryEq c (Finset.mem_sdiff.mp hc).1).trans (hs c hc)⟩

theorem helper_storedEq_1440.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma),
    TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) =
        Dn →
    ∀ (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          (HierarchyStarredStage
            { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }
            j)
          A) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Dn ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma treeMissingEq corr baseS storedS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore starBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS starEq j
  change TashkinovStoredColors corr.replacementETT.series.data
      (Fin.last corr.replacementETT.rounds) \ TreeMissingColors sigma (HierarchyStarredStage
          HS j) =
    Dn \ TreeMissingColors phi (HierarchyStarredStage HB j)
  rw [storedS, starEq, treeMissingEq _ (TreeSequenceInitialSegmentVertexSetSubset (starBToA j))]

theorem helper_missingEq_1447.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
  exact @GoldbergSeymour.SharedFacts.MixedChangeTransport.missingColorsEquality

theorem helper_firstEq_1458.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    alpha ∉ Dn ∧ beta ∉ Dn →
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
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
    ∀ eta ∈ Dn,
    HierarchyFirstMissingPosition sigma B eta = HierarchyFirstMissingPosition phi B eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Dn ib vb hAib B hDn sigma
      behavior eta he
  have hea : eta ≠ alpha := by intro h; exact hDn.1 (h ▸ he)
  have heb : eta ≠ beta := by intro h; exact hDn.2 (h ▸ he)
  have hcandidates : (Finset.univ.filter fun i => eta ∈ MissingColors G sigma (B.vertex i)) =
      (Finset.univ.filter fun i => eta ∈ MissingColors G phi (B.vertex i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact behavior.2.2.2 _ eta hea heb
  unfold HierarchyFirstMissingPosition
  rw [hcandidates]

theorem helper_segmentEq_1469.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (2 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j)
          B) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    (∀ eta ∈ Dn,
        HierarchyFirstMissingPosition sigma B eta =
          HierarchyFirstMissingPosition phi B eta) →
    ∀ (j : Fin (count + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt HB j,
    HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Dn ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma edgesFixed corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
      firstEq j eta he
  have heDn : eta ∈ Dn := (Finset.mem_sdiff.mp he).1
  have hedge (t : Fin (stages j.succ).length) :
      sigma ((stages j.succ).edge t) = phi ((stages j.succ).edge t) := by
    have hSB := stageBToB j.succ
    have hf := edgesFixed (Fin.castLE hSB.1 t)
    rw [hSB.2.2] at hf
    exact hf
  unfold HierarchySegmentColors
  simp only [starEq, firstEq eta heDn, HS, HB, hedge]

theorem helper_refreshEq_1481.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (i : Fin count),
    ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G sigma v) =
      (TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma missingA corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq i
  rw [starEq]
  apply Finset.biUnion_congr rfl
  intro v hv
  exact missingA v (TreeSequenceInitialSegmentVertexSetSubset (stageBToA i.succ)
    (Finset.mem_sdiff.mp hv).1)

theorem helper_hstarLast_1534.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let _ : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
      (hcountB :
        { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }.dividerCount =
          H.dividerCount),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        have jo : Fin (H.dividerCount + (1 : ℕ)) := Fin.cast (by omega) j;
        { dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.stage
              j.castSucc =
            H.stage jo.castSucc ∧
          HierarchyStarredStage
              { dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }
              j =
            HierarchyStarredStage H jo) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    HierarchyStarredStage HS (Fin.last count) = A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma corr baseS count stages hbbase hbterminal hbnested
      hbstrict positions hbpositive hbincreasing hbdivider hbcore hcountB hstagesB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
  rw [starEq]
  have hs := (hstagesB (Fin.last count)).2
  have hj : Fin.cast (congrArg (fun n : ℕ => n + 1) hcountB) (Fin.last count) = q :=
    Fin.ext (by simp [q])
  simpa only [hj] using hs

theorem helper_pathLe_1546.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment A T →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    A.length < B.length →
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0),
    stages (0 : Fin (count + (2 : ℕ))) =
        { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
          (Fin.last
              { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc →
    stages (Fin.last (count + (1 : ℕ))) = B →
    (∀ (j : Fin (count + (1 : ℕ))),
        TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ)) →
    (∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length) →
    ∀ (positions : Fin count → Fin (B.length + (1 : ℕ)))
      (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ)),
    (∀ (i j : Fin count),
        (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ)) →
    (∀ (i : Fin count),
        stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
          TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega)) →
    TreeSequenceInitialSegment baseB.core
        (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    HierarchyStarredStage HS (Fin.last count) = A →
    HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb AToT hAib B BToT
      ABstrict rpB aboveB strictB belowB genB baseB ettB sigma corr baseS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HS hstarLast
  exact @helper_pathLe_1004 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@AToT)
      (@hAib) (@BToT) (@ABstrict) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
      (@corr) (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@positionsS)
      (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
      (@hsdivider) (@hscore) (@hstarLast)

theorem helper_augmentationControlled_3288.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
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
    TreeSequenceInitialSegment A T →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    (∀ (i : Fin (T.length + (1 : ℕ))),
        (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
    vb ∈ TreeSequenceVertexSet Y →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    alpha ∉ TreeMissingColors phi A →
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
    B.length < T.length →
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB)
      (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S B →
    ∀ (t : Fin B.length),
    S.length ≤ (↑t : ℕ) →
    phi (B.edge t) ≠ some alpha ∧
    phi (B.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb ell yLength Y AToT
      hElementaryY hb vertexY hbY hAib halphaA horder B BToT BstrictT rpB aboveB strictB belowB
      genB baseB HB S hseq t ht
  exact @helper_augmentationControlled_1322 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
      (@alpha) (@beta) (@AToT) (@hElementaryY) (@hb) (@vertexY) (@hbY) (@hAib) (@halphaA)
      (@horder) (@BToT) (@BstrictT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
      (@HB) (@S) (@hseq) (@t) (@ht)

theorem helper_replacement_3311.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment base.core A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1)),
    MaximumProperty
        { rounds := ett.1, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB,
          belowFinal := belowB, generatingColoring := genB :
          ExtendedTashkinovTree G k e0 input B phi } →
    ∀
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    baseB.core = base.core →
    ∀
      (HB :
        TashkinovHierarchy
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          ∀ (D : Finset (Fin k)), alpha ∉ D ∧ beta ∉ D → StableColoring S D phi sigma) →
    StableColoring Tn Dn phi sigma →
    TreeSequenceInitialSegment Tn B →
    Tn.length < B.length →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed B ∧
                  phi f ≠ some alpha ∧ phi f ≠ some beta) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B → TashkinovAugmentationSequence sigma S B) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    MaximumProperty corr.replacementETT ∧
    ∃ (baseS : HierarchyBase corr.replacementETT sigma) (HS :
      TashkinovHierarchy corr.replacementETT baseS),
    SameHierarchyStages HB HS := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn Dn ib
      vb coreToA hAib B rpB aboveB strictB belowB genB hMPB baseB hcoreB HB ettB sigma
      sigmaProper sigmaOne stable stableTn TnToB TnStrictB terminalRoute routeTransport
  exact @helper_replacement_1357 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
      (@hone) (@hlower) (@alpha) (@beta) (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB)
      (@belowB) (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@sigmaProper) (@sigmaOne) (@stable)
      (@stableTn) (@TnToB) (@TnStrictB) (@terminalRoute) (@routeTransport)

theorem helper_storedEq_3373.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma),
    TashkinovStoredColors corr.replacementETT.series.data
          (Fin.last corr.replacementETT.rounds) =
        Dn →
    ∀ (count : ℕ) (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          (HierarchyStarredStage
            { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }
            j)
          A) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStoredColorsAt HS j = HierarchyStoredColorsAt HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Dn ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma treeMissingEq corr baseS storedS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore starBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS starEq j
  exact @helper_storedEq_1440 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@treeMissingEq) (@corr)
      (@baseS) (@storedS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@starBToA)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@starEq) (@j)

theorem helper_missingEq_3382.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment Tn A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          TreeMissingColors sigma S = TreeMissingColors phi S) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    ∀ (j : Fin (count + (1 : ℕ))),
    HierarchyStageMissingColors HS j = HierarchyStageMissingColors HB j := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb TnToA hAib B rpB
      aboveB strictB belowB genB baseB ettB sigma treeMissingEq corr baseS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA
      positionsS hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB
      HS j
  exact @helper_missingEq_1447 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@TnToA) (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
      (@treeMissingEq) (@corr) (@baseS) (@count) (@stages) (@hbbase) (@hbterminal)
      (@hbnested) (@hbstrict) (@positions) (@hbpositive) (@hbincreasing) (@hbdivider)
      (@hbcore) (@stageBToA) (@positionsS) (@hspositive) (@hsincreasing) (@hsbase)
      (@hsterminal) (@hsnested) (@hsstrict) (@hsdivider) (@hscore) (@j)

theorem helper_segmentEq_3397.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ (t : Fin B.length), sigma (B.edge t) = phi (B.edge t)) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (2 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j)
          B) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    (∀ eta ∈ Dn,
        HierarchyFirstMissingPosition sigma B eta =
          HierarchyFirstMissingPosition phi B eta) →
    ∀ (j : Fin (count + (1 : ℕ))),
    ∀ eta ∈ HierarchyStoredColorsAt HB j,
    HierarchySegmentColors HS j eta = HierarchySegmentColors HB j eta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Dn ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma edgesFixed corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
      firstEq j eta he
  exact @helper_segmentEq_1469 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@edgesFixed) (@corr)
      (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToB)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@starEq) (@firstEq) (@j) (@eta) (@he)

theorem helper_refreshEq_3407.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    (∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        TreeSequenceInitialSegment
          ({ dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }.stage
            j.castSucc)
          A) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    ∀ (i : Fin count),
    ((TreeSequenceVertexSet (HS.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HS i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G sigma v) =
      (TreeSequenceVertexSet (HB.stage i.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage HB i.castSucc)).biUnion
        fun (v : V) ↦ MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma missingA corr baseS count stages hbbase hbterminal
      hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore stageBToA positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq i
  exact @helper_refreshEq_1481 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@missingA) (@corr)
      (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@stageBToA)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@starEq) (@i)

theorem helper_hstarLast_3462.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0)
      (hbbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                belowFinal := belowB, generatingColoring := genB :
                ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
            (Fin.last
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
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
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ))
      (hbdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega))
      (hbcore :
        TreeSequenceInitialSegment baseB.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))))
      (hcountB :
        { dividerCount := count, stage := stages, baseStage := hbbase,
              terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
              dividerPosition := positions, dividerPositive := hbpositive,
              dividerIncreasing := hbincreasing, dividerStage := hbdivider,
              coreInsideFirst := hbcore :
              TashkinovHierarchy
                { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }
                baseB }.dividerCount =
          H.dividerCount),
    (∀
        (j :
          Fin
            ({ dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.dividerCount +
              (1 : ℕ))),
        have jo : Fin (H.dividerCount + (1 : ℕ)) := Fin.cast (by omega) j;
        { dividerCount := count, stage := stages, baseStage := hbbase,
                  terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                  dividerPosition := positions, dividerPositive := hbpositive,
                  dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                  coreInsideFirst := hbcore :
                  TashkinovHierarchy
                    { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                      abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                      belowFinal := belowB, generatingColoring := genB :
                      ExtendedTashkinovTree G k e0 input B phi }
                    baseB }.stage
              j.castSucc =
            H.stage jo.castSucc ∧
          HierarchyStarredStage
              { dividerCount := count, stage := stages, baseStage := hbbase,
                terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
                dividerPosition := positions, dividerPositive := hbpositive,
                dividerIncreasing := hbincreasing, dividerStage := hbdivider,
                coreInsideFirst := hbcore :
                TashkinovHierarchy
                  { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                    abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                    belowFinal := belowB, generatingColoring := genB :
                    ExtendedTashkinovTree G k e0 input B phi }
                  baseB }
              j =
            HierarchyStarredStage H jo) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HB : TashkinovHierarchy ettB baseB :=
      { dividerCount := count, stage := stages, baseStage := hbbase,
        terminalStage := hbterminal, nested := hbnested, strict := hbstrict,
        dividerPosition := positions, dividerPositive := hbpositive,
        dividerIncreasing := hbincreasing, dividerStage := hbdivider,
        coreInsideFirst := hbcore : TashkinovHierarchy ettB baseB };
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    (∀ (j : Fin (count + (1 : ℕ))),
        HierarchyStarredStage HS j = HierarchyStarredStage HB j) →
    HierarchyStarredStage HS (Fin.last count) = A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb hAib B rpB aboveB
      strictB belowB genB baseB ettB sigma corr baseS count stages hbbase hbterminal hbnested
      hbstrict positions hbpositive hbincreasing hbdivider hbcore hcountB hstagesB positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HB HS starEq
  exact @helper_hstarLast_1534 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hAib) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB) (@corr) (@baseS)
      (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict) (@positions)
      (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@hcountB) (@hstagesB)
      (@positionsS) (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested)
      (@hsstrict) (@hsdivider) (@hscore) (@starEq)

theorem helper_pathLe_3476.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    TreeSequenceInitialSegment A T →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (by omega);
    TreeSequenceInitialSegment B T →
    A.length < B.length →
    ∀ (rpB : (1 : ℕ) ≤ ett.1)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) B)
      (strictB :
        (ett.series.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B (ett.series.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.1))
      (baseB :
        HierarchyBase
          { rounds := ett.1, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B)
      (baseS : HierarchyBase corr.replacementETT sigma) (count : ℕ)
      (stages : Fin (count + (2 : ℕ)) → TreeSequence G e0),
    stages (0 : Fin (count + (2 : ℕ))) =
        { rounds := ett.1, roundsPositive := rpB, series := ett.series,
              abovePenultimate := aboveB, strictAbovePenultimate := strictB,
              belowFinal := belowB, generatingColoring := genB :
              ExtendedTashkinovTree G k e0 input B phi }.series.data.tree
          (Fin.last
              { rounds := ett.1, roundsPositive := rpB, series := ett.series,
                  abovePenultimate := aboveB, strictAbovePenultimate := strictB,
                  belowFinal := belowB, generatingColoring := genB :
                  ExtendedTashkinovTree G k e0 input B phi }.rounds).castSucc →
    stages (Fin.last (count + (1 : ℕ))) = B →
    (∀ (j : Fin (count + (1 : ℕ))),
        TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ)) →
    (∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length) →
    ∀ (positions : Fin count → Fin (B.length + (1 : ℕ)))
      (hbpositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positions i) : ℕ)),
    (∀ (i j : Fin count),
        (↑i : ℕ) < (↑j : ℕ) → (↑(positions i) : ℕ) < (↑(positions j) : ℕ)) →
    (∀ (i : Fin count),
        stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
          TreeSequencePrefix B (↑(positions i) : ℕ) (hbpositive i) (by omega)) →
    TreeSequenceInitialSegment baseB.core
        (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ)))) →
    ∀ (positionsS : Fin count → Fin (B.length + (1 : ℕ)))
      (hspositive : ∀ (i : Fin count), (1 : ℕ) ≤ (↑(positionsS i) : ℕ))
      (hsincreasing :
        ∀ (i j : Fin count),
          (↑i : ℕ) < (↑j : ℕ) → (↑(positionsS i) : ℕ) < (↑(positionsS j) : ℕ))
      (hsbase :
        stages (0 : Fin (count + (2 : ℕ))) =
          corr.replacementETT.series.data.tree
            (Fin.last corr.replacementETT.rounds).castSucc)
      (hsterminal : stages (Fin.last (count + (1 : ℕ))) = B)
      (hsnested :
        ∀ (j : Fin (count + (1 : ℕ))),
          TreeSequenceInitialSegment (stages j.castSucc) (stages j.succ))
      (hsstrict :
        ∀ (j : Fin (count + (1 : ℕ))), (stages j.castSucc).length < (stages j.succ).length)
      (hsdivider :
        ∀ (i : Fin count),
          stages (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))) =
            TreeSequencePrefix B (↑(positionsS i) : ℕ) (hspositive i) (by omega))
      (hscore :
        TreeSequenceInitialSegment baseS.core
          (stages (⟨(1 : ℕ), by omega⟩ : Fin (count + (2 : ℕ))))),
    let HS : TashkinovHierarchy corr.replacementETT baseS :=
      { dividerCount := count, stage := stages, baseStage := hsbase,
        terminalStage := hsterminal, nested := hsnested, strict := hsstrict,
        dividerPosition := positionsS, dividerPositive := hspositive,
        dividerIncreasing := hsincreasing, dividerStage := hsdivider,
        coreInsideFirst := hscore : TashkinovHierarchy corr.replacementETT baseS };
    HierarchyStarredStage HS (Fin.last count) = A →
    HierarchyPathNumber HS ≤ HierarchyPathNumber H := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A ib vb AToT hAib B BToT
      ABstrict rpB aboveB strictB belowB genB baseB ettB sigma corr baseS count stages hbbase
      hbterminal hbnested hbstrict positions hbpositive hbincreasing hbdivider hbcore positionsS
      hspositive hsincreasing hsbase hsterminal hsnested hsstrict hsdivider hscore HS hstarLast
  exact @helper_pathLe_1546 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@AToT)
      (@hAib) (@BToT) (@ABstrict) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
      (@corr) (@baseS) (@count) (@stages) (@hbbase) (@hbterminal) (@hbnested) (@hbstrict)
      (@positions) (@hbpositive) (@hbincreasing) (@hbdivider) (@hbcore) (@positionsS)
      (@hspositive) (@hsincreasing) (@hsbase) (@hsterminal) (@hsnested) (@hsstrict)
      (@hsdivider) (@hscore) (@hstarLast)

theorem helper_augmentationControlled_5115.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let ib : Fin (T.length + (1 : ℕ)) := HierarchyFirstMissingPosition phi T beta;
    let vb : V := T.vertex ib;
    let ell : ℕ := T.length - A.length;
    let yLength : ℕ := min (A.length + (ell - (1 : ℕ))) T.length;
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix T yLength
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        have _ : (1 : ℕ) ≤ T.length := T.positive;
        have _ : (1 : ℕ) ≤ A.length := A.positive;
        by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        omega)
        (have _ : (1 : ℕ) ≤ T.length := T.positive;
        have _ : (1 : ℕ) ≤ A.length := A.positive;
        by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        omega);
    TreeSequenceInitialSegment A T →
    ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) →
    beta ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
        (↑(HierarchyFirstMissingPosition phi T beta) : ℕ) ≤ Y.length →
    (∀ (i : Fin (T.length + (1 : ℕ))),
        (↑i : ℕ) ≤ Y.length → T.vertex i ∈ TreeSequenceVertexSet Y) →
    vb ∈ TreeSequenceVertexSet Y →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    alpha ∉ TreeMissingColors phi A →
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
        have _ : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (have _ : (1 : ℕ) ≤ T.length := T.positive;
        have _ : (1 : ℕ) ≤ A.length := A.positive;
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega);
    TreeSequenceInitialSegment B T →
    B.length < T.length →
    ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree
            (⟨ett.rounds,
                have _ : (1 : ℕ) ≤ T.length := T.positive;
                have _ : (1 : ℕ) ≤ A.length := A.positive;
                have _ : (1 : ℕ) ≤ Tn.length := Tn.positive;
                have _ : (1 : ℕ) ≤ Y.length := Y.positive;
                have _ : (1 : ℕ) ≤ B.length := B.positive;
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (ett.rounds + (2 : ℕ))))
          B)
      (strictB :
        (ett.series.data.tree
              (⟨ett.rounds,
                  have _ : (1 : ℕ) ≤ T.length := T.positive;
                  have _ : (1 : ℕ) ≤ A.length := A.positive;
                  have _ : (1 : ℕ) ≤ Tn.length := Tn.positive;
                  have _ : (1 : ℕ) ≤ Y.length := Y.positive;
                  have _ : (1 : ℕ) ≤ B.length := B.positive;
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
          { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi)
      (_ :
        TashkinovHierarchy
          { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB)
      (S : TreeSequence G e0),
    TashkinovAugmentationSequence phi S B →
    ∀ (t : Fin B.length),
    S.length ≤ (↑t : ℕ) →
    phi (B.edge t) ≠ some alpha ∧
    phi (B.edge t) ≠ some beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta H q A n Tn ib vb ell yLength Y AToT
      hElementaryY hb vertexY hbY hAib halphaA horder B BToT BstrictT rpB aboveB strictB belowB
      genB baseB HB S hseq t ht
  exact @helper_augmentationControlled_3288 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
      (@alpha) (@beta) (@AToT) (@hElementaryY) (@hb) (@vertexY) (@hbY) (@hAib) (@halphaA)
      (@horder) (@BToT) (@BstrictT) (@rpB) (@aboveB) (@strictB) (@belowB) (@genB) (@baseB)
      (@HB) (@S) (@hseq) (@t) (@ht)

theorem helper_replacement_5138.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (alpha beta : Fin k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
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
        have _ : (1 : ℕ) ≤ T.length := T.positive;
        have _ : (1 : ℕ) ≤ A.length := A.positive;
        by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        omega)
        (have _ : (1 : ℕ) ≤ T.length := T.positive;
        have _ : (1 : ℕ) ≤ A.length := A.positive;
        by
        have := GoldbergSeymour.TreeSequence.positive T
        have := GoldbergSeymour.TreeSequence.positive A
        omega);
    TreeSequenceInitialSegment base.core A →
    ∀ (hAib : A.length < (↑ib : ℕ)),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (↑ib : ℕ)
        (have this : (1 : ℕ) ≤ A.length := A.positive;
        have _ : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑ib : ℕ)) ↦ by omega)
        (have _ : (1 : ℕ) ≤ T.length := T.positive;
        have _ : (1 : ℕ) ≤ A.length := A.positive;
        by
        have := GoldbergSeymour.TreeSequence.positive T
        omega);
    ∀ (rpB : (1 : ℕ) ≤ ett.rounds)
      (aboveB :
        TreeSequenceInitialSegment
          (ett.series.data.tree
            (⟨ett.rounds,
                have _ : (1 : ℕ) ≤ T.length := T.positive;
                have _ : (1 : ℕ) ≤ A.length := A.positive;
                have _ : (1 : ℕ) ≤ Tn.length := Tn.positive;
                have _ : (1 : ℕ) ≤ Y.length := Y.positive;
                have _ : (1 : ℕ) ≤ B.length := B.positive;
                by
                have := GoldbergSeymour.TreeSequence.positive T
                omega⟩ :
              Fin (ett.rounds + (2 : ℕ))))
          B)
      (strictB :
        (ett.series.data.tree
              (⟨ett.rounds,
                  have _ : (1 : ℕ) ≤ T.length := T.positive;
                  have _ : (1 : ℕ) ≤ A.length := A.positive;
                  have _ : (1 : ℕ) ≤ Tn.length := Tn.positive;
                  have _ : (1 : ℕ) ≤ Y.length := Y.positive;
                  have _ : (1 : ℕ) ≤ B.length := B.positive;
                  by
                  have := GoldbergSeymour.TreeSequence.positive T
                  omega⟩ :
                Fin (ett.rounds + (2 : ℕ)))).length <
          B.length)
      (belowB :
        TreeSequenceInitialSegment B
          (ett.series.data.tree (Fin.last (ett.rounds + (1 : ℕ)))))
      (genB : phi = ett.series.data.coloring (Fin.last ett.rounds)),
    MaximumProperty
        { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
          abovePenultimate := aboveB, strictAbovePenultimate := strictB,
          belowFinal := belowB, generatingColoring := genB :
          ExtendedTashkinovTree G k e0 input B phi } →
    ∀
      (baseB :
        HierarchyBase
          { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          phi),
    baseB.core = base.core →
    ∀
      (HB :
        TashkinovHierarchy
          { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
            abovePenultimate := aboveB, strictAbovePenultimate := strictB,
            belowFinal := belowB, generatingColoring := genB :
            ExtendedTashkinovTree G k e0 input B phi }
          baseB),
    let ettB : ExtendedTashkinovTree G k e0 input B phi :=
      { rounds := ett.rounds, roundsPositive := rpB, series := ett.series,
        abovePenultimate := aboveB, strictAbovePenultimate := strictB, belowFinal := belowB,
        generatingColoring := genB : ExtendedTashkinovTree G k e0 input B phi };
    let sigma : PartialEdgeColoring E k :=
      TwoColorComponentSwap G phi alpha beta (Sum.inl vb);
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet A →
          ∀ (D : Finset (Fin k)), alpha ∉ D ∧ beta ∉ D → StableColoring S D phi sigma) →
    StableColoring Tn Dn phi sigma →
    TreeSequenceInitialSegment Tn B →
    Tn.length < B.length →
    (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn B ∨
        (ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = ({ f } : Finset E) ∧
              TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed B ∧
                  phi f ≠ some alpha ∧ phi f ≠ some beta) →
    (∀ (S : TreeSequence G e0),
        TashkinovAugmentationSequence phi S B → TashkinovAugmentationSequence sigma S B) →
    ∃ (corr : CorrespondingExtendedTashkinovTree G k e0 ettB sigma B),
    MaximumProperty corr.replacementETT ∧
    ∃ (baseS : HierarchyBase corr.replacementETT sigma) (HS :
      TashkinovHierarchy corr.replacementETT baseS),
    SameHierarchyStages HB HS := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower alpha beta H q A n Tn Dn ib
      vb ell yLength Y coreToA hAib B rpB aboveB strictB belowB genB hMPB baseB hcoreB HB ettB
      sigma sigmaProper sigmaOne stable stableTn TnToB TnStrictB terminalRoute routeTransport
  exact @helper_replacement_3311 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper)
      (@hone) (@hlower) (@alpha) (@beta) (@coreToA) (@hAib) (@rpB) (@aboveB) (@strictB)
      (@belowB) (@genB) (@hMPB) (@baseB) (@hcoreB) (@HB) (@sigmaProper) (@sigmaOne) (@stable)
      (@stableTn) (@TnToB) (@TnStrictB) (@terminalRoute) (@routeTransport)

end GoldbergSeymour.ChangeLemmaBothOutsidePreparation

end
