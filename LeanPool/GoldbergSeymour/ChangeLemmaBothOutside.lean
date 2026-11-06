/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChangeLemmaBothOutside.Preparation6
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleLess
public import LeanPool.GoldbergSeymour.HierarchyCounterexampleMeasure
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Change Lemma Both Outside

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open ChangeLemmaBothOutsidePreparation

theorem ChangeLemmaBothOutside {V E : Type*}
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
    (_ : ∀ {input' : PartialEdgeColoring E k}
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
    (_ :
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
      va ∉ TreeSequenceVertexSet A ∧
        vb ∉ TreeSequenceVertexSet A) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let _ := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    let Dnq := HierarchyStoredColorsAt H q
    let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
    let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
    let sameComponent := TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb)
    (0 < H.dividerCount ∧
        (alpha ∈ TreeMissingColors phi Tnq ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dnq) →
      sameComponent) ∧
    (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors phi Tn ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dn) →
      sameComponent) := by
  classical
  let H := C.hierarchy
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
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    exact @helper_segTrans_973 (@V) (@E) (@G) (@e0) (@S) (@U) (@W) (@hSU) (@hUW)
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    exact @helper_commonPrefix_982 (@V) (@E) (@G) (@e0) (@S) (@U) (@W) (@hSW) (@hUW) (@hlen)
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    induction d with
    | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    exact @helper_stageToT_998 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@stageSegment) (@j)
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    simp [A, q, HierarchyStarredStage, hz, Fin.last]
  have lastPositive (hz : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    exact @helper_lastPositive_1007 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hz)
  have coreToA : TreeSequenceInitialSegment base.core A := by
    exact @helper_coreToA_1018 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@segRefl) (@segTrans)
        (@stageSegment) (@lastZero) (@lastPositive)
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (Classical.choice (base.parallel hp).2.2).leftSegment
    · rw [base.nonparallel hp]
      exact segRefl _
  have TnToA := segTrans TnToCore coreToA
  have AToT : TreeSequenceInitialSegment A T := by
    exact @helper_AToT_1032 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@segTrans) (@stageToT)
        (@lastZero) (@lastPositive)
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    exact @helper_ordinaryToA_1038 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@stageSegment)
        (@lastPositive) (@TnToA) (@j)
  have starredToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) A := by
    exact Fin.cases coreToA (fun i => ordinaryToA i.succ) j
  have YToT : TreeSequenceInitialSegment Y T :=
    ⟨Nat.min_le_right _ _, (by intro i; rfl), (by intro i; rfl)⟩
  have hmissingY : alpha ∈ TreeMissingColors phi Y ∧ beta ∈ TreeMissingColors phi Y :=
    hmissingPrefix
  have hElementaryY : ColoredVertexSetElementary G phi (TreeSequenceVertexSet Y) :=
    hprefixElementary
  have firstMissing (c : Fin k) (hc : c ∈ TreeMissingColors phi Y) :
      c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) ∧
        (HierarchyFirstMissingPosition phi T c).val ≤ Y.length := by
    exact @SharedFacts.MixedChangeTransport.firstMissingPositionWitness (@V) (@E) inferInstance
        inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@YToT) (@c) (@hc)
  have ha := firstMissing alpha hmissingY.1
  have hb := firstMissing beta hmissingY.2
  have vertexY (i : Fin (T.length + 1)) (hi : i.val ≤ Y.length) :
      T.vertex i ∈ TreeSequenceVertexSet Y := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haY : va ∈ TreeSequenceVertexSet Y := vertexY ia ha.2
  have hbY : vb ∈ TreeSequenceVertexSet Y := vertexY ib hb.2
  have hout : va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A := hlocation
  have outsideIndex (i : Fin (T.length + 1))
      (hi : T.vertex i ∉ TreeSequenceVertexSet A) : A.length < i.val := by
    exact @helper_outsideIndex_1087 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@AToT) (@i) (@hi)
  have hAia := outsideIndex ia hout.1
  have hAib := outsideIndex ib hout.2
  have AToY : TreeSequenceInitialSegment A Y :=
    commonPrefix AToT YToT (by omega)
  have missingNotA (c : Fin k) (i : Fin (T.length + 1))
      (hmi : c ∈ MissingColors G phi (T.vertex i))
      (hiy : T.vertex i ∈ TreeSequenceVertexSet Y)
      (hia : T.vertex i ∉ TreeSequenceVertexSet A) : c ∉ TreeMissingColors phi A := by
    exact @helper_missingNotA_1098 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
        (@hne) (@hElementaryY) (@AToY) (@c) (@i) (@hmi) (@hiy) (@hia)
  exact @helper_continuation_4272 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@hminimal) (@alpha) (@beta) (@hne) (@hmissingPrefix) (@horderedUnused)
      (@hlocation) (@segRefl) (@segTrans) (@commonPrefix) (@lastPositive) (@coreToA) (@TnToA)
      (@AToT) (@ordinaryToA) (@starredToA) (@YToT) (@hmissingY) (@hElementaryY) (@ha) (@hb)
      (@vertexY) (@haY) (@hbY) (@hout) (@hAia) (@hAib) (@missingNotA)
end GoldbergSeymour

end
