/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.StableChangeCaseThree.Preparation5
public import LeanPool.GoldbergSeymour.HierarchyWeaklyStable
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength

/-!
# Stable Change Case Three

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open StableChangeCaseThreePreparation

theorem StableChangeCaseThree {V E : Type*}
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
    (hprefixElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      alpha ∈ TreeMissingColors phi
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) ∧
      beta ∈ TreeMissingColors phi
        (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)))
    (z : Sum V E) (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hAprecedes : ∀ u ∈ TreeSequenceVertexSet
        (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)),
      TreeVertexOrder T u (T.vertex (HierarchyFirstMissingPosition phi T alpha)))
    (hordered : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition phi T alpha))
      (T.vertex (HierarchyFirstMissingPosition phi T beta)))
    (hnotStored :
      alpha ∉ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount) ∧
      beta ∉ HierarchyStoredColorsAt C.hierarchy (Fin.last C.hierarchy.dividerCount))
    (hunused : alpha ∉ (Finset.univ.filter fun c =>
      ∃ t : Fin T.length,
        (HierarchyFirstMissingPosition phi T alpha).val ≤ t.val ∧
        t.val < (HierarchyFirstMissingPosition phi T beta).val ∧
        phi (T.edge t) = some c)) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dnq := HierarchyStoredColorsAt H q
    HierarchyWeaklyStable H q sigma ∧
      ModColoring ett sigma ∧
      (A = Tn ∨
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            MaximumProperty ettA) ∧
      (∀ hq : 0 < H.dividerCount,
        ∃ inputA : PartialEdgeColoring E k,
          ∃ ettA : ExtendedTashkinovTree G k e0 inputA A sigma,
            ∃ baseA : HierarchyBase ettA sigma,
              ∃ K : TashkinovHierarchy ettA baseA,
                ∃ goodA : GoodHierarchy K,
                  MaximumProperty ettA ∧
                    ∃ hcount : K.dividerCount + 1 = H.dividerCount,
                      baseA.core = base.core ∧
                      baseA.closure = base.closure ∧
                      (∀ j : Fin (K.dividerCount + 2),
                        K.stage j = H.stage ⟨j.val, by omega⟩) ∧
                      (∀ j : Fin (K.dividerCount + 1),
                        let jH : Fin (H.dividerCount + 1) :=
                          ⟨j.val, by omega⟩
                        HierarchyStoredColorsAt K j =
                            HierarchyStoredColorsAt H jH ∧
                          ∀ eta ∈ HierarchyStoredColorsAt K j,
                            goodA.gamma j eta = C.good.gamma jH eta) ∧
                      TreeColorSetMinusClosed G sigma Tnq
                        (Dnq.biUnion
                          (C.good.gamma ⟨C.hierarchy.dividerCount - 1,
                            by omega⟩))) ∧
      (∃ corrT : CorrespondingExtendedTashkinovTree
            G k e0 ett sigma T,
          MaximumProperty corrT.replacementETT ∧
            ∃ baseT : HierarchyBase corrT.replacementETT sigma,
              ∃ K : TashkinovHierarchy corrT.replacementETT baseT,
                ∃ goodT : GoodHierarchy K,
                  SameGoodHierarchy C.good goodT) := by
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
  let Y := TreeSequencePrefix T (min (A.length + (ell - 1)) T.length)
    (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (Nat.min_le_right _ _)
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    apply helper_segTrans_511 <;> assumption
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hlen : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    apply helper_commonPrefix_520 <;> assumption
  have stageSegment (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1) :
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    induction d with
    | zero => simpa using segRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      exact segTrans (ih (by omega)) (H.nested ⟨a + d, by omega⟩)
  have equalTrees {S U : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U) (hlen : S.length = U.length) : S = U := by
    apply helper_equalTrees_536 <;> assumption
  have stageToT (j : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage j) T := by
    apply helper_stageToT_552; assumption
  have lastZero (hz : H.dividerCount = 0) : A = base.core := by
    simp [A, q, HierarchyStarredStage, hz, Fin.last]
  have lastPositive (hz : H.dividerCount ≠ 0) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    apply helper_lastPositive_561; assumption
  have coreToA : TreeSequenceInitialSegment base.core A := by
    apply helper_coreToA_572 <;> assumption
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (Classical.choice (base.parallel hp).2.2).leftSegment
    · rw [base.nonparallel hp]; exact segRefl _
  have TnToA := segTrans TnToCore coreToA
  have AToT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · rw [lastZero hz]
      exact segTrans H.coreInsideFirst (stageToT ⟨1, by omega⟩)
    · rw [lastPositive hz]; exact stageToT _
  have ordinaryToA (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) A := by
    apply helper_ordinaryToA_589 <;> assumption
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
    apply helper_firstMissing_607 <;> assumption
  have firstLe (c : Fin k) (i : Fin (T.length + 1))
      (hc : c ∈ MissingColors G phi (T.vertex i)) :
      (HierarchyFirstMissingPosition phi T c).val ≤ i.val := by
    apply helper_firstLe_627; assumption
  have ha := firstMissing alpha hmissingY.1
  have hb := firstMissing beta hmissingY.2
  have habIndex : ia.val < ib.val := by
    obtain ⟨i, j, hi, hj, hij⟩ := hordered
    have hei := T.vertex_injective hi
    have hej := T.vertex_injective hj
    simpa [ia, ib, hei, hej] using hij
  have hout : va ∉ TreeSequenceVertexSet A ∧ vb ∉ TreeSequenceVertexSet A := by
    apply helper_hout_642 <;> assumption
  have outsideIndex (i : Fin (T.length + 1))
      (hi : T.vertex i ∉ TreeSequenceVertexSet A) : A.length < i.val := by
    apply helper_outsideIndex_658 <;> assumption
  have hAia := outsideIndex ia hout.1
  have hAib := outsideIndex ib hout.2
  have AToY : TreeSequenceInitialSegment A Y := commonPrefix AToT YToT (by omega)
  have vertexY (i : Fin (T.length + 1)) (hi : i.val ≤ Y.length) :
      T.vertex i ∈ TreeSequenceVertexSet Y := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i.val, by omega⟩, rfl⟩
  have haY : va ∈ TreeSequenceVertexSet Y := vertexY ia ha.2
  have hbY : vb ∈ TreeSequenceVertexSet Y := vertexY ib hb.2
  have missingNotA (c : Fin k) (i : Fin (T.length + 1))
      (hmi : c ∈ MissingColors G phi (T.vertex i))
      (hiy : T.vertex i ∈ TreeSequenceVertexSet Y)
      (hia : T.vertex i ∉ TreeSequenceVertexSet A) : c ∉ TreeMissingColors phi A := by
    apply helper_missingNotA_674 <;> assumption
  have halphaA : alpha ∉ TreeMissingColors phi A := missingNotA alpha ia ha.1 haY hout.1
  have hbetaA : beta ∉ TreeMissingColors phi A := missingNotA beta ib hb.1 hbY hout.2
  have missingSubset {S U : TreeSequence G e0} (hSU : TreeSequenceInitialSegment S U) :
      TreeMissingColors phi S ⊆ TreeMissingColors phi U := by
    intro c hc
    obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hSU hv, hcv⟩
  have hDn : alpha ∉ Dn ∧ beta ∉ Dn := by
    apply helper_hDn_690 <;> assumption
  have notControlled (c : Fin k) (hc : c = alpha ∨ c = beta) :
      c ∉ TreeMissingColors phi Tn ∪ Dn := by
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases hc with rfl | rfl
      · exact halphaA (missingSubset TnToA hm)
      · exact hbetaA (missingSubset TnToA hm)
    · rcases hc with rfl | rfl
      · exact hDn.1 hm
      · exact hDn.2 hm
  have storedOrMissing (c : Fin k) (hc : c ∈ ett.series.data.stored n) :
      c ∈ TreeMissingColors phi Tn ∪ Dn := by
    apply helper_storedOrMissing_706 <;> assumption
  -- The route includes the actual connecting seed, not merely a vertex-set extension.
  have terminalRoute :
      (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence phi Tn T) ∨
      ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges n = {f} ∧ TreeSequenceAdjoinEdge Tn f seed ∧
          TashkinovAugmentationSequence phi seed T ∧
          phi f ≠ some alpha ∧ phi f ≠ some beta) := by
    apply helper_terminalRoute_392 <;> assumption
  have treeControlled (t : Fin Tn.length) :
      phi (Tn.edge t) ≠ some alpha ∧ phi (Tn.edge t) ≠ some beta := by
    apply helper_treeControlled_729 <;> assumption
  have augmentationControlled (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S T) (t : Fin T.length)
      (ht : S.length ≤ t.val) (htb : t.val < ib.val) :
      phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta := by
    apply helper_augmentationControlled_748 <;> assumption
  have prefixControlled (t : Fin T.length) (htb : t.val < ib.val) :
      phi (T.edge t) ≠ some alpha ∧ phi (T.edge t) ≠ some beta := by
    apply helper_prefixControlled_781 <;> assumption
  have horderedUnused :
      (alpha ∉ TreeMissingColors phi A ∨ beta ∉ TreeMissingColors phi A) →
        TreeVertexOrder T va vb ∧ alpha ∉ (Finset.univ.filter fun c =>
          ∃ t : Fin T.length, A.length ≤ t.val ∧ t.val < ib.val ∧
            phi (T.edge t) = some c) := by
    apply helper_horderedUnused_800 <;> assumption
  apply helper_continuation_3662 <;> assumption
end GoldbergSeymour

end
