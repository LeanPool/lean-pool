/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableChangeCasesOneTwo
public import LeanPool.GoldbergSeymour.StableChangeCaseThree

/-!
# Stable Change

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem StableChange {V E : Type*}
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
    (z : Sum V E) (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hcase :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      let Dnq := HierarchyStoredColorsAt H q
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      let vb := T.vertex (HierarchyFirstMissingPosition phi T beta)
      let ia := HierarchyFirstMissingPosition phi T alpha
      let ib := HierarchyFirstMissingPosition phi T beta
      (0 < H.dividerCount ∧
          alpha ∈ TreeMissingColors phi Tnq ∧
          TwoColorPathComponent G phi alpha beta z ∧
          Disjoint (TwoColorComponent G phi alpha beta z)
            (TwoColorComponent G phi alpha beta (Sum.inl va))) ∨
        (H.dividerCount = 0 ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            (alpha ∈ TreeMissingColors phi A ∧
              alpha ∉ Dn ∧ beta ∉ Dn)) ∧
          TwoColorPathComponent G phi alpha beta z ∧
          Disjoint (TwoColorComponent G phi alpha beta z)
            (TwoColorComponent G phi alpha beta (Sum.inl va))) ∨
        ((∀ u ∈ TreeSequenceVertexSet A, TreeVertexOrder T u va) ∧
          TreeVertexOrder T va vb ∧
          alpha ∉ Dnq ∧ beta ∉ Dnq ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              ia.val ≤ t.val ∧ t.val < ib.val ∧
                phi (T.edge t) = some c))) :
    let H := C.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let A := HierarchyStarredStage H q
    let Tnq := H.stage ⟨H.dividerCount, by omega⟩
    let Tn := ett.series.data.tree n.castSucc
    let Dnq := HierarchyStoredColorsAt H q
    let ia := HierarchyFirstMissingPosition phi T alpha
    let ib := HierarchyFirstMissingPosition phi T beta
    (HierarchyWeaklyStable H q sigma ∧
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
                            by omega⟩)))) ∧
      (((∀ u ∈ TreeSequenceVertexSet A, TreeVertexOrder T u
              (T.vertex (HierarchyFirstMissingPosition phi T alpha))) ∧
          TreeVertexOrder T
            (T.vertex (HierarchyFirstMissingPosition phi T alpha))
            (T.vertex (HierarchyFirstMissingPosition phi T beta)) ∧
          alpha ∉ Dnq ∧ beta ∉ Dnq ∧
          alpha ∉ (Finset.univ.filter fun c =>
            ∃ t : Fin T.length,
              ia.val ≤ t.val ∧ t.val < ib.val ∧
                phi (T.edge t) = some c)) →
        ∃ corrT : CorrespondingExtendedTashkinovTree
            G k e0 ett sigma T,
          MaximumProperty corrT.replacementETT ∧
            ∃ baseT : HierarchyBase corrT.replacementETT sigma,
              ∃ K : TashkinovHierarchy corrT.replacementETT baseT,
                ∃ goodT : GoodHierarchy K,
                  SameGoodHierarchy C.good goodT) := by
  dsimp only at hcase ⊢
  constructor
  · rcases hcase with h1 | h2 | h3
    · have hresult := StableChangeCasesOneTwo G k e0 input T phi ett base C
          hproper hone hlower hfewer hminimal hprefixElementary hlarge alpha
          beta hne hmissingPrefix z h1.2.2.1 sigma hsigma
          (Or.inl ⟨h1.1, h1.2.1⟩) h1.2.2.2
      refine ⟨hresult.1, hresult.2.1, hresult.2.2.1, ?_⟩
      intro hq
      rcases hresult.2.2.2 hq with
        ⟨inputA, ettA, baseA, K, goodA, hmax, _hkind, ⟨hcount, hrest⟩⟩
      exact ⟨inputA, ettA, baseA, K, goodA, hmax, hcount, hrest⟩
    · have hresult := StableChangeCasesOneTwo G k e0 input T phi ett base C
          hproper hone hlower hfewer hminimal hprefixElementary hlarge alpha
          beta hne hmissingPrefix z h2.2.2.1 sigma hsigma
          (Or.inr ⟨h2.1, h2.2.1⟩) h2.2.2.2
      refine ⟨hresult.1, hresult.2.1, hresult.2.2.1, ?_⟩
      intro hq
      rcases hresult.2.2.2 hq with
        ⟨inputA, ettA, baseA, K, goodA, hmax, _hkind, ⟨hcount, hrest⟩⟩
      exact ⟨inputA, ettA, baseA, K, goodA, hmax, hcount, hrest⟩
    · have hresult := StableChangeCaseThree G k e0 input T phi ett base C
          hproper hone hlower hfewer hminimal hprefixElementary hlarge
          alpha beta hne hmissingPrefix z sigma hsigma h3.1 h3.2.1
          ⟨h3.2.2.1, h3.2.2.2.1⟩ h3.2.2.2.2
      exact ⟨hresult.1, hresult.2.1, hresult.2.2.1,
        hresult.2.2.2.1⟩
  · intro h3
    have hresult := StableChangeCaseThree G k e0 input T phi ett base C
      hproper hone hlower hfewer hminimal hprefixElementary hlarge alpha beta
      hne hmissingPrefix z sigma hsigma h3.1 h3.2.1
      ⟨h3.2.2.1, h3.2.2.2.1⟩ h3.2.2.2.2
    exact hresult.2.2.2.2

end GoldbergSeymour

end
