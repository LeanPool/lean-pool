/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.ChangeLemmaBothInside
public import LeanPool.GoldbergSeymour.ChangeLemmaBothOutside
public import LeanPool.GoldbergSeymour.ChangeLemmaInsideOutside

/-!
# Change Lemma

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ChangeLemma {V E : Type*}
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
                phi (T.edge t) = some c)) :
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
    let sameComponent := TwoColorComponent G phi alpha beta (Sum.inl va) =
      TwoColorComponent G phi alpha beta (Sum.inl vb)
    (0 < H.dividerCount ∧
        (alpha ∈ TreeMissingColors phi Tnq ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dnq) →
      sameComponent) ∧
    (H.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors phi Tn ∨
          Disjoint ({alpha, beta} : Finset (Fin k)) Dn) →
      sameComponent) ∧
    (alpha ∈ TreeMissingColors phi A ∧
        TreeColorSetClosed G phi A {alpha} →
      sameComponent ∧ TreeInterchangeable G A phi alpha beta) := by
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  have segmentTrans : ∀ X Y Z : TreeSequence G e0,
      TreeSequenceInitialSegment X Y → TreeSequenceInitialSegment Y Z →
        TreeSequenceInitialSegment X Z := by
    intro X Y Z hxy hyz
    rcases hxy with ⟨hxy, hvxy, hexy⟩
    rcases hyz with ⟨hyz, hvyz, heyz⟩
    have h : X.length ≤ Z.length := by omega
    refine ⟨h, ?_, ?_⟩
    · intro i
      have hi := hvyz (Fin.castLE (Nat.succ_le_succ hxy) i)
      have hj := hvxy i
      have he : Fin.castLE (Nat.succ_le_succ h) i =
          Fin.castLE (Nat.succ_le_succ hyz) (Fin.castLE (Nat.succ_le_succ hxy) i) := by
        apply Fin.ext
        rfl
      rw [he]
      exact hi.trans hj
    · intro i
      have hi := heyz (Fin.castLE hxy i)
      have hj := hexy i
      have he : Fin.castLE h i = Fin.castLE hyz (Fin.castLE hxy i) := by
        apply Fin.ext
        rfl
      rw [he]
      exact hi.trans hj
  have stageToEnd : ∀ i : Fin (H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage i.castSucc)
        (H.stage (Fin.last (H.dividerCount + 1))) := by
    have forward : ∀ i : Fin (H.dividerCount + 1), ∀ r : ℕ,
        ∀ hbound : i.val + r ≤ H.dividerCount + 1,
        TreeSequenceInitialSegment (H.stage i.castSucc)
          (H.stage ⟨i.val + r, by omega⟩) := by
      intro i r
      induction r with
      | zero =>
          intro h
          exact ⟨Nat.le_refl _, by intro j; rfl, by intro j; rfl⟩
      | succ r ih =>
          intro hbound
          let j : Fin (H.dividerCount + 1) := ⟨i.val + r, by omega⟩
          have hfirst := ih (by omega)
          have hstep := H.nested j
          have hmid : H.stage j.castSucc = H.stage ⟨i.val + r, by omega⟩ := by
            congr 1
          have hlast : H.stage j.succ =
              H.stage ⟨i.val + Nat.succ r, by omega⟩ := by
            apply congrArg H.stage
            apply Fin.ext
            rfl
          rw [← hmid] at hfirst
          rw [hlast] at hstep
          exact segmentTrans _ _ _ hfirst hstep
    intro i
    have hf := forward i (H.dividerCount + 1 - i.val) (by omega)
    simpa [Fin.last] using hf
  have hAsegment : TreeSequenceInitialSegment A T := by
    rw [show T = H.stage (Fin.last (H.dividerCount + 1)) from H.terminalStage.symm]
    by_cases hq : H.dividerCount = 0
    · have hA : A = base.core := by
        dsimp [A, q, HierarchyStarredStage]
        have hz : Fin.last H.dividerCount =
            (0 : Fin (H.dividerCount + 1)) := by
          apply Fin.ext
          simp [hq]
        rw [hz]
        rfl
      have hs : H.stage (Fin.last (H.dividerCount + 1)) = H.stage 1 := by
        apply congrArg H.stage
        apply Fin.ext
        simp [hq]
      simpa [hA, hs] using H.coreInsideFirst
    · have hs : A = H.stage q.castSucc := by
        have hqsucc : ∃ r : Fin H.dividerCount, q = r.succ := by
          refine ⟨⟨H.dividerCount - 1, by omega⟩, ?_⟩
          apply Fin.ext
          simp [q]
          omega
        rcases hqsucc with ⟨r, hr⟩
        change HierarchyStarredStage H q = H.stage q.castSucc
        rw [hr]
        dsimp [HierarchyStarredStage]
      rw [hs]
      exact stageToEnd q
  have missing_to_vertex :
    ∀ c : Fin k, c ∈ TreeMissingColors phi A → T.vertex (HierarchyFirstMissingPosition phi T c) ∈
        TreeSequenceVertexSet A := by
    intro c missing
    exact TreeSequenceFirstMissingVertexMemOfPrefix hAsegment missing
  have prefixClosed : ∀ u v : V, TreeVertexOrder T u v →
      v ∈ TreeSequenceVertexSet A → u ∈ TreeSequenceVertexSet A := by
    intro u v huv hv
    rcases huv with ⟨i, j, hi, hj, hij⟩
    unfold TreeSequenceVertexSet at hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨x, hx⟩
    rcases hAsegment with ⟨hlen, hvseg, heseg⟩
    have heq : T.vertex j = T.vertex (Fin.castLE (Nat.succ_le_succ hlen) x) := by
      exact hj.trans (hx.symm.trans (hvseg x).symm)
    have hijx := T.vertex_injective heq
    have hib : i.val ≤ A.length := by
      have : i.val < j.val := hij
      have : j.val = x.val := congrArg Fin.val hijx
      omega
    let y : Fin (A.length + 1) := ⟨i.val, Nat.lt_succ_of_le hib⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image]
    refine ⟨y, Finset.mem_univ _, ?_⟩
    have heqy : T.vertex (Fin.castLE (Nat.succ_le_succ hlen) y) = T.vertex i := by
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    rw [← hvseg y]
    exact heqy.symm.trans hi
  by_cases ha : T.vertex (HierarchyFirstMissingPosition phi T alpha) ∈
      TreeSequenceVertexSet A
  · by_cases hb : T.vertex (HierarchyFirstMissingPosition phi T beta) ∈
        TreeSequenceVertexSet A
    · exact ChangeLemmaBothInside G k e0 input T phi ett base C hproper hone
        hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
        hmissingPrefix horderedUnused ⟨ha, hb⟩
    · exact ChangeLemmaInsideOutside G k e0 input T phi ett base C hproper hone
        hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
        hmissingPrefix horderedUnused ⟨ha, hb⟩
  · by_cases hb : T.vertex (HierarchyFirstMissingPosition phi T beta) ∈
        TreeSequenceVertexSet A
    · have hna : alpha ∉ TreeMissingColors phi A := by
        intro h
        exact ha (missing_to_vertex alpha h)
      have ho := horderedUnused (Or.inl hna)
      exact (ha (prefixClosed _ _ ho.1 hb)).elim
    · have hmain := ChangeLemmaBothOutside G k e0 input T phi ett base C hproper hone
        hlower hfewer hminimal hprefixElementary hlarge alpha beta hne
        hmissingPrefix horderedUnused ⟨ha, hb⟩
      refine ⟨hmain.1, hmain.2, ?_⟩
      intro h
      exact (ha (missing_to_vertex alpha h.1)).elim

end GoldbergSeymour

end
