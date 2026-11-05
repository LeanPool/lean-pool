/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint

public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAntitone

public import LeanPool.GoldbergSeymour.ParallelInterchangeability

public import LeanPool.GoldbergSeymour.OutsideExitTransport
public import LeanPool.GoldbergSeymour.PositivePrefixPresentation

/-!
# Step1Case One Inside Positive Divider

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma Step1CaseOneInsidePositiveDivider {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (q : ℕ) (_ : H.dividerCount < q)
    (_ : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < q →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (_ : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (_ : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (_ : beta ∈ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (hP₁ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (hpaths : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (ha : a₁ ≠ a₂) (_ : b₁ ≠ b₂)
    (horder : TreeVertexOrder T b₁ b₂)
    (f₁ f₂ : E)
    (_ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (_ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (_ : Incident G b₁ f₁) (_ : Incident G b₂ f₂)
    (_ : Sum.inr f₁ ∈ P₁.support)
    (_ : Sum.inr f₂ ∈ P₂.support)
    (hinside : b₂ ∈ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (theta : Fin k) (hthetaAlpha : theta ≠ alpha)
    (hthetaBeta : theta ≠ beta)
    (hthetaMissing : theta ∈ TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (hthetaClosedStar : TreeColorSetClosed G phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)) {theta})
    (hthetaClosed : TreeColorSetClosed G phi T {theta})
    (hnoSmaller :
      ∀ (sigma : PartialEdgeColoring E k) (T' : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T'),
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
          phi sigma →
        MaximumProperty corr.replacementETT →
        ∀ (base' : HierarchyBase corr.replacementETT sigma)
          (K : TashkinovHierarchy corr.replacementETT base')
          (good' : GoodHierarchy K),
          K.dividerCount < H.dividerCount →
          2 * corr.replacementETT.rounds + 11 ≤
            (TreeMissingColors sigma
              (corr.replacementETT.series.data.tree
                (Fin.last corr.replacementETT.rounds).castSucc)).card →
          TreeColorSetMinusClosed G sigma T'
            ((HierarchyTerminalStoredColors K).biUnion
              (good'.gamma (Fin.last K.dividerCount))) →
          ∀ (a b : Fin k), a ≠ b →
            a ∈ TreeMissingColors sigma T' →
            TreeColorSetClosed G sigma T' {a} →
            ∀ (u₁ v₁ u₂ v₂ : V)
              (Q₁ : (TwoColorIncidenceGraph G sigma a b).Walk
                (Sum.inl u₁) (Sum.inl v₁))
              (Q₂ : (TwoColorIncidenceGraph G sigma a b).Walk
                (Sum.inl u₂) (Sum.inl v₂)),
              TreeExitPath T' sigma a b u₁ v₁ Q₁ →
              TreeExitPath T' sigma a b u₂ v₂ Q₂ →
              (∀ x, x ∈ Q₁.support → x ∉ Q₂.support) →
              u₁ ≠ u₂ → False)
    (hdividerPositive : 0 < H.dividerCount) : False := by
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have starPositive : ∀ j : Fin (H.dividerCount + 1), 0 < j.val →
      HierarchyStarredStage H j = H.stage j.castSucc := by
    intro j
    refine Fin.cases ?_ ?_ j
    · intro hj
      simp at hj
    · intro i hj
      rfl
  let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
  have hstar : A = H.stage ⟨i.val + 1, by omega⟩ := by
    rw [show A = H.stage (Fin.last H.dividerCount).castSucc from
      starPositive _ (by simpa using hdividerPositive)]
    congr 1
    apply Fin.ext
    dsimp [i]
    omega
  have hAT : TreeSequenceInitialSegment A T := by
    rw [hstar, H.dividerStage i]
    exact ⟨_, fun j => rfl, fun j => rfl⟩
  have hA : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T :=
    TreeSequenceInitialSegmentVertexSetSubset hAT
  have hb₁A : b₁ ∈ TreeSequenceVertexSet A := by
    as_aux_lemma =>
    obtain ⟨r, s, hr, hs, hrs⟩ := horder
    obtain ⟨t, ht⟩ : ∃ t : Fin (A.length + 1), A.vertex t = b₂ := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
        using hinside
    have hst : s = Fin.castLE (Nat.succ_le_succ hAT.1) t :=
      T.vertex_injective (hs.trans ((hAT.2.1 t).trans ht).symm)
    have hrA : r.val < A.length + 1 := by
      have htlt := t.isLt
      have hval := congrArg Fin.val hst
      simp only [Fin.val_castLE] at hval
      omega
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨r.val, hrA⟩, ?_⟩
    exact (hAT.2.1 ⟨r.val, hrA⟩).symm.trans hr
  obtain ⟨sigma, recolor, proper, one, subsetData, outsideMissing, exitTransport⟩ :=
    P2716_T1_OutsideExitTransport G T phi alpha theta beta hthetaAlpha.symm
      hne hthetaBeta hproper hone hclosed hthetaClosed
  obtain ⟨Q₁, hQ₁, support₁, length₁⟩ :=
    exitTransport A hA a₁ b₁ P₁ hP₁ hb₁A
  obtain ⟨Q₂, hQ₂, support₂, length₂⟩ :=
    exitTransport A hA a₂ b₂ P₂ hP₂ hinside
  obtain ⟨corr, mp, basePrefix, K, goodPrefix, count, large, minus⟩ :=
    P2716_T1_PositivePrefixPresentation G k e0 input T phi sigma ett hMP
      hpositive hproper hone hlower base H good hlarge alpha theta recolor hdividerPositive
  have ladderInside : TreeSequenceVertexSet
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆ TreeSequenceVertexSet T :=
    TreeSequenceInitialSegmentVertexSetSubset ett.abovePenultimate
  have ladderStable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma :=
    (subsetData _ ladderInside).1 _
  have thetaMissing : theta ∈ TreeMissingColors sigma A := by
    rw [(subsetData A hA).2.1]
    exact hthetaMissing
  have thetaClosed : TreeColorSetClosed G sigma A {theta} :=
    (subsetData A hA).2.2 theta hthetaClosedStar
  have supports : ∀ x, x ∈ Q₁.support → x ∉ Q₂.support := by
    rw [support₁, support₂]
    exact hpaths
  exact hnoSmaller sigma A corr proper one ladderStable mp basePrefix K goodPrefix
    (by omega) large minus theta beta hthetaBeta thetaMissing thetaClosed
    a₁ b₁ a₂ b₂ Q₁ Q₂ hQ₁ hQ₂ supports ha

end GoldbergSeymour

end
