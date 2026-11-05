/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.OutsideExitTransport

public import LeanPool.GoldbergSeymour.Step1ZeroDividerAnchorNonPE

/-!
# Step1Case One Inside Zero Non PE

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma Step1CaseOneInsideZeroNonPE {V E : Type*}
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
    (_ : 2 * ett.rounds + 11 ≤
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
    (_ :
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
    (hdividerZero : H.dividerCount = 0)
    (hnonPE : ett.series.data.kind (Fin.last ett.rounds) ≠
      some TashkinovExtensionKind.PE) : False := by
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have hstar : A = base.core := by
    have hlast : Fin.last H.dividerCount =
        (0 : Fin (H.dividerCount + 1)) := by
      apply Fin.ext
      simp [hdividerZero]
    change HierarchyStarredStage H (Fin.last H.dividerCount) = base.core
    rw [hlast]
    rfl
  have hprefix : TreeSequenceInitialSegment A T := by
    rw [hstar, base.nonparallel hnonPE]
    exact ett.abovePenultimate
  have hsub : TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T :=
    TreeSequenceInitialSegmentVertexSetSubset hprefix
  have hb₁A : b₁ ∈ TreeSequenceVertexSet A := by
    obtain ⟨hlen, hvertices, _⟩ := hprefix
    obtain ⟨i, j, hi, hj, hij⟩ := horder
    obtain ⟨t, ht⟩ : ∃ t : Fin (A.length + 1), A.vertex t = b₂ := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and] using hinside
    have hjcast : j = Fin.castLE (Nat.succ_le_succ hlen) t :=
      T.vertex_injective (hj.trans ((hvertices t).trans ht).symm)
    have hiBound : i.val < A.length + 1 := by
      have hjval := congrArg Fin.val hjcast
      simp only [Fin.val_castLE] at hjval
      omega
    let iA : Fin (A.length + 1) := ⟨i.val, hiBound⟩
    have hiCast : Fin.castLE (Nat.succ_le_succ hlen) iA = i := by
      apply Fin.ext
      rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    refine ⟨iA, ?_⟩
    calc
      A.vertex iA = T.vertex (Fin.castLE (Nat.succ_le_succ hlen) iA) :=
        (hvertices iA).symm
      _ = T.vertex i := by rw [hiCast]
      _ = b₁ := hi
  obtain ⟨sigma, hrecolor, hproperSigma, honeSigma, hsubset, _, hexits⟩ :=
    P2716_T1_OutsideExitTransport G T phi alpha theta beta hthetaAlpha.symm
      hne hthetaBeta hproper hone hclosed hthetaClosed
  obtain ⟨Q₁, hQ₁, hsupport₁, _⟩ :=
    hexits A hsub a₁ b₁ P₁ hP₁ hb₁A
  obtain ⟨Q₂, hQ₂, hsupport₂, _⟩ :=
    hexits A hsub a₂ b₂ P₂ hP₂ hinside
  have hQpaths : ∀ x, x ∈ Q₁.support → x ∉ Q₂.support := by
    simpa only [hsupport₁, hsupport₂] using hpaths
  obtain ⟨_, _, _, _, corr, hMPsigma, baseSigma, K, goodSigma, hsame, _⟩ :=
    HierarchyLEMStable G k e0 input T phi sigma ett hMP hpositive hlower
      base H good hproper hone alpha theta hrecolor
  obtain ⟨hcores, hcounts, _, _, _, _⟩ := hsame.1
  have hKzero : K.dividerCount = 0 := hcounts.symm.trans hdividerZero
  have hKstar : HierarchyStarredStage K (Fin.last K.dividerCount) = A := by
    have hlast : Fin.last K.dividerCount =
        (0 : Fin (K.dividerCount + 1)) := by
      apply Fin.ext
      simp [hKzero]
    rw [hlast]
    exact hcores.symm.trans hstar.symm
  have hmissingSigma : theta ∈ TreeMissingColors sigma
      (HierarchyStarredStage K (Fin.last K.dividerCount)) := by
    rw [hKstar, (hsubset A hsub).2.1]
    exact hthetaMissing
  have hclosedSigma : TreeColorSetClosed G sigma
      (HierarchyStarredStage K (Fin.last K.dividerCount)) {theta} := by
    rw [hKstar]
    exact (hsubset A hsub).2.2 theta hthetaClosedStar
  have lastKindAgreement :
    ∀ {m n : ℕ} (S₁ : TashkinovSeries G k m e0 corr.replacementInput) (S₂ : TashkinovSeries G k n
        e0 corr.replacementInput), m = n → HEq S₁ S₂ → S₁.data.kind (Fin.last m) = S₂.data.kind
        (Fin.last n) := by
    intro m n S₁ S₂ hmn hseries
    cases hmn
    cases hseries
    rfl
  have hkind : corr.replacementETT.series.data.kind
      (Fin.last corr.replacementETT.rounds) =
      ett.series.data.kind (Fin.last ett.rounds) :=
    (lastKindAgreement corr.replacementETT.series corr.replacementSeries
      corr.rungAgreement corr.seriesPresentation).trans
      (corr.extensionKindsAgree (Fin.last ett.rounds))
  have hnonSigma : corr.replacementETT.series.data.kind
      (Fin.last corr.replacementETT.rounds) ≠
      some TashkinovExtensionKind.PE := by
    rw [hkind]
    exact hnonPE
  exact Step1ZeroDividerAnchorNonPE G k e0 corr.replacementInput T sigma
    corr.replacementETT hMPsigma
    (by simpa only [corr.rungAgreement] using hpositive)
    hproperSigma honeSigma
    (fun lower hp hlt hmp => hlower lower hp
      (by simpa only [corr.rungAgreement] using hlt) hmp)
    baseSigma K hKzero theta beta hthetaBeta hmissingSigma hclosedSigma
    a₁ b₁ a₂ b₂ Q₁ Q₂
    (by simpa only [hKstar] using hQ₁)
    (by simpa only [hKstar] using hQ₂) hQpaths ha hnonSigma

end GoldbergSeymour

end
