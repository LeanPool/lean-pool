/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Step1CaseTwoInsidePositiveDivider
public import LeanPool.GoldbergSeymour.Step1CaseTwoInsideZeroNonPE
public import LeanPool.GoldbergSeymour.Step1CaseTwoInsideZeroPE

/-!
# Step1Case Two Inside Star

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma Step1CaseTwoInsideStar {V E : Type*}
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
    (q : ℕ) (hdivider : H.dividerCount < q)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
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
    (hterminal : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (halpha : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (hbeta : beta ∉ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ a₃ b₃ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₃) (Sum.inl b₃))
    (hP₁ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (hP₃ : TreeExitPath T phi alpha beta a₃ b₃ P₃)
    (hpaths₁₂ : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (hpaths₁₃ : ∀ x, x ∈ P₁.support → x ∉ P₃.support)
    (hpaths₂₃ : ∀ x, x ∈ P₂.support → x ∉ P₃.support)
    (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃) (ha₂₃ : a₂ ≠ a₃)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    (horder₁₂ : TreeVertexOrder T b₁ b₂)
    (horder₂₃ : TreeVertexOrder T b₂ b₃)
    (f₁ f₂ f₃ : E)
    (hf₁ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₃ : f₃ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hif₁ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (hif₃ : Incident G b₃ f₃)
    (hPf₁ : Sum.inr f₁ ∈ P₁.support)
    (hPf₂ : Sum.inr f₂ ∈ P₂.support)
    (hPf₃ : Sum.inr f₃ ∈ P₃.support)
    (hinside : b₃ ∈ TreeSequenceVertexSet
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
              u₁ ≠ u₂ → False) : False := by
  by_cases hpos : 0 < H.dividerCount
  · exact Step1CaseTwoInsidePositiveDivider G k e0 input T phi ett hMP hpositive
      hproper hone hlower base H good q hdivider hfewer hlarge hterminal
      hElementary alpha beta halpha hclosed hne hbeta a₁ b₁ a₂ b₂ a₃ b₃
      P₁ P₂ P₃ hP₁ hP₂ hP₃ hpaths₁₂ hpaths₁₃ hpaths₂₃ ha₁₂ ha₁₃ ha₂₃
      hb₁₂ hb₁₃ hb₂₃ horder₁₂ horder₂₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ hif₁ hif₂
      hif₃ hPf₁ hPf₂ hPf₃ hinside theta hthetaAlpha hthetaBeta
      hthetaMissing hthetaClosedStar hthetaClosed hnoSmaller hpos
  · have hzero : H.dividerCount = 0 := Nat.eq_zero_of_not_pos hpos
    by_cases hpe : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · exact Step1CaseTwoInsideZeroPE G k e0 input T phi ett hMP hpositive
        hproper hone hlower base H good q hdivider hfewer hlarge hterminal
        hElementary alpha beta halpha hclosed hne hbeta a₁ b₁ a₂ b₂ a₃ b₃
        P₁ P₂ P₃ hP₁ hP₂ hP₃ hpaths₁₂ hpaths₁₃ hpaths₂₃ ha₁₂ ha₁₃ ha₂₃
        hb₁₂ hb₁₃ hb₂₃ horder₁₂ horder₂₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ hif₁ hif₂
        hif₃ hPf₁ hPf₂ hPf₃ hinside theta hthetaAlpha hthetaBeta
        hthetaMissing hthetaClosedStar hthetaClosed hnoSmaller hzero hpe
    · exact Step1CaseTwoInsideZeroNonPE G k e0 input T phi ett hMP hpositive
        hproper hone hlower base H good q hdivider hfewer hlarge hterminal
        hElementary alpha beta halpha hclosed hne hbeta a₁ b₁ a₂ b₂ a₃ b₃
        P₁ P₂ P₃ hP₁ hP₂ hP₃ hpaths₁₂ hpaths₁₃ hpaths₂₃ ha₁₂ ha₁₃ ha₂₃
        hb₁₂ hb₁₃ hb₂₃ horder₁₂ horder₂₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ hif₁ hif₂
        hif₃ hPf₁ hPf₂ hPf₃ hinside theta hthetaAlpha hthetaBeta
        hthetaMissing hthetaClosedStar hthetaClosed hnoSmaller hzero hpe

end GoldbergSeymour

end
