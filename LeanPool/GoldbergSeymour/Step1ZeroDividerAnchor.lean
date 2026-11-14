/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.Step1ZeroDividerAnchorNonPE
public import LeanPool.GoldbergSeymour.Step1ZeroDividerAnchorPE

/-!
# Step1Zero Divider Anchor

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma Step1ZeroDividerAnchor {V E : Type*}
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
    (H : TashkinovHierarchy ett base)
    (hdividerZero : H.dividerCount = 0)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (hclosed : TreeColorSetClosed G phi
      (HierarchyStarredStage H (Fin.last H.dividerCount)) {alpha})
    (a₁ b₁ a₂ b₂ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (hP₁ : TreeExitPath
      (HierarchyStarredStage H (Fin.last H.dividerCount))
      phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath
      (HierarchyStarredStage H (Fin.last H.dividerCount))
      phi alpha beta a₂ b₂ P₂)
    (hpaths : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (ha : a₁ ≠ a₂) : False := by
  by_cases hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE
  · exact Step1ZeroDividerAnchorPE G k e0 input T phi ett hMP hpositive
      hproper hone hlower base H hdividerZero alpha beta hne halpha hclosed
      a₁ b₁ a₂ b₂ P₁ P₂ hP₁ hP₂ hpaths ha hPE
  · exact Step1ZeroDividerAnchorNonPE G k e0 input T phi ett hMP hpositive
      hproper hone hlower base H hdividerZero alpha beta hne halpha hclosed
      a₁ b₁ a₂ b₂ P₁ P₂ hP₁ hP₂ hpaths ha hPE

end GoldbergSeymour

end
