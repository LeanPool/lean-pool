/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyReplacementPresentation
public import LeanPool.GoldbergSeymour.HierarchyCounterexamplePenultimateElementary
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength
public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix

/-!
# Replacement penultimate prefixes

Shared prefix-identification and elementarity facts extracted from the pinned Trellis proofs.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ReplacementPrefixes

/-- A replacement-prefix fact shared by the advancement and nonempty-tail arguments. -/
theorem penultimatePrefixEquality.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (ctx :
        HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ),
    let A : TreeSequence G e0 := HierarchyStarredStage C.hierarchy (Fin.last
        C.hierarchy.dividerCount); (
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyStarredStage R.counterexample.hierarchy (Fin.last
        R.counterexample.hierarchy.dividerCount) = A) → (3 : ℕ) ≤ T.length - A.length →
    ∀ (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ)) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    );
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - (1 :
        ℕ)) = B := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx i A starEq htail hlen B R
  have hn : min ((HierarchyStarredStage R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount)).length +
      (HierarchyFullTailLength R.counterexample - 1)) T.length = T.length - 1 := by
    unfold HierarchyFullTailLength
    dsimp only
    rw [starEq R]
    omega
  simp only [HierarchyFullTailPrefix, hn]
  rfl

/-- A replacement-prefix fact shared by the advancement and nonempty-tail arguments. -/
theorem penultimatePrefixElementary.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
      (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) (_ : ℕ)
      (hlen : (4 : ℕ) ≤ T.length),
    let B : TreeSequence G e0 :=
      TreeSequencePrefix T (T.length - (1 : ℕ))
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    (∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
        HierarchyFullTailPrefix R.counterexample
            (HierarchyFullTailLength R.counterexample - (1 : ℕ)) =
          B) →
    ∀ (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx),
    ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C ctx i hlen B fullB R
  have h : ColoredVertexSetElementary G R.coloring
    (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
      (HierarchyFullTailLength R.counterexample - 1))) := by
    exact HierarchyCounterexamplePenultimateElementary G k e0
      R.corresponding.replacementInput T R.coloring R.corresponding.replacementETT
      R.replacementBase R.counterexample R.minimumContext.proper
      R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
      R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
      R.minimumContext.largeMissingSet
  intro u hu v hv hne
  exact h (by rw [fullB R]; exact hu) (by rw [fullB R]; exact hv) hne

end GoldbergSeymour.SharedFacts.ReplacementPrefixes

end
