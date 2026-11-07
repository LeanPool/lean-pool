/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

/-!
# Tree Facts for Certified Tashkinov Series

Shared facts from Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12, generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Consecutive noninitial stages of a certified series are nested tree sequences. -/
theorem TashkinovSeries.stepInitialSegment.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
    : TashkinovSeries G k rounds e0 input) (j : Fin (rounds + 1)) (i : Fin rounds), j = i.succ
    → TreeSequenceInitialSegment (series.data.tree i.succ.castSucc) (series.data.tree
    i.succ.succ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series j i hji
  cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero i) hji.symm |>.elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hji
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hji
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hji
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension


/-- Every positive certified stage extends the preceding tree. -/
theorem TashkinovSeries.positiveStepInitialSegment {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (index : Fin (rounds + 1)) (positive : 0 < index.val) :
    TreeSequenceInitialSegment (series.data.tree index.castSucc) (series.data.tree index.succ) := by
  let before : Fin rounds := ⟨index.val - 1, by omega⟩
  have next : before.succ = index := Fin.ext (by simp [before]; omega)
  have segment := TashkinovSeries.stepInitialSegment G k rounds e0 input series
    index before next.symm
  simpa only [next] using segment

/-- Ordered noninitial trees in a certified series are nested. -/
theorem TashkinovSeries.stageInitialSegmentOfLE {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
    (first last : Fin (rounds + 2)) (positive : 0 < first.val) (ordered : first ≤ last) :
    TreeSequenceInitialSegment (series.data.tree first) (series.data.tree last) := by
  have nested : ∀ last : Fin (rounds + 2), ∀ first, 0 < first.val → first ≤ last →
      TreeSequenceInitialSegment (series.data.tree first) (series.data.tree last) := by
    intro last
    induction last using Fin.induction with
    | zero =>
      intro first positive ordered
      change first.val ≤ 0 at ordered
      omega
    | succ index induction =>
      intro first positive ordered
      by_cases equal : first = index.succ
      · subst first
        exact TreeSequenceInitialSegment.refl _
      · have different : first.val ≠ index.val + 1 := fun same => equal (Fin.ext same)
        change first.val ≤ index.val + 1 at ordered
        have previous : first.val ≤ index.val := by omega
        exact (induction first positive (by change first.val ≤ index.val; exact previous)).trans
          (series.positiveStepInitialSegment index (by omega))
  exact nested last first positive ordered

end GoldbergSeymour

end
