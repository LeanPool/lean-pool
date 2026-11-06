/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries

/-!
# Shared facts for HkuUnsupportedVertexColors

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.UnsupportedVertexColors

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev nextSegmentStatement.{u_1, u_2} : Prop :=
  open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
      PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input) (j : Fin (rounds +
      (1 : ℕ))) (i : Fin rounds), j = i.succ → TreeSequenceInitialSegment (series.data.tree
      i.succ.castSucc) (series.data.tree i.succ.succ)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem next_segment.{u_1, u_2} : nextSegmentStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k rounds e0 input series j i hj
  cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero i) hj.symm |>.elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hj
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hj
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
    have hvals := congrArg Fin.val hj
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    exact orderedExtension

end GoldbergSeymour.SharedFacts.UnsupportedVertexColors

end
