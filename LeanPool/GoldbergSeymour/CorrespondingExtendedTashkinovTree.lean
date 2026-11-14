/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree

/-!
# Corresponding Extended Tashkinov Tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A replacement extended tree preserving ladder trees, stored colors and extension data under a
new coloring.
-/
structure CorrespondingExtendedTashkinovTree {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (base : ExtendedTashkinovTree G k e0 input T generating) (sigmaN : PartialEdgeColoring E k)
    (Tstar : TreeSequence G e0) where
  /-- Initial coloring for the replacement extension series. -/
  replacementInput : PartialEdgeColoring E k
  /-- Replacement series whose ladder and stored data agree with the original. -/
  replacementSeries : TashkinovSeries G k base.rounds e0 replacementInput
  /-- The extended tree presented by the replacement series. -/
  replacementETT : ExtendedTashkinovTree G k e0 replacementInput Tstar sigmaN
  rungAgreement : replacementETT.rounds = base.rounds
  seriesPresentation : HEq replacementETT.series replacementSeries
  finalGeneratingColoring : sigmaN = replacementSeries.data.coloring (Fin.last base.rounds)
  ladderTreesAgree :
    ∀ i : Fin base.rounds,
      replacementSeries.data.tree i.succ.castSucc = base.series.data.tree i.succ.castSucc
  storedColorsAgree :
    ∀ i : Fin (base.rounds + 1), replacementSeries.data.stored i = base.series.data.stored i
  connectingEdgesAgree :
    ∀ i : Fin (base.rounds + 1),
      replacementSeries.data.connectingEdges i = base.series.data.connectingEdges i
  extensionKindsAgree :
    ∀ i : Fin (base.rounds + 1), replacementSeries.data.kind i = base.series.data.kind i
  replacementProper :
    ∀ i : Fin (base.rounds + 1), IsProperEdgeColoring G (replacementSeries.data.coloring i)
  replacementOneUncolored :
    ∀ i : Fin (base.rounds + 1), IsOneEdgeUncolored (replacementSeries.data.coloring i) e0
  replacementStable :
    ∀ i : Fin base.rounds,
      StableColoring (base.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors base.series.data i.succ) (base.series.data.coloring i.succ)
        (replacementSeries.data.coloring i.succ)

end GoldbergSeymour

end
