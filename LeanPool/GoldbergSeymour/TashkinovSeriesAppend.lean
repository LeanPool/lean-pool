/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStepAppend

/-!
# Tashkinov Series Append

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovSeriesAppend {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (lastCertified : TashkinovSeriesStep G k (rounds + 1) e0 input
      (TashkinovSeriesDataAppend series.data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
      (Fin.last (rounds + 1))) :
    ∃ extended : TashkinovSeries G k (rounds + 1) e0 input,
      extended.data = TashkinovSeriesDataAppend series.data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex
        newOutsideVertex newDelta newGamma := by
  let appended := TashkinovSeriesDataAppend series.data newTree newColoring
    newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
    newDelta newGamma
  let extended : TashkinovSeries G k (rounds + 1) e0 input := {
    data := appended
    certified := by
      intro i
      refine Fin.lastCases lastCertified ?_ i
      intro oldIndex
      exact TashkinovSeriesStepAppend G k rounds e0 input series.data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma
        oldIndex (series.certified oldIndex)
  }
  exact ⟨extended, rfl⟩

end GoldbergSeymour

end
