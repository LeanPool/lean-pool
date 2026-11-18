/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesData

/-!
# Tashkinov Series Data Append

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Append one new tree, coloring and extension-witness entry to a series' data. -/
def TashkinovSeriesDataAppend {V E : Type*} {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0) (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k) (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E) (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V) (newDelta newGamma : Option (Fin k)) :
    TashkinovSeriesData G k (rounds + 1) e0 :=
  { tree := Fin.lastCases newTree data.tree
    coloring := Fin.lastCases newColoring data.coloring
    stored := Fin.lastCases newStored data.stored
    connectingEdges := Fin.lastCases newConnectingEdges data.connectingEdges
    kind := Fin.lastCases newKind data.kind
    chosenVertex := Fin.lastCases newChosenVertex data.chosenVertex
    outsideVertex := Fin.lastCases newOutsideVertex data.outsideVertex
    delta := Fin.lastCases newDelta data.delta
    gamma := Fin.lastCases newGamma data.gamma }

end GoldbergSeymour

end
