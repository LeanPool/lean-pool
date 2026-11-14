/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice

/-!
# Transport of maximum defective choices

Shared transports extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Transport a choice transparently to avoid repeated unfolding of its data projections. -/
abbrev MaximumDefectiveChoice.transport {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {T T' : TreeSequence G e0}
    {C C' : Finset (Fin k)} {phi phi' : PartialEdgeColoring E k}
    (choice : MaximumDefectiveChoice G e0 T C phi)
    (htree : T' = T) (hstored : C' = C) (hprev : phi' = phi) :
    MaximumDefectiveChoice G e0 T' C' phi' where
  selected := choice.selected
  selectedProper := choice.selectedProper
  selectedOneUncolored := choice.selectedOneUncolored
  selectedStable := by
    rw [htree, hstored, hprev]
    exact choice.selectedStable
  vertex := choice.vertex
  vertexDefective := by
    rw [htree]
    exact choice.vertexDefective
  maximal := by
    rw [htree, hstored, hprev]
    exact choice.maximal
  edge := choice.edge
  edgeDefective := by
    rw [htree]
    exact choice.edgeDefective
  edgeIncident := choice.edgeIncident
  otherEndpoint := choice.otherEndpoint
  otherOutside := by
    rw [htree]
    exact choice.otherOutside
  edgeEnds := choice.edgeEnds
  color := choice.color
  edgeColor := choice.edgeColor

end GoldbergSeymour

end
