/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.TashkinovSeriesData
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorCycle

/-!
# Revisiting Extension Certificate

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- An earlier parallel extension, a two-color cycle and a boundary-return path certifying a
revisiting extension.
-/
structure RevisitingExtensionCertificate {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} (data : TashkinovSeriesData G k rounds e0)
    (i : Fin (rounds + 1)) where
  /-- The earlier parallel-extension slot revisited by this certificate. -/
  earlier : Fin (rounds + 1)
  earlierPositive : 0 < earlier.val
  earlierAtMost : earlier.val ≤ i.val
  earlierPE : data.kind earlier = some TashkinovExtensionKind.PE
  interveningRevisiting :
    ∀ j : Fin (rounds + 1),
      0 < j.val → earlier.val < j.val → j.val ≤ i.val → data.kind j = some TashkinovExtensionKind.RE
  /-- The auxiliary color or color family used by this configuration. -/
  gamma : Fin k
  /-- The companion color used for the component swap at each stage. -/
  delta : Fin k
  earlierGamma : data.gamma earlier = some gamma
  earlierDelta : data.delta earlier = some delta
  /-- The two-color cycle witnessing the revisiting extension. -/
  cycle : TwoColorCycle G (data.coloring i) gamma delta
  meetsEarlier :
    ∃ v ∈ TreeSequenceVertexSet (data.tree earlier.castSucc), Sum.inl v ∈ cycle.walk.support
  leavesCurrent : ∃ u ∉ TreeSequenceVertexSet (data.tree i.succ), Sum.inl u ∈ cycle.walk.support
  /-- The selected edge, or ordered edges when the field is indexed. -/
  edge : E
  edgeOnCycle : Sum.inr edge ∈ cycle.walk.support
  edgeBoundary : edge ∈ BoundaryEdges G (TreeSequenceVertexSet (data.tree i.succ))
  /-- The chosen boundary-edge endpoint inside the current tree. -/
  insideEndpoint : V
  /-- The chosen boundary-edge endpoint outside the current tree. -/
  outsideEndpoint : V
  insideInCurrent : insideEndpoint ∈ TreeSequenceVertexSet (data.tree i.succ)
  outsideNotCurrent : outsideEndpoint ∉ TreeSequenceVertexSet (data.tree i.succ)
  edgeEnds : G.ends edge = s(insideEndpoint, outsideEndpoint)
  /-- The vertex of the earlier tree at which the return path begins. -/
  returnVertex : V
  returnInEarlier : returnVertex ∈ TreeSequenceVertexSet (data.tree earlier.castSucc)
  /-- The cycle-supported path from the earlier tree toward the boundary edge. -/
  returnPath :
    (TwoColorIncidenceGraph G (data.coloring i) gamma delta).Walk (Sum.inr edge)
      (Sum.inl returnVertex)
  returnPathIsPath : returnPath.IsPath
  returnPathOnCycle : ∀ z ∈ returnPath.support, z ∈ cycle.walk.support
  returnPathInternal :
    ∀ v, Sum.inl v ∈ returnPath.support → v ∈ TreeSequenceVertexSet (data.tree i.succ)

end GoldbergSeymour

end
