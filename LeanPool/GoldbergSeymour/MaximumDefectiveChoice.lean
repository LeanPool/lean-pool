/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DefectiveVertex
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.StableColoring
public import LeanPool.GoldbergSeymour.TreeVertexOrder

/-!
# Maximum Defective Choice

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/--
A stable coloring with a latest possible defective vertex and a chosen incident defective edge. -/
structure MaximumDefectiveChoice {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E)
    {k : ℕ} (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi : PartialEdgeColoring E k) where
  /-- The chosen stable coloring. -/
  selected : PartialEdgeColoring E k
  selectedProper : IsProperEdgeColoring G selected
  selectedOneUncolored : IsOneEdgeUncolored selected e0
  selectedStable : StableColoring T C phi selected
  /-- The selected vertex, or ordered vertices when the field is indexed. -/
  vertex : V
  vertexDefective : DefectiveVertex G selected (TreeSequenceVertexSet T) vertex
  maximal :
    ∀ (pi : PartialEdgeColoring E k) (w : V), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0
        → StableColoring T C phi pi → DefectiveVertex G pi (TreeSequenceVertexSet T) w → w =
        vertex ∨ TreeVertexOrder T w vertex
  /-- The selected edge, or ordered edges when the field is indexed. -/
  edge : E
  edgeDefective : DefectiveEdge G selected (TreeSequenceVertexSet T) edge
  edgeIncident : Incident G vertex edge
  /-- The endpoint of the selected defective edge lying outside the tree. -/
  otherEndpoint : V
  otherOutside : otherEndpoint ∉ TreeSequenceVertexSet T
  edgeEnds : G.ends edge = s(vertex, otherEndpoint)
  /-- The assigned color of the selected defective edge. -/
  color : Fin k
  edgeColor : selected edge = some color

end GoldbergSeymour

end
