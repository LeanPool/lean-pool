/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceTransport
public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset

/-!
# Transporting closures under fixed incident colors

General structural facts extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Preserving incident colors and missing colors on a containing tree transports a closure. -/
theorem TashkinovClosure.transport_of_fixed {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {first second : PartialEdgeColoring E k} {source target containing : TreeSequence G e0}
    (fixedEdges : ∀ edge, TreeIncidentEdge containing edge → second edge = first edge)
    (fixedMissing : ∀ vertex ∈ TreeSequenceVertexSet containing,
      MissingColors G second vertex = MissingColors G first vertex)
    (contained : TreeSequenceVertexSet target ⊆ TreeSequenceVertexSet containing)
    (closure : TashkinovClosure first source target) : TashkinovClosure second source target := by
  classical
  have vertexMember (index : Fin (target.length + 1)) :
      target.vertex index ∈ TreeSequenceVertexSet containing :=
    contained (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)
  refine ⟨TashkinovAugmentationSequence.transport_of_fixed ?_ ?_ closure.1, ?_⟩
  · intro index
    obtain ⟨previous, attached⟩ := target.attaches index
    apply fixedEdges
    refine ⟨target.vertex index.succ, vertexMember _, ?_⟩
    change target.vertex index.succ ∈ G.ends (target.edge index)
    rw [attached]
    exact Sym2.mem_mk_left _ _
  · intro initial segment _ vertex member
    exact fixedMissing vertex (contained (TreeSequenceInitialSegmentVertexSetSubset segment member))
  · intro edge color vertex boundary member colored missing
    have ends := boundary
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at ends
    obtain ⟨inside, insideMember, outside, outsideMember, ends⟩ := ends
    have incident : TreeIncidentEdge containing edge := by
      refine ⟨inside, contained insideMember, ?_⟩
      change inside ∈ G.ends edge
      rw [ends]
      exact Sym2.mem_mk_left _ _
    apply closure.2 boundary member ((fixedEdges edge incident).symm.trans colored)
    rw [← fixedMissing vertex (contained member)]
    exact missing

end GoldbergSeymour

end
