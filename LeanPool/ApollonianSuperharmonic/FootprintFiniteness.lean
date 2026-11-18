/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintInclusion

/-!
# FootprintFiniteness

Finiteness of the vertices, edges and boundary vertices of a finite lattice tile.
Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Every footprint edge belongs to one of finitely many constituent squares. -/
theorem FootprintEdges.finite (T : ProtoTile) : (FootprintEdges T).Finite := by
  classical
  let edges : Finset (Finset GaussianInt) := T.cells.biUnion fun x =>
    {{x, x + 1}, {x, x + ⟨0, 1⟩}, {x + 1, x + 1 + ⟨0, 1⟩},
      {x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩}}
  apply edges.finite_toSet.subset
  rintro e ⟨x, hx, he⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton] using he

/-- The footprint vertex set is finite, including the anchor of an empty tile. -/
theorem FootprintVertices.finite (T : ProtoTile) : (FootprintVertices T).Finite := by
  classical
  by_cases hne : T.cells.Nonempty
  · let vertices : Finset GaussianInt := T.cells.biUnion fun x =>
      {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩}
    have hvertices : (vertices : Set GaussianInt) = FootprintVertices T := by
      ext z
      simp [vertices, FootprintVertices, hne]
    rw [← hvertices]
    exact vertices.finite_toSet
  · simp [FootprintVertices, hne]

/-- Boundary footprint vertices form a finite subset of the footprint. -/
theorem BoundaryFootprintVertices.finite (T : ProtoTile) :
    (BoundaryFootprintVertices T).Finite :=
  (FootprintVertices.finite T).subset (BoundaryFootprintInclusion.boundaryVertex_mem T)

end ApollonianSuperharmonic

end
