/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary
public import Mathlib.Init


/-!
# InteriorFootprintIncidence

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace InteriorFootprintIncidence

/-- Shared nonempty identity for InteriorFootprintIncidence. -/
theorem nonempty :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ FootprintVertices T) → ((x ∉
            BoundaryFootprintVertices T) → (T.cells.Nonempty)) ) := by
  classical
  intro T x hx hxb
  by_contra hn
  simp only [FootprintVertices, ite_eq_right hn, Set.mem_singleton_iff] at hx
  apply hxb
  simp [BoundaryFootprintVertices, hn, hx]

/-- Shared someIncidentCell identity for InteriorFootprintIncidence. -/
theorem someIncidentCell :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ FootprintVertices T) → ((x ∉
            BoundaryFootprintVertices T) → ((T.cells.Nonempty) → (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T.cells))) ) := by
  classical
  intro T x hx hxb hne
  rw [FootprintVertices, ite_eq_left hne] at hx
  rcases hx with ⟨y, hy, rfl | rfl | rfl | rfl⟩
  · exact ⟨0, by simpa [LatticeVertexIncidentCell] using hy⟩
  · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hy⟩
  · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hy⟩
  · refine ⟨2, ?_⟩
    simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using hy

/-- Shared allIncidentCells identity for InteriorFootprintIncidence. -/
theorem allIncidentCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∉ BoundaryFootprintVertices T) → ((∃ j : Fin
            4, LatticeVertexIncidentCell x j ∈ T.cells) → (∀ j : Fin 4, LatticeVertexIncidentCell
            x j ∈ T.cells)) ) := by
  classical
  intro T x hxb hsome j
  by_contra hj
  exact hxb (P3161T2IncidentBoundary T x hsome ⟨j, hj⟩)

end InteriorFootprintIncidence
end ApollonianSuperharmonic

end
