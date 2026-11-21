/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.Rupert.Basic

/-!
# Rupert's property for finite sets

Relates the finite-set form of Rupert's property used in the geometric arguments to
the indexed-vertex formulation in `LeanPool.Rupert.Basic`.
-/

@[expose] public section

namespace RupertMinimality

/-- The Rupert Property for a convex polyhedron given as a finite set of vertices. -/
def IsRupert (vertices : Finset ℝ³) : Prop :=
   ∃ inner_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   ∃ inner_offset : EuclideanSpace ℝ (Fin 2),
   ∃ outer_rotation ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
   let hull := convexHull ℝ vertices
   let inner_shadow := { inner_offset + projXy (inner_rotation.toEuclideanLin p) | p ∈ hull }
   let outer_shadow := { projXy (outer_rotation.toEuclideanLin p) | p ∈ hull }
   inner_shadow ⊆ interior outer_shadow

/-- Enumerating the points of a finite set gives the same Rupert property. -/
theorem isRupert_finset_iff_indexed (vertices : Finset ℝ³) :
    IsRupert vertices ↔ _root_.IsRupert (fun v : vertices => v.val) := by
  have hvertices : {v.val | v : vertices} = (vertices : Set ℝ³) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  unfold IsRupert _root_.IsRupert
  rw [hvertices]

end RupertMinimality
