/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore
public import LeanPool.ApollonianSuperharmonic.P3776T1PlaneMapExists
public import LeanPool.ApollonianSuperharmonic.P3776T1EquivariantDisplacementBound
public import LeanPool.ApollonianSuperharmonic.P3776T1BoundedDisplacementSurjective
public import LeanPool.ApollonianSuperharmonic.P3776T1CellCenterMembership

-- [TABLET NODE: PeriodicTileCoverage]

/-!
# PeriodicTileCoverage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PeriodicTileCoverage {ι : Type} (P : PeriodicTileCore ι) :
    ∀ x : LatticeCell, ∃ a : ι, x ∈ (P.tile a).cells := by
-- BODY
  obtain ⟨f, hf, hperiodic, himage⟩ := P3776T1PlaneMapExists P
  have hbound := P3776T1EquivariantDisplacementBound P.lattice P.latticeReps
    P.lattice_full_rank f hf hperiodic
  have hsurjective := P3776T1BoundedDisplacementSurjective f hf hbound
  intro x
  obtain ⟨y, hy⟩ := hsurjective
    (GaussianRealPoint x + ((1 / 2, 1 / 2) : Real × Real))
  obtain ⟨a, ha⟩ := himage y
  rw [hy] at ha
  exact ⟨a, (P3776T1CellCenterMembership (P.tile a) x).mp ha⟩

end ApollonianSuperharmonic

end
