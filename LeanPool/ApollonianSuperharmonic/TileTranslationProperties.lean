/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import Mathlib.Init



/-!
# TileTranslationProperties

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace TileTranslationProperties

/-- Shared zero identity for TileTranslationProperties. -/
theorem zero :
    (by
      classical
      exact
        ∀ (U : ProtoTile), TileTranslation U 0 = U ) := by
  classical
  intro U
  have hzero : GaussianTranslation (0 : GaussianInt) = id := by
    funext z
    simp [GaussianTranslation]
  cases U
  simp [TileTranslation, hzero, GaussianTranslation]

/-- Shared cells identity for TileTranslationProperties. -/
theorem cells :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (d : GaussianInt), (TileTranslation X d).cells = X.cells.image
            (GaussianTranslation d) ) := by
  classical
  intro X d
  exact (TileTranslationFormulas X d).1

/-- Shared add identity for TileTranslationProperties. -/
theorem add :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (v : GaussianInt), ∀ (z : GaussianInt), TileTranslation
            (TileTranslation T v) z = TileTranslation T (v + z) ) := by
  classical
  intro T v z
  cases T with
  | mk cells anchor =>
    apply congrArg₂ ProtoTile.mk
    · ext q
      simp [TileTranslation, GaussianTranslation, add_comm, add_left_comm]
    · simp [TileTranslation, GaussianTranslation, add_comm, add_left_comm]

/-- Cell inclusion is preserved by translating both tiles. -/
theorem cellsSubset (X Y : ProtoTile) (hXY : X.cells ⊆ Y.cells) (d : GaussianInt) :
    (TileTranslation X d).cells ⊆ (TileTranslation Y d).cells := by
  rw [cells, cells]
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨w, hXY hw, rfl⟩

/-- A cell belongs to a translated tile exactly when its inverse translate belongs to the tile. -/
theorem mem_cells (T : ProtoTile) (w z : GaussianInt) :
    z ∈ (TileTranslation T w).cells ↔ z - w ∈ T.cells := by
  classical
  rw [cells]
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    simpa [GaussianTranslation] using hx
  · intro hz
    exact Finset.mem_image.mpr ⟨z - w, hz, by simp [GaussianTranslation]⟩

end TileTranslationProperties
end ApollonianSuperharmonic

end
