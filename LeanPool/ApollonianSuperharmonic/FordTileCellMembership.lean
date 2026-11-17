/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordTile
public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTranslation

/-!
# Ford tile cell membership

Shared coordinate characterization adapted from Wesley Pegden's Apache-2.0
Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Ford cells are precisely the integer basepoints in the half-open square. -/
theorem FordTileCellMembership (m : Nat) (z : GaussianInt) :
    z ∈ (FordTile m).cells ↔ 0 ≤ z.re ∧ z.re < m ∧ 0 ≤ z.im ∧ z.im < m := by
  classical
  change z ∈ ((Finset.range m).product (Finset.range m)).image
    (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt)) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨j, k⟩, hjk, rfl⟩
    have hjk := Finset.mem_product.mp hjk
    simp only [Finset.mem_range] at hjk
    dsimp; omega
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨(z.re.toNat, z.im.toNat),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩,
      by ext <;> dsimp <;> omega⟩

namespace FordTileCellMembership

/-- Translating a Ford square translates its coordinate bounds. -/
theorem translated (n : Nat) (v z : GaussianInt) :
    z ∈ (TileTranslation (FordTile n) v).cells ↔
      0 ≤ (z - v).re ∧ (z - v).re < n ∧ 0 ≤ (z - v).im ∧ (z - v).im < n := by
  classical
  rw [← FordTileCellMembership n (z - v)]
  change z ∈ (FordTile n).cells.image (GaussianTranslation v) ↔ _
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    simpa [GaussianTranslation] using hw
  · intro hz
    exact Finset.mem_image.mpr ⟨z - v, hz, by simp [GaussianTranslation]⟩

end FordTileCellMembership

end ApollonianSuperharmonic

end
