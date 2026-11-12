/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5250T1SeparatedCells]

/-!
# P5250T1SeparatedCells

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5250T1SeparatedCells (k : Nat) (hk : 1 < k) :
    let D := DiamondTile k
    let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
    let Eplus := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
    let Eminus := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
    Disjoint D.cells Eplus.cells ∧ Disjoint L.cells Eplus.cells ∧
      Disjoint D.cells Eminus.cells := by
-- BODY
  classical
  have cell (T : ProtoTile) (u z : GaussianInt) :
      z ∈ (TileTranslation T u).cells ↔ z - u ∈ T.cells := by
    rw [(TileTranslationFormulas T u).1]
    constructor
    · rintro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      simpa [GaussianTranslation] using hw
    · intro hz
      exact Finset.mem_image.mpr ⟨z - u, hz, by simp [GaussianTranslation]⟩
  dsimp only
  refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_,
    Finset.disjoint_left.mpr ?_⟩
  · intro z hD hE
    have hD := (P4194T1DiamondCellRows k z).1.mp hD
    have hE := (P4194T1DiamondCellRows (k - 1)
      (z - ⟨(k : Int), 1 - (k : Int)⟩)).1.mp ((cell _ _ _).mp hE)
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hE
    omega
  · intro z hL hE
    have hL := (P4194T1DiamondCellRows k
      (z - ⟨0, -(2 * (k : Int))⟩)).1.mp ((cell _ _ _).mp hL)
    have hE := (P4194T1DiamondCellRows (k - 1)
      (z - ⟨(k : Int), 1 - (k : Int)⟩)).1.mp ((cell _ _ _).mp hE)
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hL hE
    omega
  · intro z hD hE
    have hD := (P4194T1DiamondCellRows k z).1.mp hD
    have hE := (P4194T1DiamondCellRows (k - 1)
      (z - ⟨-(k : Int), 1 - (k : Int)⟩)).1.mp ((cell _ _ _).mp hE)
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at hE
    omega

end ApollonianSuperharmonic

end
