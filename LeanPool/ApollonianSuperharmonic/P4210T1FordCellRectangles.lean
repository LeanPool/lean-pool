/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: P4210T1FordCellRectangles]

/-!
# P4210T1FordCellRectangles

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4210T1FordCellRectangles (q : Nat) (z : GaussianInt) :
    (z ∈ (FordTile q).cells ↔
      0 ≤ z.re ∧ z.re < (q : Int) ∧ 0 ≤ z.im ∧ z.im < (q : Int)) ∧
    (∀ r s : Nat, q = r + s →
      (z ∈ (FordTile q).cells ↔
        z ∈ (FordTile r).cells ∨
        z ∈ (TileTranslation (FordTile r) ⟨(s : Int), (s : Int)⟩).cells ∨
        z ∈ (TileTranslation (FordTile s) ⟨(r : Int), 0⟩).cells ∨
        z ∈ (TileTranslation (FordTile s) ⟨0, (r : Int)⟩).cells)) := by
-- BODY
  have coordinates (q : Nat) (z : GaussianInt) :
      z ∈ (FordTile q).cells ↔
        0 ≤ z.re ∧ z.re < (q : Int) ∧ 0 ≤ z.im ∧ z.im < (q : Int) := by
    constructor
    · intro hz
      obtain ⟨⟨m, n⟩, ha, rfl⟩ := Finset.mem_image.mp hz
      have hm := Finset.mem_range.mp (Finset.mem_product.mp ha).1
      have hn := Finset.mem_range.mp (Finset.mem_product.mp ha).2
      simp [hm, hn]
    · rintro ⟨hr, hrq, hi, hiq⟩
      have hm : z.re.toNat < q := by omega
      have hn : z.im.toNat < q := by omega
      apply Finset.mem_image.mpr
      refine ⟨(z.re.toNat, z.im.toNat), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hm, Finset.mem_range.mpr hn⟩, ?_⟩
      apply Zsqrtd.ext <;> simp [hr, hi]
  have translated_mem (r : Nat) (u z : GaussianInt) :
      z ∈ (TileTranslation (FordTile r) u).cells ↔
        z - u ∈ (FordTile r).cells := by
    change z ∈ (FordTile r).cells.image (GaussianTranslation u) ↔ _
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      simpa [GaussianTranslation] using hy
    · intro hz
      exact Finset.mem_image.mpr
        ⟨z - u, hz, by simp [GaussianTranslation]⟩
  refine ⟨coordinates q z, ?_⟩
  intro r s hq
  have hsum : (q : Int) = (r : Int) + (s : Int) := by exact_mod_cast hq
  simp only [translated_mem, coordinates, Zsqrtd.re_sub, Zsqrtd.im_sub]
  omega

end ApollonianSuperharmonic

end
