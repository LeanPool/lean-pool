/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.DiamondTile

-- [TABLET NODE: P5124T1BoundaryGeometry]

/-!
# P5124T1BoundaryGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5124T1BoundaryGeometry (k : Nat) (hk : 0 < k) :
    let r := fun b : Int => min (b + 1) (2 * (k : Int) - b)
    let H := fun a b : Int =>
      ((b = 0 ∨ b = 2 * (k : Int)) ∧ -1 ≤ a ∧ a < 1) ∨
      (1 ≤ b ∧ b < (k : Int) ∧ (a = -b - 1 ∨ a = b)) ∨
      ((k : Int) < b ∧ b < 2 * (k : Int) ∧
        (a = b - 2 * (k : Int) - 1 ∨ a = 2 * (k : Int) - b))
    let E : Set (Finset GaussianInt) := {e | ∃ a b : Int,
      (H a b ∧ e = {⟨a, b⟩, ⟨a + 1, b⟩}) ∨
      (0 ≤ b ∧ b < 2 * (k : Int) ∧ (a = -r b ∨ a = r b) ∧
        e = {⟨a, b⟩, ⟨a, b + 1⟩})}
    BoundaryFootprintEdges (DiamondTile k) = E ∧
      BoundaryFootprintVertices (DiamondTile k) = {z | ∃ e ∈ E, z ∈ e} := by
-- BODY
  classical
  let r := fun b : Int => min (b + 1) (2 * (k : Int) - b)
  let H := fun a b : Int =>
    ((b = 0 ∨ b = 2 * (k : Int)) ∧ -1 ≤ a ∧ a < 1) ∨
    (1 ≤ b ∧ b < (k : Int) ∧ (a = -b - 1 ∨ a = b)) ∨
    ((k : Int) < b ∧ b < 2 * (k : Int) ∧
      (a = b - 2 * (k : Int) - 1 ∨ a = 2 * (k : Int) - b))
  let E : Set (Finset GaussianInt) := {e | ∃ a b : Int,
    (H a b ∧ e = {⟨a, b⟩, ⟨a + 1, b⟩}) ∨
    (0 ≤ b ∧ b < 2 * (k : Int) ∧ (a = -r b ∨ a = r b) ∧
      e = {⟨a, b⟩, ⟨a, b + 1⟩})}
  change BoundaryFootprintEdges (DiamondTile k) = E ∧
    BoundaryFootprintVertices (DiamondTile k) = {z | ∃ e ∈ E, z ∈ e}
  have horizontal (z : GaussianInt) :
      ((z ∈ (DiamondTile k).cells ∧ z - ⟨0, 1⟩ ∉ (DiamondTile k).cells) ∨
        (z ∉ (DiamondTile k).cells ∧ z - ⟨0, 1⟩ ∈ (DiamondTile k).cells)) ↔
      H z.re z.im := by
    simp only [DiamondTile, (P4194T1DiamondCellRows _ _).1,
      Zsqrtd.re_sub, Zsqrtd.im_sub]
    dsimp [H]
    omega
  have vertical (z : GaussianInt) :
      ((z ∈ (DiamondTile k).cells ∧ z - 1 ∉ (DiamondTile k).cells) ∨
        (z ∉ (DiamondTile k).cells ∧ z - 1 ∈ (DiamondTile k).cells)) ↔
      0 ≤ z.im ∧ z.im < 2 * (k : Int) ∧
        (z.re = -r z.im ∨ z.re = r z.im) := by
    simp only [DiamondTile, (P4194T1DiamondCellRows _ _).1,
      Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
    dsimp [r]
    omega
  have he : BoundaryFootprintEdges (DiamondTile k) = E := by
    have eta (z : GaussianInt) : (⟨z.re, z.im⟩ : GaussianInt) = z := by
      cases z
      rfl
    have h1 (z : GaussianInt) : z + 1 = ⟨z.re + 1, z.im⟩ := by
      ext <;> simp
    have hi (z : GaussianInt) : z + ⟨0, 1⟩ = ⟨z.re, z.im + 1⟩ := by
      ext <;> simp
    ext e
    constructor
    · rintro ⟨z, ⟨he, hz⟩ | ⟨he, hz⟩⟩
      · exact ⟨z.re, z.im, Or.inl ⟨(horizontal z).mp hz,
          by simpa only [h1, hi, eta] using he⟩⟩
      · obtain ⟨hb0, hb, ha⟩ := (vertical z).mp hz
        exact ⟨z.re, z.im, Or.inr ⟨hb0, hb, ha,
          by simpa only [h1, hi, eta] using he⟩⟩
    · rintro ⟨a, b, ⟨hz, he⟩ | ⟨hb0, hb, ha, he⟩⟩
      · exact ⟨⟨a, b⟩, Or.inl ⟨by simpa only [h1, hi] using he,
          (horizontal ⟨a, b⟩).mpr hz⟩⟩
      · exact ⟨⟨a, b⟩, Or.inr ⟨by simpa only [h1, hi] using he,
          (vertical ⟨a, b⟩).mpr ⟨hb0, hb, ha⟩⟩⟩
  have hne : (DiamondTile k).cells.Nonempty := by
    refine ⟨0, (P4194T1DiamondCellRows k 0).1.mpr ?_⟩
    norm_num
    omega
  exact ⟨he, by simp only [BoundaryFootprintVertices, ite_eq_left hne, he]⟩

end ApollonianSuperharmonic

end
