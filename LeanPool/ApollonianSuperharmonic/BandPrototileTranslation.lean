/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: BandPrototileTranslation]

/-!
# BandPrototileTranslation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPrototileTranslation : ∀ (C : CircleCoordinates) (T : ProtoTile)
    (u : GaussianInt),
    BandPrototile C T → BandPrototile C (TileTranslation T u) := by
-- BODY
  intro C T u h
  induction h generalizing u with
  | line w x hw =>
      simp? [TileTranslation, GaussianTranslation]
      exact BandPrototile.line w (x + u) hw
  | unit z x anchor =>
      simp? [TileTranslation, GaussianTranslation]
      exact BandPrototile.unit z (x + u) (anchor + u)
  | @decompose q hq S T hS hcells hfoot hcentroid ih =>
      refine @BandPrototile.decompose q hq
        (fun i s => TileTranslation (S i s) u) (TileTranslation T u) ?_ ?_ ?_ ?_
      · intro i s
        exact ih i s u
      · intro x
        change x ∈ (T.cells.image (GaussianTranslation u)) ↔
          ∃ i s, x ∈ (TileTranslation (S i s) u).cells
        constructor
        · intro hx
          have hx' : ∃ y ∈ T.cells, GaussianTranslation u y = x := by
            simpa only [Finset.mem_image] using hx
          rcases hx' with ⟨y, hy, rfl⟩
          rcases (hcells y).mp hy with ⟨i, s, hz⟩
          refine ⟨i, s, ?_⟩
          rw [(TileTranslationFormulas (S i s) u).1]
          exact Finset.mem_image.mpr ⟨y, hz, rfl⟩
        · intro hx
          rcases hx with ⟨i, s, hz⟩
          have hz' : ∃ y ∈ (S i s).cells, GaussianTranslation u y = x := by
            simpa only [(TileTranslationFormulas (S i s) u).1, Finset.mem_image] using hz
          rcases hz' with ⟨y, hy, rfl⟩
          exact Finset.mem_image.mpr ⟨y, (hcells y).mpr ⟨i, s, hy⟩, rfl⟩
      · intro i s x hx
        rw [(TileTranslationFormulas (S i s) u).2.2.2.2.2.1,
          (TileTranslationFormulas T u).2.2.2.2.2.1] at *
        rcases hx with ⟨y, hy, rfl⟩
        exact ⟨y, hfoot i s hy, rfl⟩
      · intro i s
        rw [(TileTranslationFormulas (S i s) u).2.2.2.2.1]
        rw [(TileTranslationFormulas T u).2.2.2.2.1]
        simpa [Prod.ext_iff, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
          smul_add] using hcentroid i s

end ApollonianSuperharmonic

end
