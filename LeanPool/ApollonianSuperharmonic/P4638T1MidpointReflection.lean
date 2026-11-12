/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototileCentralSymmetry
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P4638T1MidpointReflection]

/-!
# P4638T1MidpointReflection

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4638T1MidpointReflection (C : CircleCoordinates) (T U : ProtoTile)
    (hT : BandPrototile C T) (hU : BandPrototile C U)
    (hnonempty : T.cells.Nonempty) (c : Real × Real)
    (hcent : TileCentroid U =
      (2 * c.1 - (TileCentroid T).1, 2 * c.2 - (TileCentroid T).2)) :
    CentrallyReflectedAt c T U := by
-- BODY
  obtain ⟨u, hcells, _⟩ := BandPrototileTranslationNormalForm C U T hU hT
  have htransnonempty : (TileTranslation T u).cells.Nonempty := by
    rw [(TileTranslationFormulas T u).1]
    exact hnonempty.image _
  have hUnonempty : U.cells.Nonempty := hcells.symm ▸ htransnonempty
  have hcentcells : TileCentroid U = TileCentroid (TileTranslation T u) := by
    simp only [TileCentroid, ite_eq_left htransnonempty, hcells]
  have hrealcells : TileRealization U = TileRealization (TileTranslation T u) := by
    simp only [TileRealization, hcells]
  have hc := hcentcells.trans (TileTranslationFormulas T u).2.2.2.2.1
  have hre := congrArg Prod.fst (hc.symm.trans hcent)
  have him := congrArg Prod.snd (hc.symm.trans hcent)
  dsimp at hre him
  have hs := BandPrototileCentralSymmetry C T hT
  unfold CentrallyReflectedAt at hs ⊢
  rw [hrealcells, (TileTranslationFormulas T u).2.2.2.1]
  nth_rewrite 1 [hs]
  rw [Set.image_image]
  congr 1
  funext p
  apply Prod.ext <;> dsimp <;> linarith

end ApollonianSuperharmonic

end
