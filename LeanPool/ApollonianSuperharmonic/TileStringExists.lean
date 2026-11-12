/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AffineTriangularStrip
public import LeanPool.ApollonianSuperharmonic.TileStringCoordinateTransport

-- [TABLET NODE: TileStringExists]

/-!
# TileStringExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileStringExists (C : BandCircle) (orientation : Bool)
    (base R S : ProtoTile)
    (hbase : BandPrototile C.1.1 base)
    (hR : R ∈ RegularTileFamily base (TilingLattice C))
    (hS : S ∈ RegularTileFamily base (TilingLattice C)) :
    ∃ tiles : List ProtoTile, TileString C orientation base R S tiles := by
-- BODY
  obtain ⟨a, b, hdet, ha, hb, hbasis, hsource, hchart⟩ :=
    TileStringCoordinateTransport C orientation base hbase
  dsimp only at hchart
  obtain ⟨hfamily, hadjacent, hheight, htransport⟩ := hchart
  obtain ⟨r, hr, hr_unique⟩ := (hfamily R).mp hR
  obtain ⟨s, hs, hs_unique⟩ := (hfamily S).mp hS
  let tileAt := fun z : Int × Int =>
    TileTranslation base
      ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
  have map_corr : ∀ coordinates : List (Int × Int), List.Forall₂
      (fun T z => T =
        TileTranslation base
          ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b))
      (coordinates.map tileAt) coordinates := by
    intro coordinates
    induction coordinates with
    | nil => exact .nil
    | cons z zs ih =>
        exact .cons (by simp [tileAt]) ih
  obtain ⟨coordinates, hsegment, hsegment_unique⟩ :=
    (AffineTriangularStrip).1 r s
  let tiles := coordinates.map tileAt
  have hcorr : List.Forall₂
      (fun T z => T =
        TileTranslation base
          ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b))
      tiles coordinates := by
    dsimp [tiles]
    exact map_corr coordinates
  refine ⟨tiles, (htransport R S tiles r s hr hs).mpr ?_⟩
  refine ⟨coordinates, ?_, ?_⟩
  · constructor
    · exact hcorr
    · exact hsegment
  · intro other hother
    exact hsegment_unique other hother.2

end ApollonianSuperharmonic

end
