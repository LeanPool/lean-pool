/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileStringCoordinateTransport
public import LeanPool.ApollonianSuperharmonic.AffineTriangularStrip

-- [TABLET NODE: TileStringUnique]

/-!
# TileStringUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileStringUnique (C : BandCircle) (orientation : Bool)
    (base R S : ProtoTile)
    (left right : List ProtoTile)
    (hleft : TileString C orientation base R S left)
    (hright : TileString C orientation base R S right) :
    left = right := by
-- BODY
  have hbase : BandPrototile C.1.1 base := hleft.1
  obtain ⟨a, b, hdet, ha, hb, hbasis, hsource, hchart⟩ :=
    TileStringCoordinateTransport C orientation base hbase
  dsimp only at hchart
  obtain ⟨hfamily, hadjacent, hheight, htransport⟩ := hchart
  have hRmem : R ∈ RegularTileFamily base (TilingLattice C) := by
    exact hleft.2.2.2.2.1 R (List.mem_of_mem_head? hleft.2.1)
  have hSmem : S ∈ RegularTileFamily base (TilingLattice C) := by
    exact hleft.2.2.2.2.1 S (List.mem_of_getLast? hleft.2.2.1)
  obtain ⟨r, hr, hr_unique⟩ := (hfamily R).mp hRmem
  obtain ⟨s, hs, hs_unique⟩ := (hfamily S).mp hSmem
  obtain ⟨p, hp, hp_unique⟩ := (htransport R S left r s hr hs).mp hleft
  obtain ⟨q, hq, hq_unique⟩ := (htransport R S right r s hr hs).mp hright
  have hpq : p = q := (AffineTriangularStrip).1 r s |>.unique hp.2 hq.2
  subst q
  clear hp_unique hq_unique hr_unique hs_unique
  have correspondence_unique : ∀ (xs ys : List ProtoTile) (zs : List (Int × Int)),
      List.Forall₂ (fun T z => T =
        TileTranslation base
          ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)) xs zs →
      List.Forall₂ (fun T z => T =
        TileTranslation base
          ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)) ys zs →
      xs = ys := by
    intro xs ys zs hxs
    induction hxs generalizing ys with
    | nil =>
        intro hys
        cases hys
        rfl
    | cons hx hxs ih =>
        intro hys
        cases hys with
        | cons hy hys =>
            congr
            · exact hx.trans hy.symm
            · exact ih _ hys
  exact correspondence_unique left right p hp.1 hq.1

end ApollonianSuperharmonic

end
