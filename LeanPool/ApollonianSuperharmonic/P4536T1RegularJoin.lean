/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.AncestorOdometerInnerSupportNormalization
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.ParentVectorsInTilingLattice
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport

-- [TABLET NODE: P4536T1RegularJoin]

/-!
# P4536T1RegularJoin

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4536T1RegularJoin
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (hcenter : TileCentroid (D.tiles F.slot false) - TileCentroid Rminus =
      GaussianRealPoint (BandVectors.1 (F.q (F.slot + 1).succ) (F.q F.slot.succ))) :
    ∃ J : ProtoTile,
      J ∈ RegularTileFamily base (TilingLattice C) ∧
      TileCentroid J = TileCentroid (D.tiles F.slot false) ∧
      J.cells = (D.tiles F.slot false).cells ∧
      TileOdometer C.1.1 J (D.functions F.slot false) ∧
      AncestorOdometer C.1.1 F.outer.1.1
        J F.tile (D.functions F.slot false) F.odometer ∧
      BandSubtileOccurrence F.q F.tile F.slot false J := by
-- BODY
  let y := BandVectors.1 (F.q (F.slot + 1).succ) (F.q F.slot.succ)
  have hy : y ∈ TilingLattice C :=
    (ParentVectorsInTilingLattice F.q F.proper F.slot C F.parent).1
  obtain ⟨r, hr, hR⟩ := F.minus_family
  let J := TileTranslation base (r + y)
  have hfamily : J ∈ RegularTileFamily base (TilingLattice C) :=
    ⟨r + y, (TilingLattice C).add_mem hr hy, rfl⟩
  have hband : BandPrototile C.1.1 J :=
    BandPrototileTranslation C.1.1 base (r + y) F.base_band
  have hJcenter : TileCentroid J - TileCentroid Rminus = GaussianRealPoint y := by
    rw [hR]
    change TileCentroid (TileTranslation base (r + y)) -
      TileCentroid (TileTranslation base r) = GaussianRealPoint y
    rw [(TileTranslationFormulas base (r + y)).2.2.2.2.1,
      (TileTranslationFormulas base r).2.2.2.2.1]
    ext <;> simp [GaussianRealPoint]
  have hcent : TileCentroid J = TileCentroid (D.tiles F.slot false) := by
    calc
      TileCentroid J = (TileCentroid J - TileCentroid Rminus) +
          TileCentroid Rminus := (sub_add_cancel _ _).symm
      _ = GaussianRealPoint y + TileCentroid Rminus := by rw [hJcenter]
      _ = TileCentroid (D.tiles F.slot false) := by rw [← hcenter]; abel
  have hpos : 0 < (F.q F.slot.succ).1 := F.parent ▸ C.2
  have hNband : BandPrototile C.1.1 (D.tiles F.slot false) :=
    F.parent ▸ (D.occurrences F.slot false).1
  have hcells : (D.tiles F.slot false).cells = J.cells :=
    (BandPrototileCentroidUnique C.1.1 _ J hNband hband hcent.symm).1
  have hodo : TileOdometer C.1.1 J (D.functions F.slot false) :=
    PositiveCurvatureTileOdometerSupportTransport C.1.1 _ J _ C.2
      (F.parent ▸ D.odometers F.slot false) hband hcells
  have hstrict : (F.q F.slot.succ).1 < F.outer.1.1.1 :=
    F.child ▸ F.proper.2 F.slot
  have hanc : AncestorOdometer C.1.1 F.outer.1.1
      J F.tile (D.functions F.slot false) F.odometer := by
    have h := AncestorOdometerInnerSupportNormalization
      (F.q F.slot.succ) F.outer.1.1 (D.tiles F.slot false) J F.tile
      (D.functions F.slot false) F.odometer hpos hstrict
      (D.ancestors F.slot false hpos) (F.parent.symm ▸ hband) hcells
    exact F.parent ▸ h
  have hdom := PositiveCurvatureTileOdometerDomain C.1.1 J _ C.2 hodo
  have houterdom := PositiveCurvatureTileOdometerDomain F.outer.1.1 F.tile _
    F.outer.2 F.outer_odo
  have hfoot : FootprintVertices J ⊆ FootprintVertices F.tile := by
    intro z hz
    rw [← houterdom]
    apply D.domain_subset F.slot false
    change z ∈ ((D.functions F.slot false).domain : Set GaussianInt)
    rwa [hdom]
  refine ⟨J, hfamily, hcent, hcells.symm, hodo, hanc,
    F.parent.symm ▸ hband, hfoot, ?_⟩
  rw [hcent]
  exact (D.occurrences F.slot false).2.2

end ApollonianSuperharmonic

end
