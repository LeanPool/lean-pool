/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.FordTileGeometry
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance

-- [TABLET NODE: P4590T1PositivePrototileDisk]

/-!
# P4590T1PositivePrototileDisk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4590T1PositivePrototileDisk (c : CircleCoordinates) (U : ProtoTile)
    (hU : BandPrototile c U) (hc : 0 < c.1) : LatticeTile U := by
-- BODY
  cases hU with
  | line w x hw => simp at hc
  | unit z x anchor =>
    have hford := (FordTileGeometry 1 (by norm_num)).1
    have hcells : ({x} : Finset GaussianInt) =
        (TileTranslation (FordTile 1) x).cells := by
      ext y
      simp [TileTranslation, FordTile, FordCellDomain, GaussianTranslation,
        ]
      cases x; cases y; simp [Zsqrtd.ext_iff]
    have ht : LatticeTile (TileTranslation (FordTile 1) x) :=
      (TileDiskAreaCovariance (FordTile 1) x).1.mp hford
    change TopologicalDisk (TileRealization _) at ht ⊢
    simpa only [TileRealization, hcells] using ht
  | @decompose r hr S X hS hcells hfoot hcentroid =>
    exact (BandTileSimultaneousInduction r hr U
      (BandPrototile.decompose hr hS hcells hfoot hcentroid)).1

end ApollonianSuperharmonic

end
