/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordTileGeometry
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.ExactTileTiling
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.RegularTileFamily
public import LeanPool.ApollonianSuperharmonic.TileArea
public import LeanPool.ApollonianSuperharmonic.TilingLattice

-- [TABLET NODE: CurvatureOneTileBase]

/-!
# CurvatureOneTileBase

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem CurvatureOneTileBase (C : BandCircle) (hC : C.1.1.1 = 1) :
    ∃ T : ProtoTile,
      LatticeTile T ∧ TileArea T = 1 ∧ QuarterTurnSymmetric T ∧
      ExactTileTiling (RegularTileFamily T (TilingLattice C)) := by
-- BODY
  let T : ProtoTile := ⟨{0}, 0⟩
  have lattice : TilingLattice C = ⊤ := by
    simp [TilingLattice, hC]
  have hT : LatticeTile T := by
    have hunit : FordTile 1 = T := by
      have zero_coordinates : (⟨0, 0⟩ : GaussianInt) = 0 := rfl
      simp [T, FordTile, FordCellDomain, zero_coordinates]
    simpa only [hunit] using (FordTileGeometry 1 (by omega)).1
  refine ⟨T, hT, ?_, ?_, ?_⟩
  · simp [T, TileArea]
  · unfold QuarterTurnSymmetric
    intro p
    norm_num [T, TileRealization, TileCentroid, ClosedSquareRealization]
    constructor <;> intro hp
    · rcases hp with ⟨⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩
      constructor <;> constructor <;> linarith
    · rcases hp with ⟨⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩
      constructor <;> constructor <;> linarith
  · unfold ExactTileTiling RegularTileFamily
    rw [lattice]
    constructor
    · intro U hU
      rcases hU with ⟨u, hu, rfl⟩
      exact (TileDiskAreaCovariance T u).1.mp hT
    · intro x
      refine ⟨TileTranslation T x, ⟨x, trivial, rfl⟩, ?_, ?_⟩
      · simp [T, TileTranslation, GaussianTranslation]
      · intro U hU hx
        rcases hU with ⟨u, hu, rfl⟩
        have equality : x = u := by
          simpa [T, TileTranslation, GaussianTranslation] using hx
        subst x
        rfl

end ApollonianSuperharmonic

end
