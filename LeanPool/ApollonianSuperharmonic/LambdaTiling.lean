/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototileExists
public import LeanPool.ApollonianSuperharmonic.BandTileTopologyApplication
public import LeanPool.ApollonianSuperharmonic.CurvatureOneTileBase
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.BandGenealogy

-- [TABLET NODE: LambdaTiling]

/-!
# LambdaTiling

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem LambdaTiling : ∀ C : BandCircle, ∃ T : ProtoTile,
    LatticeTile T ∧ QuarterTurnSymmetric T ∧
      ExactTileTiling (RegularTileFamily T (TilingLattice C)) ∧
      (C.1.1.1 ≠ 1 →
        Nat.card {U : ProtoTile //
          U ∈ RegularTileFamily T (TilingLattice C) ∧ U ≠ T ∧
            TileBordering T U} = 6) := by
-- BODY
  intro C
  by_cases hcurv : C.1.1.1 = 1
  · obtain ⟨T, hlat, harea, hsym, htile⟩ := CurvatureOneTileBase C hcurv
    exact ⟨T, hlat, hsym, htile, fun hne => False.elim (hne hcurv)⟩
  · obtain ⟨q, hsemi, hqC, hlt, huniq⟩ := Or.resolve_left (BandGenealogy C) hcurv
    have hproper : ProperBandQuadruple q := by
      refine ⟨hsemi, ?_⟩
      intro j
      simpa [hqC] using hlt j
    obtain ⟨T, hT⟩ := BandPrototileExists C.1
    obtain ⟨hlat, harea, hcomplements, hsym, hT3, hT4, hT5, hT6⟩ :=
      BandTileSimultaneousInduction q hproper T (by simpa [hqC] using hT)
    obtain ⟨htile, hcard⟩ :=
      BandTileTopologyApplication C q hproper hqC T (by simpa [hqC] using hT)
    exact ⟨T, hlat, hsym, htile, fun _ => hcard⟩

end ApollonianSuperharmonic

end
