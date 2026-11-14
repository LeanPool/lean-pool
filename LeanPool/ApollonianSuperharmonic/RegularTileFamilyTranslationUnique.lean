/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.RegularTileFamily
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: RegularTileFamilyTranslationUnique]

/-!
# RegularTileFamilyTranslationUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem RegularTileFamilyTranslationUnique (T : ProtoTile)
    (L : AddSubgroup GaussianInt) (U : ProtoTile)
    (hU : U ∈ RegularTileFamily T L) :
    ∃! u : L, U = TileTranslation T (u : GaussianInt) := by
-- BODY
  rcases hU with ⟨u, huL, rfl⟩
  refine ⟨⟨u, huL⟩, rfl, ?_⟩
  intro v hv
  apply Subtype.ext
  have hc := congrArg TileCentroid hv
  rw [(TileTranslationFormulas T v).2.2.2.2.1,
    (TileTranslationFormulas T u).2.2.2.2.1] at hc
  have hre := congrArg Prod.fst hc
  have him := congrArg Prod.snd hc
  dsimp at hre him
  have hre' : (((v.1.re : Int) : Real)) = (((u.re : Int) : Real)) := by
    linarith
  have him' : (((v.1.im : Int) : Real)) = (((u.im : Int) : Real)) := by
    linarith
  apply Zsqrtd.ext
  · exact_mod_cast hre'
  · exact_mod_cast him'

end ApollonianSuperharmonic

end
