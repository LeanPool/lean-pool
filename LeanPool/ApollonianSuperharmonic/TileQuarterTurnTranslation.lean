/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileQuarterTurn
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import Mathlib.Init


/-!
# TileQuarterTurnTranslation

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace TileQuarterTurnTranslation

/-- Shared commute identity for TileQuarterTurnTranslation. -/
theorem commute :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), TileQuarterTurn (TileTranslation T x) =
            TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn x)
    ) := by
  classical
  intro T x
  cases T with
  | mk cells anchor =>
    have map : (fun z : GaussianInt => GaussianQuarterTurn (z + x) - 1) =
        (fun z : GaussianInt => (GaussianQuarterTurn z - 1) +
          GaussianQuarterTurn x) := by
      funext z
      ext <;> simp [GaussianQuarterTurn, add_comm]; ring
    apply congrArg₂ (fun c : FiniteTile => fun d : GaussianInt =>
      ProtoTile.mk c d)
    · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
        Finset.image_image, Function.comp_def, map]
    · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
        GaussianQuarterTurn, add_comm]

end TileQuarterTurnTranslation
end ApollonianSuperharmonic

end
