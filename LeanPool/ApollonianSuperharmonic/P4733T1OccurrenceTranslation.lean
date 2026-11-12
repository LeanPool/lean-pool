/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4677T2DrawingData
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation

-- [TABLET NODE: P4733T1OccurrenceTranslation]

/-!
# P4733T1OccurrenceTranslation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1OccurrenceTranslation (P : Fin 3 → Bool → ProtoTile)
    {u v : GaussianInt} {L : AddSubgroup GaussianInt}
    (D : P4677T2DrawingData u v L) (w : L) (a : PeriodicSubtileIndex) :
    SubtileOccurrenceInterpretation P u v (D.shift w a) =
      TileTranslation (SubtileOccurrenceInterpretation P u v a) w := by
-- BODY
  have translate_comp (T : ProtoTile) (a b : GaussianInt) :
      TileTranslation (TileTranslation T a) b = TileTranslation T (a + b) := by
    cases T with
    | mk cells anchor =>
      simp only [TileTranslation]
      rw [ProtoTile.mk.injEq]
      constructor
      · rw [Finset.image_image]
        congr 1
        funext x
        simp [GaussianTranslation, add_assoc]
      · simp [GaussianTranslation, add_assoc]
  have offset : ((a.first + (D.coordinates w).1 : Int) : GaussianInt) * u +
      ((a.second + (D.coordinates w).2 : Int) : GaussianInt) * v =
      (a.first : GaussianInt) * u + (a.second : GaussianInt) * v + (w : GaussianInt) := by
    rw [← D.coordinates_spec w]
    push_cast
    ring
  rw [D.shift_eq]
  dsimp only [SubtileOccurrenceInterpretation]
  rw [offset, translate_comp]

end ApollonianSuperharmonic

end
