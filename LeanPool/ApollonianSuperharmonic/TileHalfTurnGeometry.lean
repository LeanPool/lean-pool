/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import Mathlib.Init


/-!
# TileHalfTurnGeometry

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace TileHalfTurnGeometry

/-- Shared involutive identity for TileHalfTurnGeometry. -/
theorem involutive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        Function.Involutive tau ) := by
  classical
  intro q u w t tau z
  dsimp [tau]
  abel

/-- Shared cells identity for TileHalfTurnGeometry. -/
theorem cells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        ∀ U, (H U).cells = U.cells.image tau ) := by
  classical
  intro q u w t H tau U
  simp only [H, TileTranslation, TileQuarterTurn, Finset.image_image]
  apply Finset.image_congr
  intro z hz
  apply Zsqrtd.ext <;> simp [Function.comp_def, GaussianTranslation,
    GaussianQuarterTurn, tau] <;> ring

/-- Shared realization identity for TileHalfTurnGeometry. -/
theorem realization :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        ((t.re : Real) = 2 * (TileCentroid T).1 ∧ (t.im : Real) = 2 * (TileCentroid T).2) → (
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        ∀ U, TileRealization (H U) = (fun p : Real × Real => (2 * (TileCentroid T).1 - p.1, 2 *
            (TileCentroid T).2 - p.2)) '' TileRealization U) ) := by
  classical
  intro q T u w t ht H U
  dsimp only [H]
  rw [(TileTranslationFormulas _ t).2.2.2.1,
    (TileQuarterTurnFormulas (TileQuarterTurn U)).2.2.2.1,
    (TileQuarterTurnFormulas U).2.2.2.1, Set.image_image, Set.image_image]
  congr 1
  funext p
  apply Prod.ext <;> dsimp <;> simp only [ht.1, ht.2] <;> ring

end TileHalfTurnGeometry
end ApollonianSuperharmonic

end
