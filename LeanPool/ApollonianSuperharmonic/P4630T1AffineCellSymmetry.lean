/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P4630T1AffineCellSymmetry]

/-!
# P4630T1AffineCellSymmetry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4630T1AffineCellSymmetry (T : ProtoTile) (t : GaussianInt)
    (hne : T.cells.Nonempty)
    (h : T.cells.image (fun x => GaussianQuarterTurn x - 1 + t) = T.cells) :
    QuarterTurnSymmetric T := by
-- BODY
  classical
  let U := TileTranslation (TileQuarterTurn T) t
  have cells : U.cells = T.cells := by
    change (T.cells.image (fun x => GaussianQuarterTurn x - 1)).image
      (GaussianTranslation t) = T.cells
    simpa only [Finset.image_image, Function.comp_def, GaussianTranslation] using h
  have cent : TileCentroid U = TileCentroid T := by
    simp only [TileCentroid, cells, ite_eq_left hne]
  have real : TileRealization U = TileRealization T := by
    simp only [TileRealization, cells]
  have hc := cent
  rw [(TileTranslationFormulas (TileQuarterTurn T) t).2.2.2.2.1,
    (TileQuarterTurnFormulas T).2.2.2.2.1] at hc
  have hcr := congrArg Prod.fst hc
  have hci := congrArg Prod.snd hc
  dsimp at hcr hci
  have image :
      (fun p : Real × Real =>
        ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
          (TileCentroid T).2 + (p.1 - (TileCentroid T).1))) ''
        TileRealization T = TileRealization T := by
    calc
      _ = (fun p : Real × Real => (-p.2 + (t.re : Real),
          p.1 + (t.im : Real))) '' TileRealization T := by
        apply congrArg (fun f : (Real × Real) → Real × Real =>
          f '' TileRealization T)
        funext p
        apply Prod.ext <;> dsimp <;> linarith
      _ = TileRealization U := by
        rw [(TileTranslationFormulas (TileQuarterTurn T) t).2.2.2.1,
          (TileQuarterTurnFormulas T).2.2.2.1, Set.image_image]
      _ = TileRealization T := real
  intro p
  constructor
  · intro hp
    rw [← image]
    exact ⟨p, hp, rfl⟩
  · intro hp
    rw [← image] at hp
    obtain ⟨z, hz, he⟩ := hp
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    have heq : z = p := by
      apply Prod.ext <;> dsimp at he₁ he₂ ⊢ <;> linarith
    simpa only [heq] using hz

end ApollonianSuperharmonic

end
