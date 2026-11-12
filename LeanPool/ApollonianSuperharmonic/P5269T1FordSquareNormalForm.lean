/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5269T1FordSquareNormalForm]

/-!
# P5269T1FordSquareNormalForm

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5269T1FordSquareNormalForm (P : FordFareyParameter) (hq : 1 < P.q)
    (k : Fin 4) (T : ProtoTile)
    (hT : BandPrototile (FordRecursiveQuadruple P k) T)
    (hpos : 0 < (FordRecursiveQuadruple P k).1) :
    ∃ w : GaussianInt,
      T.cells = (TileTranslation (FordTile (![P.q, P.q₁, P.q₂, 0] k)) w).cells := by
-- BODY
  have trzero (n : Nat) : (TileTranslation (FordTile n) 0).cells =
      (FordTile n).cells := by
    change (FordTile n).cells.image (GaussianTranslation 0) = _
    rw [show GaussianTranslation 0 = id by funext z; simp [GaussianTranslation]]
    exact Finset.image_id
  obtain ⟨hroot, _, hrec⟩ := FordTileRecursiveIdentification P
  obtain ⟨_, S, hS, _, hS0, _, hS1, _⟩ := hrec hq
  have normal (C : CircleCoordinates) (E : ProtoTile) (n : Nat)
      (v : GaussianInt) (hE : BandPrototile C E) (hT : BandPrototile C T)
      (hc : E.cells = (TileTranslation (FordTile n) v).cells) :
      ∃ w : GaussianInt, T.cells = (TileTranslation (FordTile n) w).cells := by
    obtain ⟨u, hu, _⟩ := BandPrototileTranslationNormalForm C T E hT hE
    refine ⟨v + u, hu.trans ?_⟩
    change E.cells.image (GaussianTranslation u) = _
    rw [hc]
    simp only [TileTranslation, Finset.image_image]
    apply Finset.image_congr
    intro z hz
    simp [GaussianTranslation, add_assoc]
  fin_cases k
  · exact normal _ (FordTile P.q) P.q 0
      (by simpa [FordRecursiveQuadruple] using hroot) hT
      (trzero P.q).symm
  · exact normal _ (S 0 true) P.q₁ 0 (hS 0 true).1 hT
      (hS0.trans (trzero P.q₁).symm)
  · exact normal _ (S 1 true) P.q₂ ⟨P.q₁, 0⟩ (hS 1 true).1 hT hS1
  · norm_num [FordRecursiveQuadruple] at hpos

end ApollonianSuperharmonic

end
