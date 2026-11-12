/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas

-- [TABLET NODE: P4085T1RestrictedAdaptedActions]

/-!
# P4085T1RestrictedAdaptedActions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4085T1RestrictedAdaptedActions
    (g g' : BandPackingSymmetry)
    (hg : ∃ w : GaussianInt, g = .shift w ∨ g = .comp (.shift w) .negate)
    (hlift : g' = g ∨ g' = .comp (.comp .negate .negate) g) :
    ∃ m : Fin 4,
      (∀ T, BandPackingSymmetryTileAction g' T = (TileQuarterTurn^[m.val]) T) ∧
      (∀ z, BandPackingSymmetryVectorAction g' z =
        (⟨0, 1⟩ : GaussianInt) ^ m.val * z) ∧
      (∀ (U W : ProtoTile) (z : GaussianInt),
        TileCentroid W - TileCentroid U = (1 / 2 : Real) • GaussianRealPoint z →
        TileCentroid (BandPackingSymmetryTileAction g' W) -
            TileCentroid (BandPackingSymmetryTileAction g' U) =
          (1 / 2 : Real) • GaussianRealPoint (BandPackingSymmetryVectorAction g' z)) := by
-- BODY
  rcases hg with ⟨w, rfl | rfl⟩ <;> rcases hlift with rfl | rfl
  · refine ⟨0, ?_, ?_, ?_⟩
    · intro T; rfl
    · intro z; simp [BandPackingSymmetryVectorAction]
    · intro U W z h; exact h
  · refine ⟨2, ?_, ?_, ?_⟩
    · intro T; rfl
    · intro z
      ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn, pow_succ]
    · intro U W z h
      change TileCentroid (TileQuarterTurn (TileQuarterTurn W)) -
          TileCentroid (TileQuarterTurn (TileQuarterTurn U)) = _
      rw [(TileQuarterTurnFormulas (TileQuarterTurn W)).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn U)).2.2.2.2.1,
        (TileQuarterTurnFormulas W).2.2.2.2.1,
        (TileQuarterTurnFormulas U).2.2.2.2.1]
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      simp [BandPackingSymmetryVectorAction, GaussianRealPoint,
        GaussianQuarterTurn] at h₁ h₂ ⊢
      constructor <;> linarith
  · refine ⟨1, ?_, ?_, ?_⟩
    · intro T; rfl
    · intro z
      ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn]
    · intro U W z h
      change TileCentroid (TileQuarterTurn W) - TileCentroid (TileQuarterTurn U) = _
      rw [(TileQuarterTurnFormulas W).2.2.2.2.1,
        (TileQuarterTurnFormulas U).2.2.2.2.1]
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      simp [BandPackingSymmetryVectorAction, GaussianRealPoint,
        GaussianQuarterTurn] at h₁ h₂ ⊢
      constructor <;> linarith
  · refine ⟨3, ?_, ?_, ?_⟩
    · intro T; rfl
    · intro z
      ext <;> simp [BandPackingSymmetryVectorAction, GaussianQuarterTurn, pow_succ]
    · intro U W z h
      change TileCentroid (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn W))) -
          TileCentroid (TileQuarterTurn (TileQuarterTurn (TileQuarterTurn U))) = _
      rw [(TileQuarterTurnFormulas (TileQuarterTurn (TileQuarterTurn W))).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn (TileQuarterTurn U))).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn W)).2.2.2.2.1,
        (TileQuarterTurnFormulas (TileQuarterTurn U)).2.2.2.2.1,
        (TileQuarterTurnFormulas W).2.2.2.2.1,
        (TileQuarterTurnFormulas U).2.2.2.2.1]
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      simp [BandPackingSymmetryVectorAction, GaussianRealPoint,
        GaussianQuarterTurn] at h₁ h₂ ⊢
      constructor <;> linarith

end ApollonianSuperharmonic

end
