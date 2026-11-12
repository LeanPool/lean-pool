/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.AncestorTileCentralCovariance
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.PartialOdometerHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.TileOdometerCentralSymmetry

-- [TABLET NODE: AncestorOdometerCentralCovariance]

/-!
# AncestorOdometerCentralCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem AncestorOdometerCentralCovariance
    (C C' : CircleCoordinates) (T T' : ProtoTile)
    (h h' : PartialOdometer) (u a : GaussianInt) (b : Int)
    (hancestor : AncestorOdometer C C' T T' h h') :
    AncestorOdometer C C'
      (TileTranslation (TileHalfTurn T) u)
      (TileTranslation (TileHalfTurn T') u)
      (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) u a b)
      (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h') u a b) := by
-- BODY
  rcases hancestor with ⟨hO, hAT, hfoot, hsub, hval⟩
  have hsym := TileOdometerCentralSymmetry C' T' h' hO
  have hout := TileOdometerAffineTranslation C' (TileHalfTurn T')
    (PartialOdometerHalfTurn h') u a b hsym.1
  have hat := AncestorTileCentralCovariance C C' T T' u hAT
  have hhalf : (PartialOdometerHalfTurn h).domain =
      FootprintVertices (TileHalfTurn T) := by
    ext x
    change x ∈ (PartialOdometerHalfTurn h).domain ↔
      x ∈ FootprintVertices (TileHalfTurn T)
    rw [(PartialOdometerHalfTurnFormulas h).1]
    rw [(TileHalfTurnFormulas T).2.2.2.2.2.2.1]
    simp only [Set.mem_image]
    constructor
    · intro hx
      exact ⟨-x, hfoot ▸ hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      have hz : y ∈ (h.domain : Set GaussianInt) := hfoot.symm ▸ hy
      simpa using hz
  have hfoot' :
      (PartialOdometerAffineTranslate (PartialOdometerHalfTurn h) u a b).domain =
        FootprintVertices (TileTranslation (TileHalfTurn T) u) := by
    exact ((PartialOdometerAffineTranslateFormulas
      (PartialOdometerHalfTurn h) u a b).2.2.2.2.1 (TileHalfTurn T) hhalf)
  refine ⟨hout, hat, hfoot', ?_, ?_⟩
  · intro x hx
    have hx' := ((PartialOdometerAffineTranslateFormulas
      (PartialOdometerHalfTurn h) u a b).2.1 x).mp hx
    have hy : - (x - u) ∈ h.domain :=
      (PartialOdometerHalfTurnFormulas h).1 (x - u) |>.mp hx'
    have hy' := hsub hy
    apply ((PartialOdometerAffineTranslateFormulas
      (PartialOdometerHalfTurn h') u a b).2.1 x).mpr
    apply (PartialOdometerHalfTurnFormulas h').1 (x - u) |>.mpr
    exact hy'
  · intro x hx
    have hx' := ((PartialOdometerAffineTranslateFormulas
      (PartialOdometerHalfTurn h) u a b).2.1 x).mp hx
    have hy : - (x - u) ∈ h.domain :=
      (PartialOdometerHalfTurnFormulas h).1 (x - u) |>.mp hx'
    have hy' := hval (-(x - u)) hy
    rw [(PartialOdometerAffineTranslateFormulas
      (PartialOdometerHalfTurn h) u a b).2.2.1 x hx]
    rw [(PartialOdometerAffineTranslateFormulas
      (PartialOdometerHalfTurn h') u a b).2.2.1 x
      (((PartialOdometerAffineTranslateFormulas
        (PartialOdometerHalfTurn h') u a b).2.1 x).mpr
        ((PartialOdometerHalfTurnFormulas h').1 (x - u) |>.mpr
          (hsub hy)))]
    rw [(PartialOdometerHalfTurnFormulas h).2.1 (x - u) hx',
      (PartialOdometerHalfTurnFormulas h').2.1 (x - u)
        ((PartialOdometerHalfTurnFormulas h').1 (x - u) |>.mpr (hsub hy))]
    simpa using hy'

end ApollonianSuperharmonic

end
