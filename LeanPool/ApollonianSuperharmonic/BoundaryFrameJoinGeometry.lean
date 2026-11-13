/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AncestorOdometerInnerSupportNormalization
public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import Mathlib.Init


/-!
# BoundaryFrameJoinGeometry

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BoundaryFrameJoinGeometry

/-- Shared parentPrototile identity for BoundaryFrameJoinGeometry. -/
theorem parentPrototile :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), (BandPrototile (F.q F.slot.succ) (D.tiles F.slot
            false)) → (BandPrototile C.1.1 (D.tiles F.slot false)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hUband
  rw [← F.parent]
  exact hUband

/-- Shared selectedCentroid identity for BoundaryFrameJoinGeometry. -/
theorem selectedCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = (if false = true then (1 :
            ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2
            : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) → (TileCentroid (D.tiles
            F.slot false) - TileCentroid F.tile = -(1 / 2 : ℝ) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r w hUcent
  simpa [r, w] using hUcent

/-- Shared minusCentroid identity for BoundaryFrameJoinGeometry. -/
theorem minusCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint
            (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r
  simpa [r] using F.minus_centroid

/-- Shared firstVectorSumReal identity for BoundaryFrameJoinGeometry. -/
theorem firstVectorSumReal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (w + x + y = 0) → (w.re + x.re + y.re = 0) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r w x y hvsum
  simpa only [Zsqrtd.re_add, Zsqrtd.re_zero] using
    congrArg (fun z : GaussianInt => z.re) hvsum

/-- Shared firstVectorSumImaginary identity for BoundaryFrameJoinGeometry. -/
theorem firstVectorSumImaginary :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let w : GaussianInt := BandVectors.1 (r 3) (r 2)
        let x : GaussianInt := BandVectors.1 (r 1) (r 3)
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (w + x + y = 0) → (w.im + x.im + y.im = 0) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r w x y hvsum
  simpa only [Zsqrtd.im_add, Zsqrtd.im_zero] using
    congrArg (fun z : GaussianInt => z.im) hvsum

/-- Shared joinFamily identity for BoundaryFrameJoinGeometry. -/
theorem joinFamily :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (y ∈ TilingLattice C) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        join ∈ RegularTileFamily base (TilingLattice C)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r y hyLattice u join
  refine ⟨(u : GaussianInt) + y, (TilingLattice C).add_mem u.property hyLattice, ?_⟩
  rfl

/-- Shared joinCentroid identity for BoundaryFrameJoinGeometry. -/
theorem joinCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (join = TileTranslation Rminus y) → (TileCentroid join = TileCentroid Rminus +
            GaussianRealPoint y) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r y u join hjoin_eq
  rw [hjoin_eq, (TileTranslationFormulas Rminus y).2.2.2.2.1]
  apply Prod.ext <;> simp [GaussianRealPoint]

/-- Shared joinCentroidEquality identity for BoundaryFrameJoinGeometry. -/
theorem joinCentroidEquality :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (TileCentroid (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y) → (∀ (u
            : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (TileCentroid join = TileCentroid Rminus + GaussianRealPoint y) → (TileCentroid (D.tiles
            F.slot false) = TileCentroid join)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r y hcenter u join hjoinCenter
  calc
    TileCentroid (D.tiles F.slot false) =
        (TileCentroid (D.tiles F.slot false) - TileCentroid Rminus) +
          TileCentroid Rminus := by ext <;> dsimp <;> ring
    _ = GaussianRealPoint y + TileCentroid Rminus := by rw [hcenter]
    _ = TileCentroid Rminus + GaussianRealPoint y := by ext <;> dsimp <;> ring
    _ = TileCentroid join := hjoinCenter.symm

/-- Shared joinAncestor identity for BoundaryFrameJoinGeometry. -/
theorem joinAncestor :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F), (0 < (F.q F.slot.succ).1) → (((F.q F.slot.succ).1 <
            (F.q 0).1) → ((AncestorOdometer (F.q F.slot.succ) F.outer.1.1 (D.tiles F.slot false)
                F.tile (D.functions F.slot false)
            F.odometer) → (
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        ∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (BandPrototile C.1.1 join) → (((D.tiles F.slot false).cells = join.cells ∧ ((D.tiles
            F.slot false).cells = ∅ → (D.tiles F.slot false).anchor = join.anchor)) →
            (AncestorOdometer C.1.1 F.outer.1.1 join F.tile (D.functions F.slot false)
            F.odometer))))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D hCpositive hstrict hselectedAnc r y u
      join hjoinBand hjoinCells
  have hstrictOuter : (F.q F.slot.succ).1 < F.outer.1.1.1 := by
    rw [← F.child]
    exact hstrict
  have hAnc := AncestorOdometerInnerSupportNormalization
    (F.q F.slot.succ) F.outer.1.1 (D.tiles F.slot false) join F.tile
    (D.functions F.slot false) F.odometer hCpositive hstrictOuter hselectedAnc
    (by simpa only [← F.parent] using hjoinBand) hjoinCells.1
  simpa only [← F.parent] using hAnc

/-- Shared joinFootprint identity for BoundaryFrameJoinGeometry. -/
theorem joinFootprint :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (FootprintVertices (D.tiles F.slot false) ⊆ FootprintVertices F.tile) → (∀ (u :
            ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (FootprintVertices join = FootprintVertices (D.tiles F.slot false)) → (FootprintVertices
            join ⊆ FootprintVertices F.tile)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r y hUfoot u join hjoinFootEq
  rw [hjoinFootEq]
  exact hUfoot

/-- Shared joinOccurrence identity for BoundaryFrameJoinGeometry. -/
theorem joinOccurrence :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
            P4458T1RestrictionFamily F),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let y : GaussianInt := BandVectors.1 (r 2) (r 1)
        (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = (if false = true then (1 :
            ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2
            : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 :
            ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (F.q (F.slot + (2 : Fin (3 :
            ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (u : ↥(TilingLattice C)),
        let join : ProtoTile := TileTranslation base (u + y)
        (BandPrototile C.1.1 join) → ((TileCentroid (D.tiles F.slot false) = TileCentroid join) →
            ((FootprintVertices join ⊆ FootprintVertices F.tile) → (BandSubtileOccurrence F.q
            F.tile F.slot false join)))) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D r y hUcent u join hjoinBand
      hjoinCenterEq hjoinFoot
  refine ⟨by simpa only [← F.parent] using hjoinBand, hjoinFoot, ?_⟩
  rw [← hjoinCenterEq]
  exact hUcent

/-- Shared plusCentroid identity for BoundaryFrameJoinGeometry. -/
theorem plusCentroid :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        TileCentroid Rplus - TileCentroid F.tile = (1 / 2 : ℝ) • GaussianRealPoint (BandVectors.1
            (r 1) (r 0) + BandVectors.1 (r 0) (r 1)) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r
  simpa [r] using F.plus_centroid

/-- Shared secondVectorSumReal identity for BoundaryFrameJoinGeometry. -/
theorem secondVectorSumReal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa + xa + ya = 0) → (wa.re + xa.re + ya.re = 0) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa ya hasum
  simpa only [Zsqrtd.re_add, Zsqrtd.re_zero] using
    congrArg (fun z : GaussianInt => z.re) hasum

/-- Shared secondVectorSumImaginary identity for BoundaryFrameJoinGeometry. -/
theorem secondVectorSumImaginary :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀
            (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus),
        let r : Fin 4 → CircleCoordinates :=
          ![F.q 0, F.q F.slot.succ, F.q ((F.slot + 1).succ),
            F.q ((F.slot + 2).succ)]
        let wa : GaussianInt := BandVectors.2 (r 3) (r 2)
        let xa : GaussianInt := BandVectors.2 (r 1) (r 3)
        let ya : GaussianInt := BandVectors.2 (r 2) (r 1)
        (wa + xa + ya = 0) → (wa.im + xa.im + ya.im = 0) ) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F r wa xa ya hasum
  simpa only [Zsqrtd.im_add, Zsqrtd.im_zero] using
    congrArg (fun z : GaussianInt => z.im) hasum

end BoundaryFrameJoinGeometry
end ApollonianSuperharmonic

end
