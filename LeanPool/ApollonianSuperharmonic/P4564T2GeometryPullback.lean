/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandParentRotationOccurrenceCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport

-- [TABLET NODE: P4564T2GeometryPullback]

/-!
# P4564T2GeometryPullback

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4564T2GeometryPullback (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (T : ProtoTile) (hT : BandPrototile (q 0) T)
    (a : Fin 3) (g : BandPackingSymmetry) :
    let qa : Fin 4 → CircleCoordinates :=
      ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
    let qg := BandPackingSymmetryQuadrupleAction g qa
    let Tg := BandPackingSymmetryTileAction g T
    (LatticeTile Tg ∧ TileArea Tg = Int.toNat (qg 0).1 ∧
    (∀ (S : Fin 3 → Bool → ProtoTile),
      (∀ i s, BandSubtileOccurrence qg Tg i s (S i s)) →
      (∀ x, x ∈ Tg.cells ↔ ∃ i s, x ∈ (S i s).cells) →
      ∀ i s, LatticeTile (TileCellComplement Tg (S i s)) ∧
        TileTouching (TileCellComplement Tg (S i s)) (S i s)) ∧
    QuarterTurnSymmetric Tg) →
    (LatticeTile T ∧ TileArea T = Int.toNat (q 0).1 ∧
    (∀ (S : Fin 3 → Bool → ProtoTile),
      (∀ i s, BandSubtileOccurrence q T i s (S i s)) →
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) →
      ∀ i s, LatticeTile (TileCellComplement T (S i s)) ∧
        TileTouching (TileCellComplement T (S i s)) (S i s)) ∧
    QuarterTurnSymmetric T) := by
-- BODY
  dsimp only
  rintro ⟨hdisk, harea, hcomplements, hquarter⟩
  obtain ⟨disk, area, complement, touching, quarter, _⟩ :=
    BandPackingSymmetryTilingTransport g
  refine ⟨(disk T).mpr hdisk, ?_, ?_, (quarter T).mpr hquarter⟩
  · have hcurv :
        (BandPackingSymmetryQuadrupleAction g
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] 0).1 =
          (q 0).1 := (BandPackingSymmetryCovariance g).1 (q 0)
    exact (area T).symm.trans (harea.trans (congrArg Int.toNat hcurv))
  · intro S hS hcover i s
    let qa : Fin 4 → CircleCoordinates :=
      ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
    obtain ⟨hqa, hSa, hcovera⟩ :=
      BandParentRotationOccurrenceCovariance q hq a T hT S hS hcover
    obtain ⟨d, e, S', hphase, he, hfamily, hS', hcover'⟩ :=
      (BandPackingSymmetryCovariance g).2.2 qa T
        (fun j t => S (a + j) t) hqa hT hSa hcovera
    have h := hcomplements S' hS' hcover' (e (i - a, s)).1 (e (i - a, s)).2
    have hmember : S' (e (i - a, s)).1 (e (i - a, s)).2 =
        BandPackingSymmetryTileAction g (S i s) := by
      have hi : a + (i - a) = i := by abel
      simpa only [hi] using hfamily (i - a) s
    rw [hmember] at h
    refine ⟨(disk _).mpr ?_, (touching _ _).mpr ?_⟩
    · rw [complement]
      exact h.1
    · rw [complement]
      exact h.2

end ApollonianSuperharmonic

end
