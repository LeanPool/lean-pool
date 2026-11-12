/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSquares

-- [TABLET NODE: P2999T1CompleteSquareTransport]

/-!
# P2999T1CompleteSquareTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P2999T1CompleteSquareTransport (g : BandPackingSymmetry) (h : PartialOdometer) (T :
    ProtoTile)
    (hT : PartialOdometerSquares h = T.cells) :
    PartialOdometerSquares (BandPackingSymmetryPartialOdometerAction g h) =
      (BandPackingSymmetryTileAction g T).cells := by
-- BODY
  classical
  have invN (x : GaussianInt) : -GaussianQuarterTurn (GaussianQuarterTurn x) = x := by
    ext <;> simp [GaussianQuarterTurn]
  have invK (x : GaussianInt) : -GaussianReflection (-GaussianReflection x) = x := by
    ext <;> simp [GaussianReflection]
  have memN (h : PartialOdometer) (x : GaussianInt) :
      x ∈ (BandPackingSymmetryPartialOdometerAction .negate h).domain ↔
        -GaussianQuarterTurn x ∈ h.domain := by
    change x ∈ h.domain.image GaussianQuarterTurn ↔ _
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa [invN] using hy
    · intro hx
      refine Finset.mem_image.mpr ⟨-GaussianQuarterTurn x, hx, ?_⟩
      ext <;> simp [GaussianQuarterTurn]
  have memK (h : PartialOdometer) (x : GaussianInt) :
      x ∈ (BandPackingSymmetryPartialOdometerAction .conjugate h).domain ↔
        -GaussianReflection x ∈ h.domain := by
    change x ∈ h.domain.image (fun y => -GaussianReflection y) ↔ _
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa [invK] using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨-GaussianReflection x, hx, invK x⟩
  have sqN (h : PartialOdometer) :
      PartialOdometerSquares (BandPackingSymmetryPartialOdometerAction .negate h) =
        (PartialOdometerSquares h).image (fun x => GaussianQuarterTurn x - 1) := by
    have corner (x : GaussianInt) :
        -GaussianQuarterTurn (GaussianQuarterTurn x - 1) = x + ⟨0, 1⟩ ∧
        -GaussianQuarterTurn (GaussianQuarterTurn x - 1 + 1) = x ∧
        -GaussianQuarterTurn (GaussianQuarterTurn x - 1 + ⟨0, 1⟩) = x + 1 + ⟨0, 1⟩ ∧
        -GaussianQuarterTurn (GaussianQuarterTurn x - 1 + 1 + ⟨0, 1⟩) = x + 1 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp [GaussianQuarterTurn, add_comm]
    have sm (x : GaussianInt) :
        GaussianQuarterTurn x - 1 ∈
          PartialOdometerSquares (BandPackingSymmetryPartialOdometerAction .negate h) ↔
          x ∈ PartialOdometerSquares h := by
      simp only [PartialOdometerSquares, Finset.mem_filter, memN,
        (corner x).1, (corner x).2.1, (corner x).2.2.1, (corner x).2.2.2]
      tauto
    ext y
    constructor
    · intro hy
      have eq : GaussianQuarterTurn (-GaussianQuarterTurn (y + 1)) - 1 = y := by
        ext <;> simp [GaussianQuarterTurn]
      exact Finset.mem_image.mpr ⟨-GaussianQuarterTurn (y + 1),
        (sm _).mp (by simpa only [eq] using hy), eq⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (sm x).mpr hx
  have sqK (h : PartialOdometer) :
      PartialOdometerSquares (BandPackingSymmetryPartialOdometerAction .conjugate h) =
        (PartialOdometerSquares h).image (fun x => -GaussianReflection x - 1) := by
    have corner (x : GaussianInt) :
        -GaussianReflection (-GaussianReflection x - 1) = x + 1 ∧
        -GaussianReflection (-GaussianReflection x - 1 + 1) = x ∧
        -GaussianReflection (-GaussianReflection x - 1 + ⟨0, 1⟩) = x + 1 + ⟨0, 1⟩ ∧
        -GaussianReflection (-GaussianReflection x - 1 + 1 + ⟨0, 1⟩) = x + ⟨0, 1⟩ := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp [GaussianReflection, add_comm]
    have sm (x : GaussianInt) :
        -GaussianReflection x - 1 ∈
          PartialOdometerSquares (BandPackingSymmetryPartialOdometerAction .conjugate h) ↔
          x ∈ PartialOdometerSquares h := by
      simp only [PartialOdometerSquares, Finset.mem_filter, memK,
        (corner x).1, (corner x).2.1, (corner x).2.2.1, (corner x).2.2.2]
      tauto
    ext y
    constructor
    · intro hy
      have eq : -GaussianReflection (-GaussianReflection y - 1) - 1 = y := by
        ext <;> simp [GaussianReflection]
      exact Finset.mem_image.mpr ⟨-GaussianReflection y - 1,
        (sm _).mp (by simpa only [eq] using hy), eq⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (sm x).mpr hx
  induction g generalizing h T with
  | identity => exact hT
  | shift w => exact hT
  | negate => simpa only [hT, BandPackingSymmetryTileAction, TileQuarterTurn] using sqN h
  | conjugate =>
    rw [sqK, hT]
    simp only [BandPackingSymmetryTileAction, TileQuarterTurn, TileReflection,
      Finset.image_image]
    congr 1
    funext x
    ext <;> simp [GaussianQuarterTurn, GaussianReflection]
  | comp a b ia ib => exact ia _ _ (ib h T hT)

end ApollonianSuperharmonic

end
