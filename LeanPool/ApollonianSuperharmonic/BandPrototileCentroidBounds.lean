/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import Mathlib.Init


/-!
# BandPrototileCentroidBounds

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandPrototileCentroidBounds

/-- Shared imaginaryCenter fact. -/
theorem imaginaryCenter :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let c := TileCentroid T
        let imCells : Finset Int := T.cells.image (fun x => x.im)
        ∀ (imNe : imCells.Nonempty), (∀ p ∈ TileRealization T, (2 * c.1 - p.1, 2 * c.2 - p.2) ∈
            TileRealization T) → ((∀ p ∈ TileRealization T, (imCells.min' imNe : Real) ≤ p.2 ∧
            p.2 ≤ (imCells.max' imNe : Real) + 1) → (
        let mIm := imCells.min' imNe
        let MIm := imCells.max' imNe
        (∃ x ∈ T.cells, x.im = mIm) → ((∃ x ∈ T.cells, x.im = MIm) → (2 * c.2 = (mIm : Real) +
            MIm + 1))))
    ) := by
  classical
  intro T c imCells imNe reflect_mem boundIm mIm MIm minImCell maxImCell
  rcases minImCell with ⟨xmin, hxmin, hxminim⟩
  rcases maxImCell with ⟨xmax, hmax, hmaxim⟩
  have pmin : ((xmin.re : Real), (mIm : Real)) ∈ TileRealization T := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨xmin, hxmin, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    exact ⟨⟨by simp, by simp [hxminim]⟩,
      ⟨by simp, by simp [hxminim]⟩⟩
  have pmax : ((xmax.re : Real), ((MIm : Real) + 1)) ∈ TileRealization T := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨xmax, hmax, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    exact ⟨⟨by simp, by simp [hmaxim]⟩,
      ⟨by simp, by simp [hmaxim]⟩⟩
  have bmin := boundIm _ (reflect_mem _ pmin)
  have bmax := boundIm _ (reflect_mem _ pmax)
  dsimp at bmin bmax
  norm_num at bmin bmax ⊢
  linarith


/-- Bounds for the real coordinate of every point in a finite tile realization. -/
theorem realBounds (T : ProtoTile)
    (reNe : (T.cells.image (fun x => x.re)).Nonempty) :
    ∀ p ∈ TileRealization T,
      (((T.cells.image (fun x => x.re)).min' reNe : ℤ) : ℝ) ≤ p.1 ∧
        p.1 ≤ (((T.cells.image (fun x => x.re)).max' reNe : ℤ) : ℝ) + 1 := by
  classical
  let reCells := T.cells.image (fun x => x.re)
  intro p hp
  simp only [TileRealization, Set.mem_iUnion] at hp
  rcases hp with ⟨x, hx, hpx⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpx
  constructor
  · have hm := Finset.min'_le (T.cells.image (fun x => x.re)) x.re
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    exact le_trans (by exact_mod_cast hm) hpx.1.1
  · have hh := Finset.le_max' (T.cells.image (fun x => x.re))
        (x.re) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hhreal : (x.re : Real) ≤
        (reCells.max' reNe : Real) := by
      exact_mod_cast hh
    linarith [hhreal, hpx.2.1]

/-- Bounds for the imaginary coordinate of every point in a finite tile realization. -/
theorem imaginaryBounds (T : ProtoTile)
    (imNe : (T.cells.image (fun x => x.im)).Nonempty) :
    ∀ p ∈ TileRealization T,
      (((T.cells.image (fun x => x.im)).min' imNe : ℤ) : ℝ) ≤ p.2 ∧
        p.2 ≤ (((T.cells.image (fun x => x.im)).max' imNe : ℤ) : ℝ) + 1 := by
  classical
  let imCells := T.cells.image (fun x => x.im)
  intro p hp
  simp only [TileRealization, Set.mem_iUnion] at hp
  rcases hp with ⟨x, hx, hpx⟩
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hpx
  constructor
  · exact le_trans (Int.cast_le.mpr (Finset.min'_le _ x.im
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩))) hpx.1.2
  · have hh := Finset.le_max' (T.cells.image (fun x => x.im))
        x.im (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hhreal : (x.im : Real) ≤
        ((imCells.max' imNe : Int) : Real) := by
      exact_mod_cast hh
    linarith [hpx.2.2]

/-- Reflection symmetry determines the real centroid from the extreme cell coordinates. -/
theorem realCoordinateCenter (T : ProtoTile)
    (reNe : (T.cells.image (fun x => x.re)).Nonempty)
    (reflect_mem : ∀ p ∈ TileRealization T,
      (2 * (TileCentroid T).1 - p.1, 2 * (TileCentroid T).2 - p.2) ∈ TileRealization T) :
    2 * (TileCentroid T).1 = (((T.cells.image (fun x => x.re)).min' reNe : ℤ) : ℝ) +
      ((T.cells.image (fun x => x.re)).max' reNe : ℤ) + 1 := by
  classical
  let c := TileCentroid T
  let reCells := T.cells.image (fun x => x.re)
  let mRe := reCells.min' reNe
  let MRe := reCells.max' reNe
  have hboundRe := realBounds T reNe
  have minReCell : ∃ x ∈ T.cells, x.re = mRe := by
    rcases Finset.mem_image.mp (Finset.min'_mem reCells reNe) with ⟨x, hx, he⟩
    exact ⟨x, hx, he⟩
  have maxReCell : ∃ x ∈ T.cells, x.re = MRe := by
    rcases Finset.mem_image.mp (Finset.max'_mem reCells reNe) with ⟨x, hx, he⟩
    exact ⟨x, hx, he⟩
  rcases minReCell with ⟨xmin, hxmin, hxminre⟩
  rcases maxReCell with ⟨xmax, hmax, hmaxre⟩
  have pmin : ((mRe : Real), (xmin.im : Real)) ∈ TileRealization T := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨xmin, hxmin, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    exact ⟨⟨by simp [hxminre], by simp []⟩,
      ⟨by simp [hxminre], by simp⟩⟩
  have pmax : (((MRe : Real) + 1), (xmax.im : Real)) ∈ TileRealization T := by
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨xmax, hmax, ?_⟩
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    exact ⟨⟨by simp [hmaxre], by simp⟩,
      ⟨by simp [hmaxre], by simp⟩⟩
  have qmin := reflect_mem _ pmin
  have qmax := reflect_mem _ pmax
  have bmin := hboundRe _ qmin
  have bmax := hboundRe _ qmax
  dsimp at bmin bmax
  norm_num at bmin bmax ⊢
  linarith [bmin.2, bmax.1]

/-- Reflection symmetry determines the imaginary centroid from extreme cell coordinates. -/
theorem imaginaryCoordinateCenter (T : ProtoTile)
    (imNe : (T.cells.image (fun x => x.im)).Nonempty)
    (reflect_mem : ∀ p ∈ TileRealization T,
      (2 * (TileCentroid T).1 - p.1, 2 * (TileCentroid T).2 - p.2) ∈ TileRealization T) :
    2 * (TileCentroid T).2 = (((T.cells.image (fun x => x.im)).min' imNe : ℤ) : ℝ) +
      ((T.cells.image (fun x => x.im)).max' imNe : ℤ) + 1 := by
  classical
  apply imaginaryCenter T imNe reflect_mem (imaginaryBounds T imNe)
  · rcases Finset.mem_image.mp (Finset.min'_mem _ imNe) with ⟨x, hx, he⟩
    exact ⟨x, hx, he⟩
  · rcases Finset.mem_image.mp (Finset.max'_mem _ imNe) with ⟨x, hx, he⟩
    exact ⟨x, hx, he⟩

/-- A nonempty centrally symmetric lattice tile has an integral doubled centroid. -/
theorem integralDoubleCenter (T : ProtoTile) (hne : T.cells.Nonempty)
    (hcentral : CentrallyReflectedAt (TileCentroid T) T T) :
    ∃ u : GaussianInt, (2 : ℝ) • TileCentroid T = GaussianRealPoint u := by
  classical
  have reflect_mem : ∀ p ∈ TileRealization T,
      (2 * (TileCentroid T).1 - p.1, 2 * (TileCentroid T).2 - p.2) ∈ TileRealization T := by
    intro p hp
    rw [hcentral]
    exact ⟨p, hp, rfl⟩
  have reNe : (T.cells.image (fun x => x.re)).Nonempty := Finset.image_nonempty.mpr hne
  have imNe : (T.cells.image (fun x => x.im)).Nonempty := Finset.image_nonempty.mpr hne
  have centerRe := realCoordinateCenter T reNe reflect_mem
  have centerIm := imaginaryCoordinateCenter T imNe reflect_mem
  refine ⟨⟨((T.cells.image (fun x => x.re)).min' reNe : ℤ) +
      ((T.cells.image (fun x => x.re)).max' reNe : ℤ) + 1,
    ((T.cells.image (fun x => x.im)).min' imNe : ℤ) +
      ((T.cells.image (fun x => x.im)).max' imNe : ℤ) + 1⟩, ?_⟩
  apply Prod.ext <;> simp [GaussianRealPoint] <;> linarith [centerRe, centerIm]

end BandPrototileCentroidBounds
end ApollonianSuperharmonic

end
