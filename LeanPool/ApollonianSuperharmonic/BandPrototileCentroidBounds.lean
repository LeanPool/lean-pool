/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileRealization
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


end BandPrototileCentroidBounds
end ApollonianSuperharmonic

end
