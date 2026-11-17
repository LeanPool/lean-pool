/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileOdometerDomain
public import Mathlib.Init


/-!
# TileOdometerSlopeNonempty

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace TileOdometerSlopeNonempty

/-- A tile odometer with a defined slope has a nonempty tile. -/
theorem cells (c : CircleCoordinates) (T : ProtoTile)
    (h : PartialOdometer) (p : ℝ × ℝ) (hO : TileOdometer c T h)
    (hp : PartialOdometerSlope h = some p) : T.cells.Nonempty := by
  classical
  have hd := TileOdometerDomain c T h hO
  by_contra hn
  have hde : (h.domain : Set GaussianInt) = {T.anchor} := by
    rw [hd]
    simp [FootprintVertices, hn]
  have hs : (PartialOdometerSquares h).Nonempty := by
    by_contra hs
    simp [PartialOdometerSlope, hs] at hp
  rcases hs with ⟨x, hx⟩
  simp only [PartialOdometerSquares, Finset.mem_filter] at hx
  have hz : x + 1 = T.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hde]
    exact hx.2.1
  have hz0 : x = T.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hde]
    exact hx.1
  have hzbad : x + 1 = x := hz.trans hz0.symm
  have hzbad' := congrArg (fun z : GaussianInt => z.re) hzbad
  norm_num at hzbad'



end TileOdometerSlopeNonempty
end ApollonianSuperharmonic

end
