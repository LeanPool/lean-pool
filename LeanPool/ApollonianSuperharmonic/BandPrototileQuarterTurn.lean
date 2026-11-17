/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction

/-!
# BandPrototileQuarterTurn

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandPrototileQuarterTurn

/-- Every band prototile is quarter-turn symmetric. -/
theorem symmetry (D : CircleCoordinates) (U : ProtoTile) (hU : BandPrototile D U) :
    QuarterTurnSymmetric U := by
  classical
  cases hU with
  | line w z hw =>
      intro p
      simp [TileRealization, TileCentroid]
  | unit z a anchor =>
      intro p
      have hc : TileCentroid (⟨{a}, anchor⟩ : ProtoTile) =
          (((a.re : Int) : Real) + (1 / 2 : Real),
            ((a.im : Int) : Real) + (1 / 2 : Real)) := by
        simp [TileCentroid]
      rw [hc]
      rcases p with ⟨px, py⟩
      simp only [TileRealization, Finset.mem_singleton, Set.mem_iUnion]
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
      constructor
      · rintro ⟨b, rfl, hlo, hhi⟩
        refine ⟨b, rfl, ?_, ?_⟩ <;> constructor <;>
          linarith [hlo.1, hlo.2, hhi.1, hhi.2]
      · rintro ⟨b, rfl, hlo, hhi⟩
        refine ⟨b, rfl, ?_, ?_⟩ <;> constructor <;>
          linarith [hlo.1, hlo.2, hhi.1, hhi.2]
  | @decompose q' hq' S' U' hS hcells hfoot hcent =>
      exact (BandTileSimultaneousInduction q' hq' U
        (.decompose hq' hS hcells hfoot hcent)).2.2.2.1

end BandPrototileQuarterTurn
end ApollonianSuperharmonic

end
