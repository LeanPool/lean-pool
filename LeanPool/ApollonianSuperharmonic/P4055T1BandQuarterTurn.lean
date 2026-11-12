/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization

-- [TABLET NODE: P4055T1BandQuarterTurn]

/-!
# P4055T1BandQuarterTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4055T1BandQuarterTurn (D : CircleCoordinates) (V : ProtoTile)
    (hV : BandPrototile D V) : QuarterTurnSymmetric V := by
-- BODY
  cases hV with
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
  | @decompose q hq S V hS hcells hfoot hcent =>
      exact (BandTileSimultaneousInduction q hq V
        (.decompose hq hS hcells hfoot hcent)).2.2.2.1

end ApollonianSuperharmonic

end
