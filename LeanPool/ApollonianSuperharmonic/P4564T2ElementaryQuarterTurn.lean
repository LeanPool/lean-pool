/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization

-- [TABLET NODE: P4564T2ElementaryQuarterTurn]

/-!
# P4564T2ElementaryQuarterTurn

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4564T2ElementaryQuarterTurn (x anchor : GaussianInt) :
    QuarterTurnSymmetric (⟨∅, anchor⟩ : ProtoTile) ∧
      QuarterTurnSymmetric (⟨{x}, anchor⟩ : ProtoTile) := by
-- BODY
  constructor
  · intro p
    simp [TileRealization]
  · intro p
    simp only [TileRealization, Finset.mem_singleton, Set.iUnion_iUnion_eq_left,
      TileCentroid, Finset.singleton_nonempty, ite_eq_left, Finset.sum_singleton,
      Finset.card_singleton, Nat.cast_one, div_one]
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    constructor <;> rintro ⟨⟨hx, hy⟩, hx', hy'⟩ <;>
      constructor <;> constructor <;> linarith

end ApollonianSuperharmonic

end
