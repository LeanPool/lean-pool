/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandLatticeEquality
public import LeanPool.ApollonianSuperharmonic.LambdaTiling

-- [TABLET NODE: IntegralityTiling]

/-!
# IntegralityTiling

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem IntegralityTiling : ∀ C : BandCircle, ∃ T : ProtoTile,
    LatticeTile T ∧ QuarterTurnSymmetric T ∧
      ExactTileTiling (RegularTileFamily T (IntegralityLattice C)) ∧
      (C.1.1.1 ≠ 1 →
        Nat.card {U : ProtoTile //
          U ∈ RegularTileFamily T (IntegralityLattice C) ∧ U ≠ T ∧
            TileBordering T U} = 6) := by
-- BODY
  intro C
  obtain ⟨T, hT, hS, hE, hN⟩ := LambdaTiling C
  refine ⟨T, hT, hS, ?_, ?_⟩
  · simpa [BandLatticeEquality C] using hE
  · intro hC
    simpa [BandLatticeEquality C] using hN hC

end ApollonianSuperharmonic

end
