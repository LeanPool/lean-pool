/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ExactTileTiling
public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne

-- [TABLET NODE: PeriodicTileMultiplicityOne]

/-!
# PeriodicTileMultiplicityOne

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PeriodicTileMultiplicityOne {ι : Type} (P : PeriodicTileComplex ι) :
    ExactTileTiling (Set.range P.tile) := by
-- BODY
  unfold ExactTileTiling
  constructor
  · intro T hT
    obtain ⟨a, rfl⟩ := hT
    exact P.tiles_are_disks a
  · intro x
    obtain ⟨a, ha, hunique⟩ := PeriodicTileIndexedMultiplicityOne P x
    refine ⟨P.tile a, ⟨a, rfl⟩, ha, ?_⟩
    intro U hU hu
    obtain ⟨b, rfl⟩ := hU
    exact congrArg P.tile (hunique b hu)

end ApollonianSuperharmonic

end
