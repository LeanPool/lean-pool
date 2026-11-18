/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple

-- [TABLET NODE: ExactTileInterfaceTripleSwapLast]

/-!
# ExactTileInterfaceTripleSwapLast

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ExactTileInterfaceTripleSwapLast (A B C : ProtoTile)
    (E : ExactTileInterfaceTriple A B C) :
    ∃ E' : ExactTileInterfaceTriple A C B,
      E'.point = E.point ∧ E'.otherAB = E.otherCA ∧
      E'.otherBC = E.otherBC ∧ E'.otherCA = E.otherAB := by
-- BODY
  let E' : ExactTileInterfaceTriple A C B :=
    { point := E.point
      otherAB := E.otherCA
      otherBC := E.otherBC
      otherCA := E.otherAB
      pathAB := by simpa [Set.inter_comm] using E.pathCA
      pathBC := by simpa [Set.inter_comm] using E.pathBC
      pathCA := by simpa [Set.inter_comm] using E.pathAB
      unique_common := by
        intro y
        simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
          E.unique_common y }
  exact ⟨E', rfl, rfl, rfl, rfl⟩

end ApollonianSuperharmonic

end
