/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeCell

-- [TABLET NODE: FourNeighborAdjacent]

/-!
# FourNeighborAdjacent

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Two lattice cells are *four-neighbor adjacent* when their lower-left
corners differ by one of $\pm1,\pm i$.  Equivalently, their closed unit
squares share a complete unit side.
-/
def FourNeighborAdjacent (x y : LatticeCell) : Prop :=
-- BODY
  y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩

end ApollonianSuperharmonic

end
