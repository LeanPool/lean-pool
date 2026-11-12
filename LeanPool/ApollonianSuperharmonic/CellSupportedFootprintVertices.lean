/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: CellSupportedFootprintVertices]

/-!
# CellSupportedFootprintVertices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The cell-supported footprint vertices of a prototile $T$ are the lattice
vertices that occur as one of the four corners of an actual constituent
cell of $T$.  Thus this set agrees with the usual footprint vertex set when
$T$ has a cell, but it is empty when $T$ has no cells; in particular it does
not include the stored anchor of an empty prototile.
-/
def CellSupportedFootprintVertices (T : ProtoTile) : Set GaussianInt :=
-- BODY
  {v | ∃ x ∈ T.cells,
    v = x ∨ v = x + 1 ∨ v = x + ⟨0, 1⟩ ∨
      v = x + 1 + ⟨0, 1⟩}

end ApollonianSuperharmonic

end
