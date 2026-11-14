/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: FootprintVertices]

/-!
# FootprintVertices

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The footprint vertices of a nonempty prototile are exactly the four lattice
vertices of each of its constituent cells.  The footprint vertex set of an
empty prototile is the singleton containing its anchor.
-/
def FootprintVertices (T : ProtoTile) : Set GaussianInt :=
-- BODY
  if T.cells.Nonempty then
    {v | ∃ x ∈ T.cells,
      v = x ∨ v = x + 1 ∨ v = x + ⟨0, 1⟩ ∨
        v = x + 1 + ⟨0, 1⟩}
  else {T.anchor}

end ApollonianSuperharmonic

end
