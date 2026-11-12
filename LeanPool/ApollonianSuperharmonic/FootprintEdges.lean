/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProtoTile

-- [TABLET NODE: FootprintEdges]

/-!
# FootprintEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The footprint edges of a prototile are the four unoriented lattice edges of
each constituent square, represented by their two-element endpoint sets.
Thus an edge belongs to the footprint only when it is contributed by a
constituent square; two footprint vertices do not by themselves create an
edge.
-/
def FootprintEdges (T : ProtoTile) : Set (Finset GaussianInt) :=
-- BODY
  {e | ∃ x ∈ T.cells,
    e = {x, x + 1} ∨ e = {x, x + ⟨0, 1⟩} ∨
      e = {x + 1, x + 1 + ⟨0, 1⟩} ∨
      e = {x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩}}

end ApollonianSuperharmonic

end
