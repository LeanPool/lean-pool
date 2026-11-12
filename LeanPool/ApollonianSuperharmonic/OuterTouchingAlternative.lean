/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileArea
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: OuterTouchingAlternative]

/-!
# OuterTouchingAlternative

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
Three prototiles satisfy the *outer-touching alternative* if they form
a touching triple, or if all three have area one and every pair of their
footprints intersects.  The second possibility is the exceptional
three-unit-square conclusion in Claim `c.outtouch` of the paper; it
does not assert that the three squares have disjoint interiors.
-/
def OuterTouchingAlternative (T U V : ProtoTile) : Prop :=
-- BODY
  TouchingTriple T U V ∨
    (TileArea T = 1 ∧ TileArea U = 1 ∧ TileArea V = 1 ∧
      (FootprintVertices T ∩ FootprintVertices U).Nonempty ∧
      (FootprintVertices U ∩ FootprintVertices V).Nonempty ∧
      (FootprintVertices V ∩ FootprintVertices T).Nonempty)

end ApollonianSuperharmonic

end
