/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore

-- [TABLET NODE: P3776T1OpenStar]

/-!
# P3776T1OpenStar

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an area-free periodic core $P$ and an index $a$, let $U_a$ consist of
the position of $a$, the interiors (with both endpoints removed) of all
fixed arcs incident to $a$, and the open regions of all faces incident to
$a$. These are subsets of the actual fixed plane drawing, not of a new
polygonal drawing.
-/
def P3776T1OpenStar {ι : Type} (P : PeriodicTileCore ι) (a : ι) :
    Set (Real × Real) :=
-- BODY
  {x | x = P.plane.position a ∨
    (∃ b, P.plane.adjacent a b ∧ x ∈ P.plane.edgeArc a b ∧
      x ≠ P.plane.position a ∧ x ≠ P.plane.position b) ∨
    ∃ f, (∃ i, P.plane.faceVertex f i = a) ∧ x ∈ P.plane.faceRegion f}

end ApollonianSuperharmonic

end
