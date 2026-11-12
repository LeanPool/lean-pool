/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation

-- [TABLET NODE: P3767T1FixedTrace]

/-!
# P3767T1FixedTrace

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a plane triangulation $P$ in the sense of
`PlaneTriangulation`, its fixed trace is the subset of
$\mathbb R^2$ consisting of all stored vertex positions and all points
on stored arcs of adjacent pairs:
$$
 \mathcal T_P=\{P.\mathrm{position}(a):a\in\iota\}
 \cup\{x:\exists a,b,\ a\sim b\text{ and }x\in P.\mathrm{edgeArc}(a,b)\}.
$$
This is the trace of the given drawing, not of a newly constructed
tile-interior contact drawing.
-/
def P3767T1FixedTrace {ι : Type} (P : PlaneTriangulation ι) :
    Set (Real × Real) :=
-- BODY
  Set.range P.position ∪ {x | ∃ a b, P.adjacent a b ∧ x ∈ P.edgeArc a b}

end ApollonianSuperharmonic

end
