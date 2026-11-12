/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.CircleCoordinates
public import LeanPool.ApollonianSuperharmonic.GaussianReflection

-- [TABLET NODE: BandPackingSymmetryCircleAction]

/-!
# BandPackingSymmetryCircleAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The action of a band-packing symmetry word on curvature coordinates is
defined on generators by
$$
 C\mapsto C,\qquad (c,z)\mapsto(c,-z),\qquad
 (c,z)\mapsto(c,\overline z),\qquad
 (c,z)\mapsto(c,z+2cw),
$$
and composition acts by function composition, with the right-hand word
acting first.  In particular every symmetry preserves curvature.
-/
def BandPackingSymmetryCircleAction :
    BandPackingSymmetry → CircleCoordinates → CircleCoordinates :=
-- BODY
  fun g C => match g with
    | .identity => C
    | .negate => (C.1, -C.2)
    | .conjugate => (C.1, GaussianReflection C.2)
    | .shift w => (C.1, C.2 + 2 * (C.1 : GaussianInt) * w)
    | .comp g h =>
        BandPackingSymmetryCircleAction g
          (BandPackingSymmetryCircleAction h C)

end ApollonianSuperharmonic

end
