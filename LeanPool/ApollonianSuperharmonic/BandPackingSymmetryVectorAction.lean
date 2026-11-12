/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.GaussianReflection

-- [TABLET NODE: BandPackingSymmetryVectorAction]

/-!
# BandPackingSymmetryVectorAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The induced action of a band-packing symmetry word on a canonical Gaussian
lattice vector is defined as follows.  The identity fixes $v$, coordinate
negation acts by the quarter-turn $v\mapsto iv$, coordinate conjugation acts
by $v\mapsto-\overline v$, and every shift fixes $v$.  For
$\operatorname{comp}(g,h)$, first apply the action of $h$ and then the action
of $g$.  These choices use the canonical primitive orientation of the band
vectors; they do not attach data to a constructor history for a circle.
-/
def BandPackingSymmetryVectorAction :
    BandPackingSymmetry → GaussianInt → GaussianInt :=
-- BODY
  fun g v => match g with
    | .identity => v
    | .negate => GaussianQuarterTurn v
    | .conjugate => -GaussianReflection v
    | .shift _ => v
    | .comp g h =>
        BandPackingSymmetryVectorAction g
          (BandPackingSymmetryVectorAction h v)

end ApollonianSuperharmonic

end
