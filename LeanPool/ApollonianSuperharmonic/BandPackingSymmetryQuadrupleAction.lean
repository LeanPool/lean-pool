/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCircleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryReversesOrientation

-- [TABLET NODE: BandPackingSymmetryQuadrupleAction]

/-!
# BandPackingSymmetryQuadrupleAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For an ordered quadruple $q=(C_0,C_1,C_2,C_3)$ and a packing symmetry
$g$, the transformed ordered quadruple has child $gC_0$.  If $g$ preserves
orientation its parents are $(gC_1,gC_2,gC_3)$; if $g$ reverses orientation
they are $(gC_1,gC_3,gC_2)$.  The reversal is part of the action because
proper quadruples remember the cyclic geometric order of their parents.
-/
def BandPackingSymmetryQuadrupleAction (g : BandPackingSymmetry)
    (q : Fin 4 → CircleCoordinates) : Fin 4 → CircleCoordinates :=
-- BODY
  let parentIndex : Fin 3 → Fin 3 := fun i =>
    if BandPackingSymmetryReversesOrientation g then -i else i
  ![BandPackingSymmetryCircleAction g (q 0),
    BandPackingSymmetryCircleAction g (q (parentIndex 0).succ),
    BandPackingSymmetryCircleAction g (q (parentIndex 1).succ),
    BandPackingSymmetryCircleAction g (q (parentIndex 2).succ)]

end ApollonianSuperharmonic

end
