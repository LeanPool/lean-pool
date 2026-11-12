/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry

-- [TABLET NODE: BandPackingSymmetryReversesOrientation]

/-!
# BandPackingSymmetryReversesOrientation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The orientation parity of a band-packing symmetry word is false for the
identity, coordinate negation, and shifts, true for conjugation, and is
added modulo two under composition.  It records whether the cyclic order
of the three parents of an oriented Descartes quadruple must be reversed.
-/
def BandPackingSymmetryReversesOrientation : BandPackingSymmetry → Bool :=
-- BODY
  fun g => match g with
    | .identity => false
    | .negate => false
    | .conjugate => true
    | .shift _ => false
    | .comp g h =>
        xor (BandPackingSymmetryReversesOrientation g)
          (BandPackingSymmetryReversesOrientation h)

end ApollonianSuperharmonic

end
