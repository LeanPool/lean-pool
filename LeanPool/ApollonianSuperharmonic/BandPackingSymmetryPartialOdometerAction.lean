/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingShiftPotential
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import LeanPool.ApollonianSuperharmonic.GaussianReflection
public import LeanPool.ApollonianSuperharmonic.PartialOdometer

-- [TABLET NODE: BandPackingSymmetryPartialOdometerAction]

/-!
# BandPackingSymmetryPartialOdometerAction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The partial-odometer action of a band-packing symmetry is defined
generator by generator.  The identity fixes the function.  A packing
shift $T_w$ keeps the literal finite domain and adds
$\operatorname{BandPackingShiftPotential}(w,\cdot)$ on that domain.  Coordinate
negation sends a domain point $x$ to $ix$ and transports the value by the
inverse map $y\mapsto-iy$.  Coordinate conjugation sends $x$ to
$-\bar x$ and transports the value by this involution.  In every case the
stored total-function representative is zero off the transported finite
domain.  A composite word acts by composition, with the right-hand word
acting first, in the same order as
`BandPackingSymmetryTileAction`.
-/
noncomputable def BandPackingSymmetryPartialOdometerAction :
    BandPackingSymmetry → PartialOdometer → PartialOdometer :=
-- BODY
  fun g h => match g with
    | .identity => h
    | .shift w =>
        { domain := h.domain
          value := fun x =>
            if x ∈ h.domain then h.value x + BandPackingShiftPotential w x else 0
          value_outside := by
            intro x hx
            simp [hx] }
    | .negate =>
        { domain := h.domain.image GaussianQuarterTurn
          value := fun x =>
            if x ∈ h.domain.image GaussianQuarterTurn then
              h.value (-GaussianQuarterTurn x)
            else 0
          value_outside := by
            intro x hx
            simp [hx] }
    | .conjugate =>
        { domain := h.domain.image (fun x => -GaussianReflection x)
          value := fun x =>
            if x ∈ h.domain.image (fun y => -GaussianReflection y) then
              h.value (-GaussianReflection x)
            else 0
          value_outside := by
            intro x hx
            simp [hx] }
    | .comp a b =>
        BandPackingSymmetryPartialOdometerAction a
          (BandPackingSymmetryPartialOdometerAction b h)

end ApollonianSuperharmonic

end
