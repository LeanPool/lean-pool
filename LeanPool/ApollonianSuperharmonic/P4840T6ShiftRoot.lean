/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction
public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple

-- [TABLET NODE: P4840T6ShiftRoot]

/-!
# P4840T6ShiftRoot

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4840T6ShiftRoot (z : GaussianInt) :
    BandPackingSymmetryQuadrupleAction (.shift (-z))
      ![(4, 1 + 8 * z + 4 * ⟨0, 1⟩),
        (1, 1 + 2 * z + 2 * ⟨0, 1⟩), (1, 1 + 2 * z), (0, -1)] =
      DiamondRecursiveQuadruple ⟨1, by norm_num⟩ := by
  funext j
  fin_cases j <;> apply Prod.ext
  all_goals try apply Zsqrtd.ext
  all_goals norm_num [BandPackingSymmetryQuadrupleAction, BandPackingSymmetryCircleAction,
    BandPackingSymmetryReversesOrientation, DiamondRecursiveQuadruple]

end ApollonianSuperharmonic

end
