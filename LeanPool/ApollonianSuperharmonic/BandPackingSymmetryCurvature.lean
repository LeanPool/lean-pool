/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCircleAction
public import Mathlib.Init


/-!
# BandPackingSymmetryCurvature

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandPackingSymmetryCurvature

/-- Shared preserved identity for BandPackingSymmetryCurvature. -/
theorem preserved :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (c : CircleCoordinates), (BandPackingSymmetryCircleAction
            g c).1 = c.1 ) := by
  classical
  intro g
  induction g with
  | identity => intro c; rfl
  | negate => intro c; rfl
  | conjugate => intro c; rfl
  | shift w => intro c; rfl
  | comp a b iha ihb => intro c; simp [BandPackingSymmetryCircleAction, iha, ihb]

end BandPackingSymmetryCurvature
end ApollonianSuperharmonic

end
