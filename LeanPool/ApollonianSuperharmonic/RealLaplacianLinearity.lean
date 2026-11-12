/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.RealFourNeighborLaplacian

-- [TABLET NODE: RealLaplacianLinearity]

/-!
# RealLaplacianLinearity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem RealLaplacianLinearity (u v : GaussianInt -> Real) (a b : Real)
    (x : GaussianInt) :
    RealFourNeighborLaplacian (fun y => a * u y + b * v y) x =
      a * RealFourNeighborLaplacian u x +
        b * RealFourNeighborLaplacian v x := by
-- BODY
  simp [RealFourNeighborLaplacian]
  ring

end ApollonianSuperharmonic

end
