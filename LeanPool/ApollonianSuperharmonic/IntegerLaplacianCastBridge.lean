/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.RealFourNeighborLaplacian

-- [TABLET NODE: IntegerLaplacianCastBridge]

/-!
# IntegerLaplacianCastBridge

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem IntegerLaplacianCastBridge (f : IntegerLatticeFunction)
    (x : GaussianInt) :
    RealFourNeighborLaplacian (fun y => (f y : Real)) x =
      (FourNeighborLaplacian f x : Real) := by
-- BODY
  simp [RealFourNeighborLaplacian, FourNeighborLaplacian]

end ApollonianSuperharmonic

end
