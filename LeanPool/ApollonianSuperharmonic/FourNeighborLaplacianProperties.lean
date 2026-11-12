/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import Mathlib.Init


/-!
# FourNeighborLaplacianProperties

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace FourNeighborLaplacianProperties

/-- Shared differences identity for FourNeighborLaplacianProperties. -/
theorem differences :
    (by
      classical
      exact
        ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt), FourNeighborLaplacian g x = g (x +
            (1 : GaussianInt)) - g x + (g (x - (1 : GaussianInt)) - g x) + (g (x + ⟨(0 : ℤ), (1 :
            ℤ)⟩) - g x) + (g (x - ⟨(0 : ℤ), (1 : ℤ)⟩) - g x) ) := by
  classical
  intro g x
  unfold FourNeighborLaplacian
  ring

end FourNeighborLaplacianProperties
end ApollonianSuperharmonic

end
