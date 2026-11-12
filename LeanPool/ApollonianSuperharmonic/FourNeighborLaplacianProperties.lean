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

/-- Affine perturbations and translation preserve the four-neighbor Laplacian. -/
theorem affineTranslate :
    ∀ (f : GaussianInt → ℤ), ∀ (f' : GaussianInt → ℤ), ∀ (x : GaussianInt), ∀ (t : GaussianInt),
        ∀ (A : ℤ), ∀ (B : ℤ), ∀ (C : ℤ), f x = f' (x - t) + A * x.re + B * x.im + C → f (x - (1 :
        GaussianInt)) = f' (x - t - (1 : GaussianInt)) + A * (x - (1 : GaussianInt)).re + B * (x
        - (1 : GaussianInt)).im + C → f (x + (1 : GaussianInt)) = f' (x - t + (1 : GaussianInt))
        + A * (x + (1 : GaussianInt)).re + B * (x + (1 : GaussianInt)).im + C → f (x - ⟨(0 : ℤ),
        (1 : ℤ)⟩) = f' (x - t - ⟨(0 : ℤ), (1 : ℤ)⟩) + A * (x - ⟨(0 : ℤ), (1 : ℤ)⟩).re + B * (x -
        ⟨(0 : ℤ), (1 : ℤ)⟩).im + C → f (x + ⟨(0 : ℤ), (1 : ℤ)⟩) = f' (x - t + ⟨(0 : ℤ), (1 : ℤ)⟩)
        + A * (x + ⟨(0 : ℤ), (1 : ℤ)⟩).re + B * (x + ⟨(0 : ℤ), (1 : ℤ)⟩).im + C →
        FourNeighborLaplacian f x = FourNeighborLaplacian f' (x - t) := by
  classical
  intro f f' x t A B C h0 hm hp hmi hpi
  rw [FourNeighborLaplacian, hm, hp, hmi, hpi, h0,
    FourNeighborLaplacian]
  rw [show x - t - 1 = (x - t) - 1 by abel,
    show x - t + 1 = (x - t) + 1 by abel,
    show x - t - ⟨0, 1⟩ = (x - t) - ⟨0, 1⟩ by rfl,
    show x - t + ⟨0, 1⟩ = (x - t) + ⟨0, 1⟩ by rfl]
  simp
  ring

end FourNeighborLaplacianProperties
end ApollonianSuperharmonic

end
