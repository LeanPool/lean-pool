/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageNormalized
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.BallCover

/-!
# Geometry of the physical Gaussian cylinder

The affine image of a normalized averaging box is the physical
Gaussian averaging cylinder at half the elapsed time.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The physical Gaussian radius is the scaled normalized averaging
radius (`lem:bu-small-time`). -/
theorem bu_short_physical_average_radius
    (scale δ : ℝ) (hscale : 0 < scale) :
    let t := scale ^ 2 * δ / 2
    Real.sqrt (3 * t) = scale * Real.sqrt (3 * δ / 2) := by
  dsimp
  have harg : 3 * (scale ^ 2 * δ / 2) =
      scale ^ 2 * (3 * δ / 2) := by ring
  rw [harg, Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs,
    abs_of_pos hscale]

end ESS
