/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic

/-!
# Straight coordinates near a circle boundary

For the local surface charts needed by XII (3.1), page 245, subtract
the height of the right semicircle from the real coordinate. This is
a homeomorphism of the plane. Near the point one, it sends the outside
of the unit disc to the right half-plane and the circle to its boundary
line. Rotation supplies the same coordinates at every circle point.
-/

public section

namespace GraphMinor.GM12

/-- Subtract the right semicircle's real coordinate. Its inverse adds
that coordinate back, while leaving the imaginary coordinate unchanged. -/
@[expose] noncomputable def circleBoundaryShear : ℂ ≃ₜ ℂ where
  toFun z := z - (Real.sqrt (1 - z.im ^ 2) : ℂ)
  invFun w := w + (Real.sqrt (1 - w.im ^ 2) : ℂ)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Real coordinate in the circle boundary chart. -/
theorem circleBoundaryShear_re (z : ℂ) :
    (circleBoundaryShear z).re = z.re - Real.sqrt (1 - z.im ^ 2) := by rfl

/-- The imaginary coordinate is unchanged by the circle boundary chart. -/
theorem circleBoundaryShear_im (z : ℂ) : (circleBoundaryShear z).im = z.im := by
  change (z - (Real.sqrt (1 - z.im ^ 2) : ℂ)).im = z.im
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]

/-- On the right side of the plane, near the horizontal diameter,
the outside of the unit disc maps to the right half-plane. -/
theorem circleBoundaryShear_outside_iff {z : ℂ} (hzre : 0 < z.re) (hzim : |z.im| < 1) :
    1 ≤ ‖z‖ ↔ 0 ≤ (circleBoundaryShear z).re := by
  have himsq : z.im ^ 2 < 1 := by
    have h := abs_lt.mp hzim
    nlinarith [h.1, h.2]
  have hspos : 0 < Real.sqrt (1 - z.im ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr himsq)
  have hsq : Real.sqrt (1 - z.im ^ 2) ^ 2 = 1 - z.im ^ 2 := Real.sq_sqrt (by linarith)
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [circleBoundaryShear_re]
  constructor
  · intro h
    nlinarith [norm_nonneg z]
  · intro h
    nlinarith [norm_nonneg z]

/-- The unit circle maps to the boundary line of the right half-plane
in these local coordinates. -/
theorem circleBoundaryShear_circle_iff {z : ℂ} (hzre : 0 < z.re) (hzim : |z.im| < 1) :
    ‖z‖ = 1 ↔ (circleBoundaryShear z).re = 0 := by
  have himsq : z.im ^ 2 < 1 := by
    have h := abs_lt.mp hzim
    nlinarith [h.1, h.2]
  have hspos : 0 < Real.sqrt (1 - z.im ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr himsq)
  have hsq : Real.sqrt (1 - z.im ^ 2) ^ 2 = 1 - z.im ^ 2 := Real.sq_sqrt (by linarith)
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [circleBoundaryShear_re]
  constructor
  · intro h
    rw [h] at hnorm
    nlinarith
  · intro h
    nlinarith [norm_nonneg z]

end GraphMinor.GM12
