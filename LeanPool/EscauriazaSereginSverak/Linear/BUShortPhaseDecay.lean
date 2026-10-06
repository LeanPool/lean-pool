/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEarlyErrorLimit

/-!
# Phase-shifted half-space weight

Factoring out the fixed normal phase leaves a tangential Gaussian and
an exponential that decays on the cutoff transition region.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The half-space Carleman density with the fixed normal phase removed. -/
@[expose] def buShortShiftedWeight (scale a : ℝ) (z : ParabolicPoint) : ℝ :=
  Real.exp (-(2 * a * buShortB scale)) * buShortCarlemanWeight a z

/-- The phase-shifted weight separates into time, tangential Gaussian,
and normal phase factors. -/
theorem buShortShiftedWeight_eq
    (scale a : ℝ) (z : ParabolicPoint) (htime : 0 < z.2) :
    buShortShiftedWeight scale a z =
      z.2 ^ 2 *
        Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
        Real.exp (2 * a *
          (buShortF (z.1 2) z.2 - buShortB scale)) := by
  rw [buShortShiftedWeight, buShortCarlemanWeight,
    bu_halfSpaceWeight_split a scale z htime]
  have hcancel : Real.exp (-(2 * a * buShortB scale)) *
      Real.exp (2 * a * buShortB scale) = 1 := by
    rw [← Real.exp_add]
    have harg : -(2 * a * buShortB scale) + 2 * a * buShortB scale = 0 := by
      ring
    rw [harg, Real.exp_zero]
  calc
    _ = (Real.exp (-(2 * a * buShortB scale)) *
          Real.exp (2 * a * buShortB scale)) *
          (z.2 ^ 2 *
            Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
            Real.exp (2 * a *
              (buShortF (z.1 2) z.2 - buShortB scale))) := by ring
    _ = _ := by rw [hcancel]; ring

/-- Above the initial time and below time one, the shifted weight has
the exponential phase gap bound. -/
theorem buShortShiftedWeight_le_gap
    (scale a : ℝ) (ha : 0 ≤ a)
    (z : ParabolicPoint) (htime : 0 < z.2) (htime1 : z.2 ≤ 1)
    (hgap : buShortF (z.1 2) z.2 - buShortB scale ≤
      -buShortD scale / 2) :
    buShortShiftedWeight scale a z ≤
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
        Real.exp (-(a * buShortD scale)) := by
  rw [buShortShiftedWeight_eq scale a z htime]
  have ht2 : z.2 ^ 2 ≤ 1 := by nlinarith only [htime.le, htime1]
  have hgapArg :
      2 * a * (buShortF (z.1 2) z.2 - buShortB scale) ≤
        -(a * buShortD scale) := by
    have h := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * a by positivity)
    nlinarith only [h]
  have hexp := Real.exp_le_exp.mpr hgapArg
  have hgauss : 0 ≤ Real.exp
      (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) :=
    (Real.exp_pos _).le
  let G := Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2))
  let P := Real.exp (2 * a * (buShortF (z.1 2) z.2 - buShortB scale))
  let Q := Real.exp (-(a * buShortD scale))
  have hGP : 0 ≤ G * P := mul_nonneg hgauss (Real.exp_pos _).le
  calc
    z.2 ^ 2 * G * P = z.2 ^ 2 * (G * P) := by ring
    _ ≤ 1 * (G * P) := mul_le_mul_of_nonneg_right ht2 hGP
    _ = G * P := by ring
    _ ≤ G * Q := mul_le_mul_of_nonneg_left hexp hgauss

end ESS
