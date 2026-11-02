/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.DivisorSums.GreatestPrimeFactorCount

/-! # Quantitative logarithmic gain from saved prime factors

The error in a lower bound for the rough logarithmic mass must be smaller
than the saving from divisor hits. A merely qualitative `o(1)` relative
error does not supply the quantitative conclusion used in Theorem 2.
-/

@[expose] public section

namespace NairTenenbaum

open Real

/-- Convert logarithmic mass and a factor-count saving into an exponential
lower bound. `E` is the absolute error in the mass estimate. -/
theorem exp_gain_of_logMass_bounds {P y a H E M : ℝ} (hP : 1 ≤ P) (hy : 1 ≤ y)
    (ha : 0 < a) (hH : 0 ≤ H) (hHa : H ≤ a)
    (hlower : a * Real.log y - E ≤ M) (hupper : M ≤ (a - H) * Real.log P)
    (herror : E ≤ H * Real.log y / 2) :
    y * Real.exp (H * Real.log y / (2 * a)) ≤ P := by
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlog : Real.log y ≤ Real.log P := by
    by_contra! h
    have hmass : a * Real.log y - H * Real.log y / 2 ≤ (a - H) * Real.log P := by linarith
    by_cases hHa' : H = a
    · rw [hHa', sub_self, zero_mul] at hmass
      have hyzero : Real.log y = 0 := by nlinarith
      have HP := Real.log_nonneg hP
      linarith
    · have hgap : 0 < a - H := by rcases lt_or_eq_of_le hHa with h | h <;> [linarith; contradiction]
      have := mul_lt_mul_of_pos_left h hgap
      nlinarith
  have Hgain : H * Real.log y / 2 ≤ a * (Real.log P - Real.log y) := by
    have HH := mul_le_mul_of_nonneg_left hlog hH
    nlinarith
  have Hdiv : H * Real.log y / (2 * a) ≤ Real.log P - Real.log y := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).mpr
    nlinarith
  have HE := Real.exp_le_exp.mpr (show Real.log y + H * Real.log y / (2 * a) ≤ Real.log P by
    linarith)
  simpa only [Real.exp_add, Real.exp_log (by
    linarith : 0 < y), Real.exp_log (by linarith : 0 < P)] using HE

end NairTenenbaum
