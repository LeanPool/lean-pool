/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffs
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfWeightsDerivatives

/-!
# The shifted half-space weight

At exponent three quarters the half-space Carleman phase splits into a
tangential Gaussian and the normal phase used in `lem:bu-small-time`.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The half-space phase at exponent three quarters is a tangential
Gaussian plus `a` times the normal phase. -/
theorem bu_halfSpacePhase_eq
    (a : ℝ) (z : ParabolicPoint) (htime : 0 < z.2) :
    halfSpacePhase a (3 / 4 : ℝ) z =
      -(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
        a * buShortF (z.1 2) z.2 := by
  dsimp [halfSpacePhase, buShortF]
  rw [Real.rpow_neg htime.le]
  norm_num
  ring_nf

/-- Factoring out the fixed phase shift changes the exponential weight
only by a constant independent of space and time. -/
theorem bu_halfSpaceWeight_split
    (a scale : ℝ) (z : ParabolicPoint) (htime : 0 < z.2) :
    Real.exp (2 * halfSpacePhase a (3 / 4 : ℝ) z) =
      Real.exp (2 * a * buShortB scale) *
        (Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
          Real.exp (2 * a * (buShortF (z.1 2) z.2 - buShortB scale))) := by
  rw [bu_halfSpacePhase_eq a z htime]
  have harg :
      2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
        a * buShortF (z.1 2) z.2) =
      2 * a * buShortB scale +
        (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2) +
          2 * a * (buShortF (z.1 2) z.2 - buShortB scale)) := by ring
  rw [harg, Real.exp_add, Real.exp_add]

end ESS
