/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WithinIntegralDerivative
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Uniform positive-energy phase bounds on the closed upper half-plane

These bounds use the sign of the real exponential and hold up to the
boundary. In particular the dominating slope has only one power of the
energy; it does not require an unjustified exponential moment.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem norm_exp_sub_one_le_two_norm_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) :
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  by_cases hsmall : ‖z‖ ≤ 1
  · exact Complex.norm_exp_sub_one_le hsmall
  · have he : ‖Complex.exp z‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hz
    have htri := norm_sub_le (Complex.exp z) (1 : ℂ)
    norm_num only [norm_one] at htri
    linarith

theorem norm_exp_sub_exp_le_two_norm_of_re_nonpos {z w : ℂ}
    (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp z - Complex.exp w‖ ≤ 2 * ‖z - w‖ := by
  have hone {a b : ℂ} (hab : a.re ≤ b.re) (hb : b.re ≤ 0) :
      ‖Complex.exp a - Complex.exp b‖ ≤ 2 * ‖a - b‖ := by
    have heq : Complex.exp a - Complex.exp b =
        Complex.exp b * (Complex.exp (a - b) - 1) := by
      rw [mul_sub, ← Complex.exp_add, mul_one]
      congr 2
      ring
    have hbexp : ‖Complex.exp b‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hb
    have hd := norm_exp_sub_one_le_two_norm_of_re_nonpos
      (z := a - b) (by simpa only [Complex.sub_re] using sub_nonpos.mpr hab)
    rw [heq, norm_mul]
    calc
      _ ≤ 1 * (2 * ‖a - b‖) :=
        mul_le_mul hbexp hd (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  rcases le_total z.re w.re with h | h
  · exact hone h hw
  · simpa only [norm_sub_rev] using hone h hz

/-- Positive energy phase given by `Complex.exp (z * (Complex.I * (ω : ℂ)))`. -/
noncomputable def positiveEnergyPhase (ω : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * (Complex.I * (ω : ℂ)))

theorem positiveEnergyExponent_re (ω : ℝ) (z : ℂ) :
    (z * (Complex.I * (ω : ℂ))).re = -z.im * ω := by
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_positiveEnergyPhase_le_one {ω : ℝ} (hω : 0 ≤ ω)
    {z : ℂ} (hz : 0 ≤ z.im) : ‖positiveEnergyPhase ω z‖ ≤ 1 := by
  rw [positiveEnergyPhase, Complex.norm_exp, positiveEnergyExponent_re]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hω)

theorem norm_positiveEnergyPhase_sub_le {ω : ℝ} (hω : 0 ≤ ω)
    {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    ‖positiveEnergyPhase ω z - positiveEnergyPhase ω w‖ ≤ 2 * ω * ‖z - w‖ := by
  have h := norm_exp_sub_exp_le_two_norm_of_re_nonpos
    (z := z * (Complex.I * (ω : ℂ))) (w := w * (Complex.I * (ω : ℂ)))
    (by
      rw [positiveEnergyExponent_re]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hω)
    (by
      rw [positiveEnergyExponent_re]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hw) hω)
  rw [← sub_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω] at h
  simpa only [positiveEnergyPhase, mul_comm, mul_left_comm, mul_assoc] using h

theorem hasDerivAt_positiveEnergyPhase (ω : ℝ) (z : ℂ) :
    HasDerivAt (positiveEnergyPhase ω)
      (positiveEnergyPhase ω z * (Complex.I * (ω : ℂ))) z := by
  simpa only [positiveEnergyPhase, id_eq, one_mul] using!
    ((hasDerivAt_id z).mul_const (Complex.I * (ω : ℂ))).cexp

end VacuumBellSeparation
