/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The actual complex-plane Gaussian phase integral

This is a specialization of the pinned finite-dimensional real Gaussian
Fourier integral to the real Hilbert space underlying `ℂ`. Both the phase
integral and its actual integrability are obtained from that theorem.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

theorem real_inner_neg_I_mul (z w : ℂ) :
    inner ℝ (-Complex.I * z) w = (conj w * z).im := by
  rw [real_inner_eq_re_inner ℂ]
  rw [RCLike.inner_apply', RCLike.re_eq_complex_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

theorem integral_complex_gaussian_phase {a : ℝ} (ha : 0 < a) (t : ℝ) (z : ℂ) :
    (∫ w : ℂ, Complex.exp (((-a * ‖w‖ ^ 2 : ℝ) : ℂ) +
      2 * Complex.I * (t : ℂ) * ((conj w * z).im : ℂ))) =
        ((Real.pi / a : ℝ) : ℂ) *
          Complex.exp (((-t ^ 2 * ‖z‖ ^ 2 / a : ℝ) : ℂ)) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (b := (a : ℂ)) (show 0 < (a : ℂ).re from ha)
    (2 * Complex.I * (t : ℂ)) (-Complex.I * z)
  simp only [real_inner_neg_I_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.finrank_real_complex] at h
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_one] at h
  have he : (2 * Complex.I * (t : ℂ)) ^ 2 * (‖z‖ : ℂ) ^ 2 / (4 * (a : ℂ)) =
      ((-t ^ 2 * ‖z‖ ^ 2 / a : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [he] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow] using h

theorem integrable_complex_gaussian_phase {a : ℝ} (ha : 0 < a) (t : ℝ) (z : ℂ) :
    Integrable (fun w : ℂ => Complex.exp (((-a * ‖w‖ ^ 2 : ℝ) : ℂ) +
      2 * Complex.I * (t : ℂ) * ((conj w * z).im : ℂ))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (a : ℂ)) (show 0 < (a : ℂ).re from ha)
    (2 * Complex.I * (t : ℂ)) (-Complex.I * z)
  simpa only [real_inner_neg_I_mul, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow] using h

end VacuumBellSeparation.Gaussian
