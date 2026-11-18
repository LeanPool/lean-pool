/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AngularMoments.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Angular Fourier moments on a full circle -/


@[expose] public section


open MeasureTheory Set
open scoped Interval Real

namespace GinibrePoincare

noncomputable section

/-- The angular Fourier mode used in complex Gaussian polar coordinates. -/
def angularMode (a b : ℕ) (θ : ℝ) : ℂ :=
  Complex.exp ((((a : ℤ) - (b : ℤ) : ℤ) : ℂ) * θ * Complex.I)

/-- Angular modes are continuous, hence integrable on the bounded polar
angle interval. -/
theorem intervalIntegrable_angularMode (a b : ℕ) :
    IntervalIntegrable (angularMode a b) volume (-Real.pi) Real.pi := by
  apply Continuous.intervalIntegrable
  unfold angularMode
  fun_prop

/-- The exact Fourier orthogonality integral on the polar angle interval. -/
theorem integral_angularMode_Ioc (a b : ℕ) :
    ∫ θ in Ioc (-Real.pi) Real.pi, angularMode a b θ =
      if a = b then (2 * Real.pi : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  by_cases hab : a = b
  · subst b
    simp [angularMode]
    ring
  · rw [ite_eq_right hab]
    let k : ℤ := (a : ℤ) - (b : ℤ)
    have hk : k ≠ 0 := by
      intro h
      apply hab
      exact_mod_cast sub_eq_zero.mp h
    let c : ℂ := (k : ℂ) * Complex.I
    have hc : c ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hk) Complex.I_ne_zero
    have hfun : angularMode a b = fun θ : ℝ ↦ Complex.exp (c * θ) := by
      funext θ
      simp only [angularMode, c, k]
      congr 1
      ring
    rw [hfun, integral_exp_mul_complex hc]
    have hplus : Complex.exp (c * Real.pi) = ((-1 : ℂ) ^ k) := by
      rw [show c * Real.pi = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) by
        simp only [c]
        ring]
      rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
    have hminus : Complex.exp (c * ((-Real.pi : ℝ) : ℂ)) =
        ((-1 : ℂ) ^ k) := by
      rw [show c * ((-Real.pi : ℝ) : ℂ) =
          (k : ℂ) * (-((Real.pi : ℂ) * Complex.I)) by
        simp only [c]
        push_cast
        ring]
      rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      simp
    rw [hplus, hminus, sub_self, zero_div]

end

end GinibrePoincare
