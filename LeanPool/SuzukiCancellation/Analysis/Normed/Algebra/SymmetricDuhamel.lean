/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.ExponentialCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Two-sided variation of constants

For a differentiable curve in a Banach algebra, transport its symmetric residual
by the exponential on both sides. The fundamental theorem of calculus gives the
error relative to the exact exponential, for every real endpoint.

## Main results

* `symmetricResidual_integrable`: existence of the transported residual integral.
* `sub_eq_integral_symmetricResidual`: variation of constants with arbitrary initial value.
* `sub_exp_eq_integral_symmetricResidual`: the two-sided Duhamel identity.
-/

@[expose] public noncomputable section

open NormedSpace MeasureTheory
open scoped RealScalar

namespace TrotterError

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- Transporting a continuous residual on both sides gives an interval integrable curve. -/
theorem symmetricResidual_integrable (H : A) {S D : ℝ → A}
    (hS : Continuous S) (hD : Continuous D) (h : ℝ) :
    IntervalIntegrable (fun x ↦ exp ((h - x) • H) *
      (D x - (H * S x + S x * H)) * exp ((h - x) • H)) volume 0 h := by
  have he : Continuous (fun x : ℝ ↦ exp ((h - x) • H)) :=
    (contDiff_exp_smul_const H).continuous.comp (continuous_const.sub continuous_id)
  exact (he.mul (hD.sub ((continuous_const.mul hS).add
    (hS.mul continuous_const))) |>.mul he).intervalIntegrable 0 h

/-- The derivative of a curve transported by the same exponential on both sides. -/
theorem hasDerivAt_exp_mul_mul_exp (H : A) {S : ℝ → A} {D : A} {x : ℝ}
    (hS : HasDerivAt S D x) (h : ℝ) :
    HasDerivAt (fun y ↦ exp ((h - y) • H) * S y * exp ((h - y) • H))
      (exp ((h - x) • H) * (D - (H * S x + S x * H)) *
        exp ((h - x) • H)) x := by
  have he : HasDerivAt (fun y : ℝ ↦ exp ((h - y) • H))
      (-(H * exp ((h - x) • H))) x := by
    simpa only [Function.comp_def, sub_self, zero_sub, neg_one_smul] using
      (hasDerivAt_exp_smul_const' H (h - x)).scomp x
      ((hasDerivAt_const x h).sub (hasDerivAt_id x))
  convert (he.mul hS).mul he using 1
  dsimp only [Pi.mul_apply]
  have hc := ((Commute.refl H).smul_right (h - x)).exp_right.eq
  generalize exp ((h - x) • H) = E at *
  noncomm_ring [hc]

/-- **Two-sided variation of constants** for an arbitrary initial value and real endpoint. -/
theorem sub_eq_integral_symmetricResidual (H : A) {S D : ℝ → A}
    (hS : ∀ x, HasDerivAt S (D x) x) (hD : Continuous D) (h : ℝ) :
    S h - exp (h • H) * S 0 * exp (h • H) =
      ∫ x in 0..h, exp ((h - x) • H) *
        (D x - (H * S x + S x * H)) * exp ((h - x) • H) := by
  have hcont : Continuous S := continuous_iff_continuousAt.mpr fun x ↦
    (hS x).continuousAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hasDerivAt_exp_mul_mul_exp H (hS x) h)
    (symmetricResidual_integrable H hcont hD h)]
  simp only [sub_self, zero_smul, exp_zero, one_mul, mul_one, sub_zero]

/-- **Two-sided Duhamel identity.** A curve starting at the identity differs from
`exp (2hH)` by the integral of its symmetric residual. The interval integral is
oriented, so the statement includes negative and zero endpoints. -/
theorem sub_exp_eq_integral_symmetricResidual (H : A) {S D : ℝ → A}
    (hS : ∀ x, HasDerivAt S (D x) x) (hD : Continuous D) (h0 : S 0 = 1) (h : ℝ) :
    S h - exp ((2 * h) • H) =
      ∫ x in 0..h, exp ((h - x) • H) *
        (D x - (H * S x + S x * H)) * exp ((h - x) • H) := by
  rw [← sub_eq_integral_symmetricResidual H hS hD h, h0, mul_one]
  rw [← exp_add_of_commute (Commute.refl _), ← add_smul, ← two_mul]

end TrotterError
